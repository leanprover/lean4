// Lean compiler output
// Module: Lean.Elab.Tactic.NormCast
// Imports: public import Lean.Meta.Tactic.NormCast public import Lean.Elab.Tactic.Conv.Simp
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
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_getLhs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_consumeMData(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_NormCast_normCastExt;
lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkDefaultMethods(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Meta_Simp_Methods_toMethodsRefImpl(lean_object*);
lean_object* lean_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Simp_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_bombEmoji;
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_findLocalDeclWithType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_rewrite_x3f(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_getCoeFnInfo_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNumeral(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_coerce_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_Simp_SimprocsArray_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Conv_applySimpResult(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_NormCast_pushCastExt;
lean_object* l_Lean_Meta_SimpExtension_getTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkConfigItemViews(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_elabConfig(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_applySimpResultToLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandLocation(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_NormCast_addElim(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_mkCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Lean_Elab_Term_tryPostpone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
lean_object* l_Lean_Elab_Term_withExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
lean_object* l_Lean_Elab_Tactic_simpLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Context_setFailIfUnchanged(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__0_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__0_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__0_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__1_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "norm_cast"};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__1_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__1_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__2_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__0_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 205, 46, 93, 234, 75, 44, 75)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__2_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__2_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__1_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(182, 61, 207, 202, 244, 209, 78, 162)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__2_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__2_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__3_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__3_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__3_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__4_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__3_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__4_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__4_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__5_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__5_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__5_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__6_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__4_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__5_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__6_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__6_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__7_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__7_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__7_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__8_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__6_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__7_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 59, 67, 7, 118, 215, 141, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__8_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__8_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__9_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__8_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__0_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(133, 58, 227, 168, 195, 28, 19, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__9_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__9_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__10_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "NormCast"};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__10_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__10_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__11_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__9_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__10_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(51, 162, 136, 242, 134, 53, 60, 80)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__11_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__11_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__12_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__11_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(158, 29, 89, 155, 218, 119, 156, 211)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__12_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__12_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__13_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__12_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__5_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(231, 52, 160, 104, 246, 223, 107, 175)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__13_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__13_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__14_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__13_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__7_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(169, 159, 129, 135, 134, 210, 201, 86)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__14_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__14_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__15_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__14_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__0_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(64, 30, 88, 140, 145, 32, 6, 44)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__15_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__15_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__16_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__15_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__10_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(10, 97, 33, 80, 97, 75, 242, 179)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__16_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__16_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__17_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__17_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__17_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__18_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__16_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__17_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(79, 58, 201, 12, 62, 234, 101, 99)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__18_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__18_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__19_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__19_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__19_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__20_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__18_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__19_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(186, 192, 123, 84, 21, 50, 71, 114)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__20_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__20_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__21_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__20_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__5_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(219, 236, 191, 158, 42, 245, 99, 165)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__21_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__21_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__22_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__21_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__7_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(237, 73, 185, 141, 55, 124, 148, 186)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__22_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__22_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__23_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__22_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__0_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(84, 165, 235, 100, 117, 192, 96, 155)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__23_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__23_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__24_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__23_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__10_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(174, 51, 15, 235, 171, 15, 129, 56)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__24_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__24_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__25_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__24_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1508164376) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(150, 32, 109, 233, 232, 18, 92, 214)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__25_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__25_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__26_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__26_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__26_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__27_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__25_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__26_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(49, 117, 38, 224, 16, 5, 105, 27)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__27_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__27_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__28_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__28_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__28_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__29_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__27_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__28_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(201, 43, 6, 161, 164, 217, 168, 53)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__29_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__29_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__30_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__29_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(180, 111, 22, 94, 70, 182, 158, 120)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__30_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__30_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2____boxed(lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__0;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 32, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 1, 1, 1, 0, 1),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 1, 1, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 1, 1, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__5;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__9;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__10;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__11;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "proving: "};
static const lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__6___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_NormCast_mkCoe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "failed"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_mkCoe___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_mkCoe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_mkCoe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(51, 81, 163, 94, 71, 156, 90, 186)}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__5_value;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__8;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " to "};
static const lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_NormCast_splittingProcedure___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "splitting "};
static const lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_splittingProcedure___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_splittingProcedure___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_prove_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "discharging: "};
static const lean_object* l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_NormCast_prove___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "squash"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_NormCast_numeralToCoe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cast"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_numeralToCoe___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_numeralToCoe___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_numeralToCoe___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_numeralToCoe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_numeralToCoe___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_NormCast_numeralToCoe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 237, 167, 212, 100, 179, 19, 112)}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_numeralToCoe___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_numeralToCoe___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_numeralToCoe(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_numeralToCoe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3__value;
static const lean_string_object l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Simp"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3__value;
static const lean_string_object l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "NormCastConfig"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3__value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__5_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3__value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__0_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3__value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__1_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(54, 38, 229, 237, 143, 62, 212, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3__value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__2_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3__value),LEAN_SCALAR_PTR_LITERAL(77, 116, 70, 245, 174, 212, 20, 27)}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_ = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__0_value;
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__1_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__2;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__14_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__15;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__16_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__19_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__0_value;
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__1_value;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__2;
static const lean_array_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__3 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Error evaluating configuration\n"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "\n\nException: "};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Configuration contains `sorry`"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__5;
static const lean_string_object l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "Error evaluating configuration: Environment does not yet contain type "};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__8;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__9;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 32, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 1, 0, 0, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 1, 1, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 1, 1, 1, 1, 1, 1, 1),LEAN_SCALAR_PTR_LITERAL(1, 1, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_derive___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_derive___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__1;
static const lean_string_object l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = " (after "};
static const lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__3;
static const lean_string_object l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__18(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__18___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__10(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__14___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__16(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__16___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__27(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_NormCast_derive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_NormCast_derive___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_NormCast_derive___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_derive___closed__0_value;
static const lean_closure_object l_Lean_Elab_Tactic_NormCast_derive___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_NormCast_derive___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_NormCast_derive___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_derive___closed__1_value;
static const lean_closure_object l_Lean_Elab_Tactic_NormCast_derive___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_NormCast_derive___lam__2___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_NormCast_derive___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_derive___closed__2_value;
static const lean_closure_object l_Lean_Elab_Tactic_NormCast_derive___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_NormCast_derive___lam__3___boxed, .m_arity = 10, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_NormCast_derive___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_derive___closed__3_value;
static const lean_closure_object l_Lean_Elab_Tactic_NormCast_derive___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_NormCast_derive___lam__6___boxed, .m_arity = 11, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Elab_Tactic_NormCast_derive___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_derive___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_NormCast_derive___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "pre-processing numerals"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_derive___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_derive___closed__5_value;
static const lean_array_object l_Lean_Elab_Tactic_NormCast_derive___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_derive___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_derive___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_NormCast_derive___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "moving upward, splitting and eliminating"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_derive___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_derive___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_NormCast_derive___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "reduceCtorEq"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_derive___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_derive___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_derive___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_NormCast_derive___closed__8_value),LEAN_SCALAR_PTR_LITERAL(241, 230, 128, 19, 70, 224, 61, 3)}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_derive___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_derive___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_NormCast_derive___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "squashing"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_derive___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_derive___closed__10_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mod_cast"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_NormCast_elabModCast___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "modCast"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabModCast___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__5_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabModCast___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 150, 13, 6, 253, 161, 172, 138)}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "elabModCast"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__5_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__7_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__0_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__10_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 229, 224, 191, 239, 182, 82, 45)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 228, 31, 241, 142, 75, 34, 234)}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(209) << 1) | 1)),((lean_object*)(((size_t)(29) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(224) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__0_value),((lean_object*)(((size_t)(29) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(209) << 1) | 1)),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(209) << 1) | 1)),((lean_object*)(((size_t)(44) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__3_value),((lean_object*)(((size_t)(33) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__4_value),((lean_object*)(((size_t)(44) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "normCast0"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__5_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__0_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(45, 127, 34, 143, 195, 62, 88, 123)}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__2_value;
static const lean_array_object l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalNormCast0"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__5_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__7_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__0_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__10_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 229, 224, 191, 239, 182, 82, 45)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 95, 7, 173, 250, 13, 126, 205)}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(241) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(253) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(241) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(241) << 1) | 1)),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__4_value),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Conv"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "normCast"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__5_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__0_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(204, 210, 228, 19, 50, 14, 27, 75)}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "evalConvNormCast"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__5_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__7_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__0_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__10_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 229, 224, 191, 239, 182, 82, 45)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(13, 37, 228, 165, 116, 249, 109, 194)}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(256) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(258) << 1) | 1)),((lean_object*)(((size_t)(41) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__1_value),((lean_object*)(((size_t)(41) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(256) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(256) << 1) | 1)),((lean_object*)(((size_t)(20) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__4_value),((lean_object*)(((size_t)(20) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "pushCast"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__5_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__0_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 171, 212, 196, 187, 204, 157, 118)}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "evalPushCast"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__5_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__7_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__0_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__10_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 229, 224, 191, 239, 182, 82, 45)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(91, 23, 255, 99, 127, 149, 218, 153)}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(261) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(266) << 1) | 1)),((lean_object*)(((size_t)(78) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__1_value),((lean_object*)(((size_t)(78) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(261) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(261) << 1) | 1)),((lean_object*)(((size_t)(16) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__4_value),((lean_object*)(((size_t)(16) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "normCastAddElim"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__5_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__0_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__0_value),LEAN_SCALAR_PTR_LITERAL(118, 195, 100, 84, 187, 133, 197, 208)}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__3_value;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__4;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__6;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__8;
static const lean_array_object l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__9_value;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__10;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__11;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__12;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__13;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "elabAddElim"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__5_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__7_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__0_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__10_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 229, 224, 191, 239, 182, 82, 45)}};
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(132, 193, 199, 111, 225, 102, 144, 218)}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(269) << 1) | 1)),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(274) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__0_value),((lean_object*)(((size_t)(54) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(269) << 1) | 1)),((lean_object*)(((size_t)(58) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(269) << 1) | 1)),((lean_object*)(((size_t)(69) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__3_value),((lean_object*)(((size_t)(58) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__4_value),((lean_object*)(((size_t)(69) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_75_; uint8_t v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_75_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__2_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_));
v___x_76_ = 0;
v___x_77_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__30_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_));
v___x_78_ = l_Lean_registerTraceClass(v___x_75_, v___x_76_, v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2____boxed(lean_object* v_a_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_();
return v_res_80_;
}
}
static uint64_t _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__0(void){
_start:
{
uint8_t v___x_81_; uint64_t v___x_82_; 
v___x_81_ = 2;
v___x_82_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_81_);
return v___x_82_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__2(void){
_start:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_90_ = lean_box(0);
v___x_91_ = lean_unsigned_to_nat(16u);
v___x_92_ = lean_mk_array(v___x_91_, v___x_90_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__3(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__2, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__2_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__2);
v___x_94_ = lean_unsigned_to_nat(0u);
v___x_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v___x_93_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__4(void){
_start:
{
lean_object* v___x_96_; 
v___x_96_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_96_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__5(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__4, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__4_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__4);
v___x_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; uint8_t v___x_101_; lean_object* v___x_102_; 
v___x_99_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__5, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__5);
v___x_100_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__3, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__3_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__3);
v___x_101_ = 1;
v___x_102_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_102_, 0, v___x_100_);
lean_ctor_set(v___x_102_, 1, v___x_99_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*2, v___x_101_);
return v___x_102_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__7(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = lean_unsigned_to_nat(0u);
v___x_104_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__5, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__5);
v___x_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v___x_103_);
return v___x_105_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8(void){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = lean_unsigned_to_nat(32u);
v___x_107_ = lean_mk_empty_array_with_capacity(v___x_106_);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__9(void){
_start:
{
size_t v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_109_ = ((size_t)5ULL);
v___x_110_ = lean_unsigned_to_nat(0u);
v___x_111_ = lean_unsigned_to_nat(32u);
v___x_112_ = lean_mk_empty_array_with_capacity(v___x_111_);
v___x_113_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8);
v___x_114_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_112_);
lean_ctor_set(v___x_114_, 2, v___x_110_);
lean_ctor_set(v___x_114_, 3, v___x_110_);
lean_ctor_set_usize(v___x_114_, 4, v___x_109_);
return v___x_114_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__10(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_115_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__9, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__9_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__9);
v___x_116_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__5, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__5);
v___x_117_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
lean_ctor_set(v___x_117_, 2, v___x_116_);
lean_ctor_set(v___x_117_, 3, v___x_115_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__11(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_118_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__10, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__10_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__10);
v___x_119_ = lean_unsigned_to_nat(0u);
v___x_120_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__7, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__7_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__7);
v___x_121_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__3, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__3_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__3);
v___x_122_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6);
v___x_123_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v___x_121_);
lean_ctor_set(v___x_123_, 2, v___x_121_);
lean_ctor_set(v___x_123_, 3, v___x_120_);
lean_ctor_set(v___x_123_, 4, v___x_119_);
lean_ctor_set(v___x_123_, 5, v___x_118_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing(lean_object* v_s_124_, lean_object* v_a_125_, lean_object* v_b_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
lean_object* v___x_132_; uint8_t v_foApprox_133_; uint8_t v_ctxApprox_134_; uint8_t v_quasiPatternApprox_135_; uint8_t v_constApprox_136_; uint8_t v_isDefEqStuckEx_137_; uint8_t v_unificationHints_138_; uint8_t v_proofIrrelevance_139_; uint8_t v_assignSyntheticOpaque_140_; uint8_t v_offsetCnstrs_141_; uint8_t v_etaStruct_142_; uint8_t v_univApprox_143_; uint8_t v_iota_144_; uint8_t v_beta_145_; uint8_t v_proj_146_; uint8_t v_zeta_147_; uint8_t v_zetaDelta_148_; uint8_t v_zetaUnused_149_; uint8_t v_zetaHave_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_278_; 
v___x_132_ = l_Lean_Meta_Context_config(v_a_127_);
v_foApprox_133_ = lean_ctor_get_uint8(v___x_132_, 0);
v_ctxApprox_134_ = lean_ctor_get_uint8(v___x_132_, 1);
v_quasiPatternApprox_135_ = lean_ctor_get_uint8(v___x_132_, 2);
v_constApprox_136_ = lean_ctor_get_uint8(v___x_132_, 3);
v_isDefEqStuckEx_137_ = lean_ctor_get_uint8(v___x_132_, 4);
v_unificationHints_138_ = lean_ctor_get_uint8(v___x_132_, 5);
v_proofIrrelevance_139_ = lean_ctor_get_uint8(v___x_132_, 6);
v_assignSyntheticOpaque_140_ = lean_ctor_get_uint8(v___x_132_, 7);
v_offsetCnstrs_141_ = lean_ctor_get_uint8(v___x_132_, 8);
v_etaStruct_142_ = lean_ctor_get_uint8(v___x_132_, 10);
v_univApprox_143_ = lean_ctor_get_uint8(v___x_132_, 11);
v_iota_144_ = lean_ctor_get_uint8(v___x_132_, 12);
v_beta_145_ = lean_ctor_get_uint8(v___x_132_, 13);
v_proj_146_ = lean_ctor_get_uint8(v___x_132_, 14);
v_zeta_147_ = lean_ctor_get_uint8(v___x_132_, 15);
v_zetaDelta_148_ = lean_ctor_get_uint8(v___x_132_, 16);
v_zetaUnused_149_ = lean_ctor_get_uint8(v___x_132_, 17);
v_zetaHave_150_ = lean_ctor_get_uint8(v___x_132_, 18);
v_isSharedCheck_278_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_278_ == 0)
{
v___x_152_ = v___x_132_;
v_isShared_153_ = v_isSharedCheck_278_;
goto v_resetjp_151_;
}
else
{
lean_dec(v___x_132_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_278_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; 
v___x_154_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_130_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; uint8_t v_trackZetaDelta_156_; lean_object* v_zetaDeltaSet_157_; lean_object* v_lctx_158_; lean_object* v_localInstances_159_; lean_object* v_defEqCtx_x3f_160_; lean_object* v_synthPendingDepth_161_; lean_object* v_canUnfold_x3f_162_; uint8_t v_univApprox_163_; uint8_t v_inTypeClassResolution_164_; uint8_t v_cacheInferType_165_; uint8_t v___x_166_; lean_object* v_config_168_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
lean_inc(v_a_155_);
lean_dec_ref(v___x_154_);
v_trackZetaDelta_156_ = lean_ctor_get_uint8(v_a_127_, sizeof(void*)*7);
v_zetaDeltaSet_157_ = lean_ctor_get(v_a_127_, 1);
v_lctx_158_ = lean_ctor_get(v_a_127_, 2);
v_localInstances_159_ = lean_ctor_get(v_a_127_, 3);
v_defEqCtx_x3f_160_ = lean_ctor_get(v_a_127_, 4);
v_synthPendingDepth_161_ = lean_ctor_get(v_a_127_, 5);
v_canUnfold_x3f_162_ = lean_ctor_get(v_a_127_, 6);
v_univApprox_163_ = lean_ctor_get_uint8(v_a_127_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_164_ = lean_ctor_get_uint8(v_a_127_, sizeof(void*)*7 + 2);
v_cacheInferType_165_ = lean_ctor_get_uint8(v_a_127_, sizeof(void*)*7 + 3);
v___x_166_ = 2;
if (v_isShared_153_ == 0)
{
v_config_168_ = v___x_152_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, 0, v_foApprox_133_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, 1, v_ctxApprox_134_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, 2, v_quasiPatternApprox_135_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, 3, v_constApprox_136_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, 4, v_isDefEqStuckEx_137_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, 5, v_unificationHints_138_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, 6, v_proofIrrelevance_139_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, 7, v_assignSyntheticOpaque_140_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, 8, v_offsetCnstrs_141_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, 10, v_etaStruct_142_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, 11, v_univApprox_143_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, 12, v_iota_144_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, 13, v_beta_145_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, 14, v_proj_146_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, 15, v_zeta_147_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, 16, v_zetaDelta_148_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, 17, v_zetaUnused_149_);
lean_ctor_set_uint8(v_reuseFailAlloc_269_, 18, v_zetaHave_150_);
v_config_168_ = v_reuseFailAlloc_269_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
uint64_t v___x_169_; uint64_t v___x_170_; uint64_t v___x_171_; uint64_t v___x_172_; uint64_t v___x_173_; uint64_t v_key_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
lean_ctor_set_uint8(v_config_168_, 9, v___x_166_);
v___x_169_ = l_Lean_Meta_Context_configKey(v_a_127_);
v___x_170_ = 2ULL;
v___x_171_ = lean_uint64_shift_right(v___x_169_, v___x_170_);
v___x_172_ = lean_uint64_shift_left(v___x_171_, v___x_170_);
v___x_173_ = lean_uint64_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__0, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__0_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__0);
v_key_174_ = lean_uint64_lor(v___x_172_, v___x_173_);
v___x_175_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_175_, 0, v_config_168_);
lean_ctor_set_uint64(v___x_175_, sizeof(void*)*1, v_key_174_);
lean_inc(v_canUnfold_x3f_162_);
lean_inc(v_synthPendingDepth_161_);
lean_inc(v_defEqCtx_x3f_160_);
lean_inc_ref(v_localInstances_159_);
lean_inc_ref(v_lctx_158_);
lean_inc(v_zetaDeltaSet_157_);
v___x_176_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v_zetaDeltaSet_157_);
lean_ctor_set(v___x_176_, 2, v_lctx_158_);
lean_ctor_set(v___x_176_, 3, v_localInstances_159_);
lean_ctor_set(v___x_176_, 4, v_defEqCtx_x3f_160_);
lean_ctor_set(v___x_176_, 5, v_synthPendingDepth_161_);
lean_ctor_set(v___x_176_, 6, v_canUnfold_x3f_162_);
lean_ctor_set_uint8(v___x_176_, sizeof(void*)*7, v_trackZetaDelta_156_);
lean_ctor_set_uint8(v___x_176_, sizeof(void*)*7 + 1, v_univApprox_163_);
lean_ctor_set_uint8(v___x_176_, sizeof(void*)*7 + 2, v_inTypeClassResolution_164_);
lean_ctor_set_uint8(v___x_176_, sizeof(void*)*7 + 3, v_cacheInferType_165_);
v___x_177_ = lean_box(0);
v___x_178_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__1));
v___x_179_ = lean_unsigned_to_nat(1u);
v___x_180_ = lean_mk_empty_array_with_capacity(v___x_179_);
v___x_181_ = lean_array_push(v___x_180_, v_s_124_);
v___x_182_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_178_, v___x_181_, v_a_155_, v___x_176_, v_a_129_, v_a_130_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; lean_object* v___x_184_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_a_183_);
lean_dec_ref(v___x_182_);
v___x_184_ = l_Lean_Meta_Simp_mkDefaultMethods(v_a_129_, v_a_130_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_252_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_252_ == 0)
{
v___x_187_ = v___x_184_;
v_isShared_188_ = v_isSharedCheck_252_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_252_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v_a_192_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_189_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__11, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__11_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__11);
v___x_190_ = lean_st_mk_ref(v___x_189_);
v___x_197_ = l_Lean_Meta_Simp_Methods_toMethodsRefImpl(v_a_185_);
lean_dec(v_a_185_);
lean_inc(v_a_130_);
lean_inc_ref(v_a_129_);
lean_inc(v_a_128_);
lean_inc_ref(v___x_176_);
lean_inc(v___x_190_);
lean_inc(v_a_183_);
lean_inc(v___x_197_);
v___x_198_ = lean_simp(v_a_125_, v___x_197_, v_a_183_, v___x_190_, v___x_176_, v_a_128_, v_a_129_, v_a_130_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_a_199_; lean_object* v___x_200_; 
v_a_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_a_199_);
lean_dec_ref(v___x_198_);
lean_inc(v_a_130_);
lean_inc_ref(v_a_129_);
lean_inc(v_a_128_);
lean_inc_ref(v___x_176_);
lean_inc(v___x_190_);
lean_inc_ref(v_b_126_);
v___x_200_ = lean_simp(v_b_126_, v___x_197_, v_a_183_, v___x_190_, v___x_176_, v_a_128_, v_a_129_, v_a_130_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v_a_201_; lean_object* v_expr_202_; lean_object* v_expr_203_; lean_object* v___x_204_; 
v_a_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_a_201_);
lean_dec_ref(v___x_200_);
v_expr_202_ = lean_ctor_get(v_a_199_, 0);
v_expr_203_ = lean_ctor_get(v_a_201_, 0);
lean_inc_ref(v_expr_203_);
lean_inc_ref(v_expr_202_);
v___x_204_ = l_Lean_Meta_isExprDefEq(v_expr_202_, v_expr_203_, v___x_176_, v_a_128_, v_a_129_, v_a_130_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_a_205_; uint8_t v___x_206_; 
v_a_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_a_205_);
lean_dec_ref(v___x_204_);
v___x_206_ = lean_unbox(v_a_205_);
lean_dec(v_a_205_);
if (v___x_206_ == 0)
{
lean_dec(v_a_201_);
lean_dec(v_a_199_);
lean_dec_ref(v___x_176_);
lean_dec_ref(v_b_126_);
v_a_192_ = v___x_177_;
goto v___jp_191_;
}
else
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_Meta_Simp_Result_mkEqSymm(v_b_126_, v_a_201_, v___x_176_, v_a_128_, v_a_129_, v_a_130_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v___x_209_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_a_208_);
lean_dec_ref(v___x_207_);
v___x_209_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_199_, v_a_208_, v___x_176_, v_a_128_, v_a_129_, v_a_130_);
lean_dec_ref(v___x_176_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_object* v_a_210_; lean_object* v___x_211_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_a_210_);
lean_dec_ref(v___x_209_);
v___x_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_211_, 0, v_a_210_);
v_a_192_ = v___x_211_;
goto v___jp_191_;
}
else
{
lean_object* v_a_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_219_; 
lean_dec(v___x_190_);
lean_del_object(v___x_187_);
v_a_212_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_219_ == 0)
{
v___x_214_ = v___x_209_;
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_a_212_);
lean_dec(v___x_209_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_219_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_217_; 
if (v_isShared_215_ == 0)
{
v___x_217_ = v___x_214_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_a_212_);
v___x_217_ = v_reuseFailAlloc_218_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
return v___x_217_;
}
}
}
}
else
{
lean_object* v_a_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_227_; 
lean_dec(v_a_199_);
lean_dec(v___x_190_);
lean_del_object(v___x_187_);
lean_dec_ref(v___x_176_);
v_a_220_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_227_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_227_ == 0)
{
v___x_222_ = v___x_207_;
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_a_220_);
lean_dec(v___x_207_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_227_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v_a_220_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
}
}
}
else
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
lean_dec(v_a_201_);
lean_dec(v_a_199_);
lean_dec(v___x_190_);
lean_del_object(v___x_187_);
lean_dec_ref(v___x_176_);
lean_dec_ref(v_b_126_);
v_a_228_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_204_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_204_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_228_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
else
{
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_243_; 
lean_dec(v_a_199_);
lean_dec(v___x_190_);
lean_del_object(v___x_187_);
lean_dec_ref(v___x_176_);
lean_dec_ref(v_b_126_);
v_a_236_ = lean_ctor_get(v___x_200_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_200_);
if (v_isSharedCheck_243_ == 0)
{
v___x_238_ = v___x_200_;
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_200_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_236_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
else
{
lean_object* v_a_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_251_; 
lean_dec(v___x_197_);
lean_dec(v___x_190_);
lean_del_object(v___x_187_);
lean_dec(v_a_183_);
lean_dec_ref(v___x_176_);
lean_dec_ref(v_b_126_);
v_a_244_ = lean_ctor_get(v___x_198_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_251_ == 0)
{
v___x_246_ = v___x_198_;
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_a_244_);
lean_dec(v___x_198_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_251_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v___x_249_; 
if (v_isShared_247_ == 0)
{
v___x_249_ = v___x_246_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v_a_244_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
}
v___jp_191_:
{
lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_193_ = lean_st_ref_get(v___x_190_);
lean_dec(v___x_190_);
lean_dec(v___x_193_);
if (v_isShared_188_ == 0)
{
lean_ctor_set(v___x_187_, 0, v_a_192_);
v___x_195_ = v___x_187_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_a_192_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
else
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
lean_dec(v_a_183_);
lean_dec_ref(v___x_176_);
lean_dec_ref(v_b_126_);
lean_dec_ref(v_a_125_);
v_a_253_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_184_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_184_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
lean_dec_ref(v___x_176_);
lean_dec_ref(v_b_126_);
lean_dec_ref(v_a_125_);
v_a_261_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_182_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_182_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_del_object(v___x_152_);
lean_dec_ref(v_b_126_);
lean_dec_ref(v_a_125_);
lean_dec_ref(v_s_124_);
v_a_270_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_154_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_154_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___boxed(lean_object* v_s_279_, lean_object* v_a_280_, lean_object* v_b_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Elab_Tactic_NormCast_proveEqUsing(v_s_279_, v_a_280_, v_b_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(lean_object* v_cls_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_options_294_; uint8_t v_hasTrace_295_; 
v_options_294_ = lean_ctor_get(v___y_292_, 2);
v_hasTrace_295_ = lean_ctor_get_uint8(v_options_294_, sizeof(void*)*1);
if (v_hasTrace_295_ == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; 
lean_dec(v_cls_291_);
v___x_296_ = lean_box(v_hasTrace_295_);
v___x_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
return v___x_297_;
}
else
{
lean_object* v_inheritedTraceOptions_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v_inheritedTraceOptions_298_ = lean_ctor_get(v___y_292_, 13);
v___x_299_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__1));
v___x_300_ = l_Lean_Name_append(v___x_299_, v_cls_291_);
v___x_301_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_298_, v_options_294_, v___x_300_);
lean_dec(v___x_300_);
v___x_302_ = lean_box(v___x_301_);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___boxed(lean_object* v_cls_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v_cls_304_, v___y_305_);
lean_dec_ref(v___y_305_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0(lean_object* v_cls_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v_cls_308_, v___y_311_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___boxed(lean_object* v_cls_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0(v_cls_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
return v_res_321_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_322_ = lean_unsigned_to_nat(32u);
v___x_323_ = lean_mk_empty_array_with_capacity(v___x_322_);
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
return v___x_324_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_325_ = ((size_t)5ULL);
v___x_326_ = lean_unsigned_to_nat(0u);
v___x_327_ = lean_unsigned_to_nat(32u);
v___x_328_ = lean_mk_empty_array_with_capacity(v___x_327_);
v___x_329_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__0);
v___x_330_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___x_328_);
lean_ctor_set(v___x_330_, 2, v___x_326_);
lean_ctor_set(v___x_330_, 3, v___x_326_);
lean_ctor_set_usize(v___x_330_, 4, v___x_325_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg(lean_object* v___y_331_){
_start:
{
lean_object* v___x_333_; lean_object* v_traceState_334_; lean_object* v_traces_335_; lean_object* v___x_336_; lean_object* v_traceState_337_; lean_object* v_env_338_; lean_object* v_nextMacroScope_339_; lean_object* v_ngen_340_; lean_object* v_auxDeclNGen_341_; lean_object* v_cache_342_; lean_object* v_messages_343_; lean_object* v_infoState_344_; lean_object* v_snapshotTasks_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_364_; 
v___x_333_ = lean_st_ref_get(v___y_331_);
v_traceState_334_ = lean_ctor_get(v___x_333_, 4);
lean_inc_ref(v_traceState_334_);
lean_dec(v___x_333_);
v_traces_335_ = lean_ctor_get(v_traceState_334_, 0);
lean_inc_ref(v_traces_335_);
lean_dec_ref(v_traceState_334_);
v___x_336_ = lean_st_ref_take(v___y_331_);
v_traceState_337_ = lean_ctor_get(v___x_336_, 4);
v_env_338_ = lean_ctor_get(v___x_336_, 0);
v_nextMacroScope_339_ = lean_ctor_get(v___x_336_, 1);
v_ngen_340_ = lean_ctor_get(v___x_336_, 2);
v_auxDeclNGen_341_ = lean_ctor_get(v___x_336_, 3);
v_cache_342_ = lean_ctor_get(v___x_336_, 5);
v_messages_343_ = lean_ctor_get(v___x_336_, 6);
v_infoState_344_ = lean_ctor_get(v___x_336_, 7);
v_snapshotTasks_345_ = lean_ctor_get(v___x_336_, 8);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_364_ == 0)
{
v___x_347_ = v___x_336_;
v_isShared_348_ = v_isSharedCheck_364_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_snapshotTasks_345_);
lean_inc(v_infoState_344_);
lean_inc(v_messages_343_);
lean_inc(v_cache_342_);
lean_inc(v_traceState_337_);
lean_inc(v_auxDeclNGen_341_);
lean_inc(v_ngen_340_);
lean_inc(v_nextMacroScope_339_);
lean_inc(v_env_338_);
lean_dec(v___x_336_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_364_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
uint64_t v_tid_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_362_; 
v_tid_349_ = lean_ctor_get_uint64(v_traceState_337_, sizeof(void*)*1);
v_isSharedCheck_362_ = !lean_is_exclusive(v_traceState_337_);
if (v_isSharedCheck_362_ == 0)
{
lean_object* v_unused_363_; 
v_unused_363_ = lean_ctor_get(v_traceState_337_, 0);
lean_dec(v_unused_363_);
v___x_351_ = v_traceState_337_;
v_isShared_352_ = v_isSharedCheck_362_;
goto v_resetjp_350_;
}
else
{
lean_dec(v_traceState_337_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_362_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_353_; lean_object* v___x_355_; 
v___x_353_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__1);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 0, v___x_353_);
v___x_355_ = v___x_351_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_353_);
lean_ctor_set_uint64(v_reuseFailAlloc_361_, sizeof(void*)*1, v_tid_349_);
v___x_355_ = v_reuseFailAlloc_361_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v___x_357_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 4, v___x_355_);
v___x_357_ = v___x_347_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_env_338_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_nextMacroScope_339_);
lean_ctor_set(v_reuseFailAlloc_360_, 2, v_ngen_340_);
lean_ctor_set(v_reuseFailAlloc_360_, 3, v_auxDeclNGen_341_);
lean_ctor_set(v_reuseFailAlloc_360_, 4, v___x_355_);
lean_ctor_set(v_reuseFailAlloc_360_, 5, v_cache_342_);
lean_ctor_set(v_reuseFailAlloc_360_, 6, v_messages_343_);
lean_ctor_set(v_reuseFailAlloc_360_, 7, v_infoState_344_);
lean_ctor_set(v_reuseFailAlloc_360_, 8, v_snapshotTasks_345_);
v___x_357_ = v_reuseFailAlloc_360_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = lean_st_ref_set(v___y_331_, v___x_357_);
v___x_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_359_, 0, v_traces_335_);
return v___x_359_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___boxed(lean_object* v___y_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg(v___y_365_);
lean_dec(v___y_365_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg(v___y_371_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___boxed(lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v___y_374_, v___y_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
return v_res_379_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(lean_object* v_opts_380_, lean_object* v_opt_381_){
_start:
{
lean_object* v_name_382_; lean_object* v_defValue_383_; lean_object* v_map_384_; lean_object* v___x_385_; 
v_name_382_ = lean_ctor_get(v_opt_381_, 0);
v_defValue_383_ = lean_ctor_get(v_opt_381_, 1);
v_map_384_ = lean_ctor_get(v_opts_380_, 0);
v___x_385_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_384_, v_name_382_);
if (lean_obj_tag(v___x_385_) == 0)
{
uint8_t v___x_386_; 
v___x_386_ = lean_unbox(v_defValue_383_);
return v___x_386_;
}
else
{
lean_object* v_val_387_; 
v_val_387_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_val_387_);
lean_dec_ref(v___x_385_);
if (lean_obj_tag(v_val_387_) == 1)
{
uint8_t v_v_388_; 
v_v_388_ = lean_ctor_get_uint8(v_val_387_, 0);
lean_dec_ref(v_val_387_);
return v_v_388_;
}
else
{
uint8_t v___x_389_; 
lean_dec(v_val_387_);
v___x_389_ = lean_unbox(v_defValue_383_);
return v___x_389_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___boxed(lean_object* v_opts_390_, lean_object* v_opt_391_){
_start:
{
uint8_t v_res_392_; lean_object* v_r_393_; 
v_res_392_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_opts_390_, v_opt_391_);
lean_dec_ref(v_opt_391_);
lean_dec_ref(v_opts_390_);
v_r_393_ = lean_box(v_res_392_);
return v_r_393_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__1(void){
_start:
{
lean_object* v___x_395_; lean_object* v___x_396_; 
v___x_395_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__0));
v___x_396_ = l_Lean_stringToMessageData(v___x_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0(lean_object* v_a_397_, lean_object* v_b_398_, lean_object* v_x_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Meta_mkEq(v_a_397_, v_b_398_, v___y_400_, v___y_401_, v___y_402_, v___y_403_);
if (lean_obj_tag(v___x_405_) == 0)
{
lean_object* v_a_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_416_; 
v_a_406_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_416_ == 0)
{
v___x_408_ = v___x_405_;
v_isShared_409_ = v_isSharedCheck_416_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_a_406_);
lean_dec(v___x_405_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_416_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_414_; 
v___x_410_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__1, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__1);
v___x_411_ = l_Lean_MessageData_ofExpr(v_a_406_);
v___x_412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_410_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 0, v___x_412_);
v___x_414_ = v___x_408_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v___x_412_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
else
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
v_a_417_ = lean_ctor_get(v___x_405_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_405_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_405_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_405_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___boxed(lean_object* v_a_425_, lean_object* v_b_426_, lean_object* v_x_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0(v_a_425_, v_b_426_, v_x_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_);
lean_dec(v___y_431_);
lean_dec_ref(v___y_430_);
lean_dec(v___y_429_);
lean_dec_ref(v___y_428_);
lean_dec_ref(v_x_427_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5___redArg(lean_object* v_x_434_){
_start:
{
if (lean_obj_tag(v_x_434_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_443_; 
v_a_436_ = lean_ctor_get(v_x_434_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v_x_434_);
if (v_isSharedCheck_443_ == 0)
{
v___x_438_ = v_x_434_;
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_a_436_);
lean_dec(v_x_434_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_443_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_441_; 
if (v_isShared_439_ == 0)
{
lean_ctor_set_tag(v___x_438_, 1);
v___x_441_ = v___x_438_;
goto v_reusejp_440_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_a_436_);
v___x_441_ = v_reuseFailAlloc_442_;
goto v_reusejp_440_;
}
v_reusejp_440_:
{
return v___x_441_;
}
}
}
else
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_451_; 
v_a_444_ = lean_ctor_get(v_x_434_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v_x_434_);
if (v_isSharedCheck_451_ == 0)
{
v___x_446_ = v_x_434_;
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v_x_434_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_451_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_449_; 
if (v_isShared_447_ == 0)
{
lean_ctor_set_tag(v___x_446_, 0);
v___x_449_ = v___x_446_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_444_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5___redArg___boxed(lean_object* v_x_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5___redArg(v_x_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__6(lean_object* v_opts_455_, lean_object* v_opt_456_){
_start:
{
lean_object* v_name_457_; lean_object* v_defValue_458_; lean_object* v_map_459_; lean_object* v___x_460_; 
v_name_457_ = lean_ctor_get(v_opt_456_, 0);
v_defValue_458_ = lean_ctor_get(v_opt_456_, 1);
v_map_459_ = lean_ctor_get(v_opts_455_, 0);
v___x_460_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_459_, v_name_457_);
if (lean_obj_tag(v___x_460_) == 0)
{
lean_inc(v_defValue_458_);
return v_defValue_458_;
}
else
{
lean_object* v_val_461_; 
v_val_461_ = lean_ctor_get(v___x_460_, 0);
lean_inc(v_val_461_);
lean_dec_ref(v___x_460_);
if (lean_obj_tag(v_val_461_) == 3)
{
lean_object* v_v_462_; 
v_v_462_ = lean_ctor_get(v_val_461_, 0);
lean_inc(v_v_462_);
lean_dec_ref(v_val_461_);
return v_v_462_;
}
else
{
lean_dec(v_val_461_);
lean_inc(v_defValue_458_);
return v_defValue_458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__6___boxed(lean_object* v_opts_463_, lean_object* v_opt_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__6(v_opts_463_, v_opt_464_);
lean_dec_ref(v_opt_464_);
lean_dec_ref(v_opts_463_);
return v_res_465_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__3(lean_object* v_e_466_){
_start:
{
if (lean_obj_tag(v_e_466_) == 0)
{
uint8_t v___x_467_; 
v___x_467_ = 2;
return v___x_467_;
}
else
{
lean_object* v_a_468_; 
v_a_468_ = lean_ctor_get(v_e_466_, 0);
if (lean_obj_tag(v_a_468_) == 0)
{
uint8_t v___x_469_; 
v___x_469_ = 1;
return v___x_469_;
}
else
{
uint8_t v___x_470_; 
v___x_470_ = 0;
return v___x_470_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__3___boxed(lean_object* v_e_471_){
_start:
{
uint8_t v_res_472_; lean_object* v_r_473_; 
v_res_472_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__3(v_e_471_);
lean_dec_ref(v_e_471_);
v_r_473_ = lean_box(v_res_472_);
return v_r_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__6(lean_object* v_msgData_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v___x_480_; lean_object* v_env_481_; lean_object* v___x_482_; lean_object* v_mctx_483_; lean_object* v_lctx_484_; lean_object* v_options_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_480_ = lean_st_ref_get(v___y_478_);
v_env_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc_ref(v_env_481_);
lean_dec(v___x_480_);
v___x_482_ = lean_st_ref_get(v___y_476_);
v_mctx_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc_ref(v_mctx_483_);
lean_dec(v___x_482_);
v_lctx_484_ = lean_ctor_get(v___y_475_, 2);
v_options_485_ = lean_ctor_get(v___y_477_, 2);
lean_inc_ref(v_options_485_);
lean_inc_ref(v_lctx_484_);
v___x_486_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_486_, 0, v_env_481_);
lean_ctor_set(v___x_486_, 1, v_mctx_483_);
lean_ctor_set(v___x_486_, 2, v_lctx_484_);
lean_ctor_set(v___x_486_, 3, v_options_485_);
v___x_487_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v_msgData_474_);
v___x_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__6___boxed(lean_object* v_msgData_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__6(v_msgData_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
lean_dec(v___y_493_);
lean_dec_ref(v___y_492_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__5(size_t v_sz_496_, size_t v_i_497_, lean_object* v_bs_498_){
_start:
{
uint8_t v___x_499_; 
v___x_499_ = lean_usize_dec_lt(v_i_497_, v_sz_496_);
if (v___x_499_ == 0)
{
return v_bs_498_;
}
else
{
lean_object* v_v_500_; lean_object* v_msg_501_; lean_object* v___x_502_; lean_object* v_bs_x27_503_; size_t v___x_504_; size_t v___x_505_; lean_object* v___x_506_; 
v_v_500_ = lean_array_uget_borrowed(v_bs_498_, v_i_497_);
v_msg_501_ = lean_ctor_get(v_v_500_, 1);
lean_inc_ref(v_msg_501_);
v___x_502_ = lean_unsigned_to_nat(0u);
v_bs_x27_503_ = lean_array_uset(v_bs_498_, v_i_497_, v___x_502_);
v___x_504_ = ((size_t)1ULL);
v___x_505_ = lean_usize_add(v_i_497_, v___x_504_);
v___x_506_ = lean_array_uset(v_bs_x27_503_, v_i_497_, v_msg_501_);
v_i_497_ = v___x_505_;
v_bs_498_ = v___x_506_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_508_, lean_object* v_i_509_, lean_object* v_bs_510_){
_start:
{
size_t v_sz_boxed_511_; size_t v_i_boxed_512_; lean_object* v_res_513_; 
v_sz_boxed_511_ = lean_unbox_usize(v_sz_508_);
lean_dec(v_sz_508_);
v_i_boxed_512_ = lean_unbox_usize(v_i_509_);
lean_dec(v_i_509_);
v_res_513_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__5(v_sz_boxed_511_, v_i_boxed_512_, v_bs_510_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4(lean_object* v_oldTraces_514_, lean_object* v_data_515_, lean_object* v_ref_516_, lean_object* v_msg_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v_fileName_523_; lean_object* v_fileMap_524_; lean_object* v_options_525_; lean_object* v_currRecDepth_526_; lean_object* v_maxRecDepth_527_; lean_object* v_ref_528_; lean_object* v_currNamespace_529_; lean_object* v_openDecls_530_; lean_object* v_initHeartbeats_531_; lean_object* v_maxHeartbeats_532_; lean_object* v_quotContext_533_; lean_object* v_currMacroScope_534_; uint8_t v_diag_535_; lean_object* v_cancelTk_x3f_536_; uint8_t v_suppressElabErrors_537_; lean_object* v_inheritedTraceOptions_538_; lean_object* v___x_539_; lean_object* v_traceState_540_; lean_object* v_traces_541_; lean_object* v_ref_542_; lean_object* v___x_543_; lean_object* v___x_544_; size_t v_sz_545_; size_t v___x_546_; lean_object* v___x_547_; lean_object* v_msg_548_; lean_object* v___x_549_; lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_587_; 
v_fileName_523_ = lean_ctor_get(v___y_520_, 0);
v_fileMap_524_ = lean_ctor_get(v___y_520_, 1);
v_options_525_ = lean_ctor_get(v___y_520_, 2);
v_currRecDepth_526_ = lean_ctor_get(v___y_520_, 3);
v_maxRecDepth_527_ = lean_ctor_get(v___y_520_, 4);
v_ref_528_ = lean_ctor_get(v___y_520_, 5);
v_currNamespace_529_ = lean_ctor_get(v___y_520_, 6);
v_openDecls_530_ = lean_ctor_get(v___y_520_, 7);
v_initHeartbeats_531_ = lean_ctor_get(v___y_520_, 8);
v_maxHeartbeats_532_ = lean_ctor_get(v___y_520_, 9);
v_quotContext_533_ = lean_ctor_get(v___y_520_, 10);
v_currMacroScope_534_ = lean_ctor_get(v___y_520_, 11);
v_diag_535_ = lean_ctor_get_uint8(v___y_520_, sizeof(void*)*14);
v_cancelTk_x3f_536_ = lean_ctor_get(v___y_520_, 12);
v_suppressElabErrors_537_ = lean_ctor_get_uint8(v___y_520_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_538_ = lean_ctor_get(v___y_520_, 13);
v___x_539_ = lean_st_ref_get(v___y_521_);
v_traceState_540_ = lean_ctor_get(v___x_539_, 4);
lean_inc_ref(v_traceState_540_);
lean_dec(v___x_539_);
v_traces_541_ = lean_ctor_get(v_traceState_540_, 0);
lean_inc_ref(v_traces_541_);
lean_dec_ref(v_traceState_540_);
v_ref_542_ = l_Lean_replaceRef(v_ref_516_, v_ref_528_);
lean_inc_ref(v_inheritedTraceOptions_538_);
lean_inc(v_cancelTk_x3f_536_);
lean_inc(v_currMacroScope_534_);
lean_inc(v_quotContext_533_);
lean_inc(v_maxHeartbeats_532_);
lean_inc(v_initHeartbeats_531_);
lean_inc(v_openDecls_530_);
lean_inc(v_currNamespace_529_);
lean_inc(v_maxRecDepth_527_);
lean_inc(v_currRecDepth_526_);
lean_inc_ref(v_options_525_);
lean_inc_ref(v_fileMap_524_);
lean_inc_ref(v_fileName_523_);
v___x_543_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_543_, 0, v_fileName_523_);
lean_ctor_set(v___x_543_, 1, v_fileMap_524_);
lean_ctor_set(v___x_543_, 2, v_options_525_);
lean_ctor_set(v___x_543_, 3, v_currRecDepth_526_);
lean_ctor_set(v___x_543_, 4, v_maxRecDepth_527_);
lean_ctor_set(v___x_543_, 5, v_ref_542_);
lean_ctor_set(v___x_543_, 6, v_currNamespace_529_);
lean_ctor_set(v___x_543_, 7, v_openDecls_530_);
lean_ctor_set(v___x_543_, 8, v_initHeartbeats_531_);
lean_ctor_set(v___x_543_, 9, v_maxHeartbeats_532_);
lean_ctor_set(v___x_543_, 10, v_quotContext_533_);
lean_ctor_set(v___x_543_, 11, v_currMacroScope_534_);
lean_ctor_set(v___x_543_, 12, v_cancelTk_x3f_536_);
lean_ctor_set(v___x_543_, 13, v_inheritedTraceOptions_538_);
lean_ctor_set_uint8(v___x_543_, sizeof(void*)*14, v_diag_535_);
lean_ctor_set_uint8(v___x_543_, sizeof(void*)*14 + 1, v_suppressElabErrors_537_);
v___x_544_ = l_Lean_PersistentArray_toArray___redArg(v_traces_541_);
lean_dec_ref(v_traces_541_);
v_sz_545_ = lean_array_size(v___x_544_);
v___x_546_ = ((size_t)0ULL);
v___x_547_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__5(v_sz_545_, v___x_546_, v___x_544_);
v_msg_548_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_548_, 0, v_data_515_);
lean_ctor_set(v_msg_548_, 1, v_msg_517_);
lean_ctor_set(v_msg_548_, 2, v___x_547_);
v___x_549_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__6(v_msg_548_, v___y_518_, v___y_519_, v___x_543_, v___y_521_);
lean_dec_ref(v___x_543_);
v_a_550_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_587_ == 0)
{
v___x_552_ = v___x_549_;
v_isShared_553_ = v_isSharedCheck_587_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_549_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_587_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v_traceState_555_; lean_object* v_env_556_; lean_object* v_nextMacroScope_557_; lean_object* v_ngen_558_; lean_object* v_auxDeclNGen_559_; lean_object* v_cache_560_; lean_object* v_messages_561_; lean_object* v_infoState_562_; lean_object* v_snapshotTasks_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_586_; 
v___x_554_ = lean_st_ref_take(v___y_521_);
v_traceState_555_ = lean_ctor_get(v___x_554_, 4);
v_env_556_ = lean_ctor_get(v___x_554_, 0);
v_nextMacroScope_557_ = lean_ctor_get(v___x_554_, 1);
v_ngen_558_ = lean_ctor_get(v___x_554_, 2);
v_auxDeclNGen_559_ = lean_ctor_get(v___x_554_, 3);
v_cache_560_ = lean_ctor_get(v___x_554_, 5);
v_messages_561_ = lean_ctor_get(v___x_554_, 6);
v_infoState_562_ = lean_ctor_get(v___x_554_, 7);
v_snapshotTasks_563_ = lean_ctor_get(v___x_554_, 8);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_554_);
if (v_isSharedCheck_586_ == 0)
{
v___x_565_ = v___x_554_;
v_isShared_566_ = v_isSharedCheck_586_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_snapshotTasks_563_);
lean_inc(v_infoState_562_);
lean_inc(v_messages_561_);
lean_inc(v_cache_560_);
lean_inc(v_traceState_555_);
lean_inc(v_auxDeclNGen_559_);
lean_inc(v_ngen_558_);
lean_inc(v_nextMacroScope_557_);
lean_inc(v_env_556_);
lean_dec(v___x_554_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_586_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
uint64_t v_tid_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_584_; 
v_tid_567_ = lean_ctor_get_uint64(v_traceState_555_, sizeof(void*)*1);
v_isSharedCheck_584_ = !lean_is_exclusive(v_traceState_555_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; 
v_unused_585_ = lean_ctor_get(v_traceState_555_, 0);
lean_dec(v_unused_585_);
v___x_569_ = v_traceState_555_;
v_isShared_570_ = v_isSharedCheck_584_;
goto v_resetjp_568_;
}
else
{
lean_dec(v_traceState_555_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_584_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_571_, 0, v_ref_516_);
lean_ctor_set(v___x_571_, 1, v_a_550_);
v___x_572_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_514_, v___x_571_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_572_);
v___x_574_ = v___x_569_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_583_; 
v_reuseFailAlloc_583_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_583_, 0, v___x_572_);
lean_ctor_set_uint64(v_reuseFailAlloc_583_, sizeof(void*)*1, v_tid_567_);
v___x_574_ = v_reuseFailAlloc_583_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_576_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 4, v___x_574_);
v___x_576_ = v___x_565_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_env_556_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_nextMacroScope_557_);
lean_ctor_set(v_reuseFailAlloc_582_, 2, v_ngen_558_);
lean_ctor_set(v_reuseFailAlloc_582_, 3, v_auxDeclNGen_559_);
lean_ctor_set(v_reuseFailAlloc_582_, 4, v___x_574_);
lean_ctor_set(v_reuseFailAlloc_582_, 5, v_cache_560_);
lean_ctor_set(v_reuseFailAlloc_582_, 6, v_messages_561_);
lean_ctor_set(v_reuseFailAlloc_582_, 7, v_infoState_562_);
lean_ctor_set(v_reuseFailAlloc_582_, 8, v_snapshotTasks_563_);
v___x_576_ = v_reuseFailAlloc_582_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_580_; 
v___x_577_ = lean_st_ref_set(v___y_521_, v___x_576_);
v___x_578_ = lean_box(0);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_578_);
v___x_580_ = v___x_552_;
goto v_reusejp_579_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_578_);
v___x_580_ = v_reuseFailAlloc_581_;
goto v_reusejp_579_;
}
v_reusejp_579_:
{
return v___x_580_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4___boxed(lean_object* v_oldTraces_588_, lean_object* v_data_589_, lean_object* v_ref_590_, lean_object* v_msg_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4(v_oldTraces_588_, v_data_589_, v_ref_590_, v_msg_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
return v_res_597_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__0));
v___x_600_ = l_Lean_stringToMessageData(v___x_599_);
return v___x_600_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2(void){
_start:
{
lean_object* v___x_601_; double v___x_602_; 
v___x_601_ = lean_unsigned_to_nat(0u);
v___x_602_ = lean_float_of_nat(v___x_601_);
return v___x_602_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__4(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__3));
v___x_605_ = l_Lean_stringToMessageData(v___x_604_);
return v___x_605_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__5(void){
_start:
{
lean_object* v___x_606_; double v___x_607_; 
v___x_606_ = lean_unsigned_to_nat(1000u);
v___x_607_ = lean_float_of_nat(v___x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3(lean_object* v_cls_608_, uint8_t v_collapsed_609_, lean_object* v_tag_610_, lean_object* v_opts_611_, uint8_t v_clsEnabled_612_, lean_object* v_oldTraces_613_, lean_object* v_msg_614_, lean_object* v_resStartStop_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
lean_object* v_fst_621_; lean_object* v_snd_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_720_; 
v_fst_621_ = lean_ctor_get(v_resStartStop_615_, 0);
v_snd_622_ = lean_ctor_get(v_resStartStop_615_, 1);
v_isSharedCheck_720_ = !lean_is_exclusive(v_resStartStop_615_);
if (v_isSharedCheck_720_ == 0)
{
v___x_624_ = v_resStartStop_615_;
v_isShared_625_ = v_isSharedCheck_720_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_snd_622_);
lean_inc(v_fst_621_);
lean_dec(v_resStartStop_615_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_720_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v_data_629_; lean_object* v_fst_640_; lean_object* v_snd_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_719_; 
v_fst_640_ = lean_ctor_get(v_snd_622_, 0);
v_snd_641_ = lean_ctor_get(v_snd_622_, 1);
v_isSharedCheck_719_ = !lean_is_exclusive(v_snd_622_);
if (v_isSharedCheck_719_ == 0)
{
v___x_643_ = v_snd_622_;
v_isShared_644_ = v_isSharedCheck_719_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_snd_641_);
lean_inc(v_fst_640_);
lean_dec(v_snd_622_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_719_;
goto v_resetjp_642_;
}
v___jp_626_:
{
lean_object* v___x_630_; 
lean_inc(v___y_627_);
v___x_630_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4(v_oldTraces_613_, v_data_629_, v___y_627_, v___y_628_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v___x_631_; 
lean_dec_ref(v___x_630_);
v___x_631_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5___redArg(v_fst_621_);
return v___x_631_;
}
else
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_639_; 
lean_dec(v_fst_621_);
v_a_632_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_639_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_639_ == 0)
{
v___x_634_ = v___x_630_;
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_630_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_639_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_637_; 
if (v_isShared_635_ == 0)
{
v___x_637_ = v___x_634_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_a_632_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
v_resetjp_642_:
{
lean_object* v___x_645_; uint8_t v___x_646_; lean_object* v___y_648_; lean_object* v_a_649_; uint8_t v___y_673_; double v___y_704_; 
v___x_645_ = l_Lean_trace_profiler;
v___x_646_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_opts_611_, v___x_645_);
if (v___x_646_ == 0)
{
v___y_673_ = v___x_646_;
goto v___jp_672_;
}
else
{
lean_object* v___x_709_; uint8_t v___x_710_; 
v___x_709_ = l_Lean_trace_profiler_useHeartbeats;
v___x_710_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_opts_611_, v___x_709_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; lean_object* v___x_712_; double v___x_713_; double v___x_714_; double v___x_715_; 
v___x_711_ = l_Lean_trace_profiler_threshold;
v___x_712_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__6(v_opts_611_, v___x_711_);
v___x_713_ = lean_float_of_nat(v___x_712_);
v___x_714_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__5);
v___x_715_ = lean_float_div(v___x_713_, v___x_714_);
v___y_704_ = v___x_715_;
goto v___jp_703_;
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; double v___x_718_; 
v___x_716_ = l_Lean_trace_profiler_threshold;
v___x_717_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__6(v_opts_611_, v___x_716_);
v___x_718_ = lean_float_of_nat(v___x_717_);
v___y_704_ = v___x_718_;
goto v___jp_703_;
}
}
v___jp_647_:
{
uint8_t v_result_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_655_; 
v_result_650_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__3(v_fst_621_);
v___x_651_ = l_Lean_TraceResult_toEmoji(v_result_650_);
v___x_652_ = l_Lean_stringToMessageData(v___x_651_);
v___x_653_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1);
if (v_isShared_644_ == 0)
{
lean_ctor_set_tag(v___x_643_, 7);
lean_ctor_set(v___x_643_, 1, v___x_653_);
lean_ctor_set(v___x_643_, 0, v___x_652_);
v___x_655_ = v___x_643_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_652_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v___x_653_);
v___x_655_ = v_reuseFailAlloc_666_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v_m_657_; 
if (v_isShared_625_ == 0)
{
lean_ctor_set_tag(v___x_624_, 7);
lean_ctor_set(v___x_624_, 1, v_a_649_);
lean_ctor_set(v___x_624_, 0, v___x_655_);
v_m_657_ = v___x_624_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_a_649_);
v_m_657_ = v_reuseFailAlloc_665_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_658_; lean_object* v___x_659_; double v___x_660_; lean_object* v_data_661_; 
v___x_658_ = lean_box(v_result_650_);
v___x_659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
v___x_660_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2);
lean_inc_ref(v_tag_610_);
lean_inc_ref(v___x_659_);
lean_inc(v_cls_608_);
v_data_661_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_661_, 0, v_cls_608_);
lean_ctor_set(v_data_661_, 1, v___x_659_);
lean_ctor_set(v_data_661_, 2, v_tag_610_);
lean_ctor_set_float(v_data_661_, sizeof(void*)*3, v___x_660_);
lean_ctor_set_float(v_data_661_, sizeof(void*)*3 + 8, v___x_660_);
lean_ctor_set_uint8(v_data_661_, sizeof(void*)*3 + 16, v_collapsed_609_);
if (v___x_646_ == 0)
{
lean_dec_ref(v___x_659_);
lean_dec(v_snd_641_);
lean_dec(v_fst_640_);
lean_dec_ref(v_tag_610_);
lean_dec(v_cls_608_);
v___y_627_ = v___y_648_;
v___y_628_ = v_m_657_;
v_data_629_ = v_data_661_;
goto v___jp_626_;
}
else
{
lean_object* v_data_662_; double v___x_663_; double v___x_664_; 
lean_dec_ref(v_data_661_);
v_data_662_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_662_, 0, v_cls_608_);
lean_ctor_set(v_data_662_, 1, v___x_659_);
lean_ctor_set(v_data_662_, 2, v_tag_610_);
v___x_663_ = lean_unbox_float(v_fst_640_);
lean_dec(v_fst_640_);
lean_ctor_set_float(v_data_662_, sizeof(void*)*3, v___x_663_);
v___x_664_ = lean_unbox_float(v_snd_641_);
lean_dec(v_snd_641_);
lean_ctor_set_float(v_data_662_, sizeof(void*)*3 + 8, v___x_664_);
lean_ctor_set_uint8(v_data_662_, sizeof(void*)*3 + 16, v_collapsed_609_);
v___y_627_ = v___y_648_;
v___y_628_ = v_m_657_;
v_data_629_ = v_data_662_;
goto v___jp_626_;
}
}
}
}
v___jp_667_:
{
lean_object* v_ref_668_; lean_object* v___x_669_; 
v_ref_668_ = lean_ctor_get(v___y_618_, 5);
lean_inc(v___y_619_);
lean_inc_ref(v___y_618_);
lean_inc(v___y_617_);
lean_inc_ref(v___y_616_);
lean_inc(v_fst_621_);
v___x_669_ = lean_apply_6(v_msg_614_, v_fst_621_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, lean_box(0));
if (lean_obj_tag(v___x_669_) == 0)
{
lean_object* v_a_670_; 
v_a_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_a_670_);
lean_dec_ref(v___x_669_);
v___y_648_ = v_ref_668_;
v_a_649_ = v_a_670_;
goto v___jp_647_;
}
else
{
lean_object* v___x_671_; 
lean_dec_ref(v___x_669_);
v___x_671_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__4);
v___y_648_ = v_ref_668_;
v_a_649_ = v___x_671_;
goto v___jp_647_;
}
}
v___jp_672_:
{
if (v_clsEnabled_612_ == 0)
{
if (v___y_673_ == 0)
{
lean_object* v___x_674_; lean_object* v_traceState_675_; lean_object* v_env_676_; lean_object* v_nextMacroScope_677_; lean_object* v_ngen_678_; lean_object* v_auxDeclNGen_679_; lean_object* v_cache_680_; lean_object* v_messages_681_; lean_object* v_infoState_682_; lean_object* v_snapshotTasks_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_702_; 
lean_del_object(v___x_643_);
lean_dec(v_snd_641_);
lean_dec(v_fst_640_);
lean_del_object(v___x_624_);
lean_dec_ref(v_msg_614_);
lean_dec_ref(v_tag_610_);
lean_dec(v_cls_608_);
v___x_674_ = lean_st_ref_take(v___y_619_);
v_traceState_675_ = lean_ctor_get(v___x_674_, 4);
v_env_676_ = lean_ctor_get(v___x_674_, 0);
v_nextMacroScope_677_ = lean_ctor_get(v___x_674_, 1);
v_ngen_678_ = lean_ctor_get(v___x_674_, 2);
v_auxDeclNGen_679_ = lean_ctor_get(v___x_674_, 3);
v_cache_680_ = lean_ctor_get(v___x_674_, 5);
v_messages_681_ = lean_ctor_get(v___x_674_, 6);
v_infoState_682_ = lean_ctor_get(v___x_674_, 7);
v_snapshotTasks_683_ = lean_ctor_get(v___x_674_, 8);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_702_ == 0)
{
v___x_685_ = v___x_674_;
v_isShared_686_ = v_isSharedCheck_702_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_snapshotTasks_683_);
lean_inc(v_infoState_682_);
lean_inc(v_messages_681_);
lean_inc(v_cache_680_);
lean_inc(v_traceState_675_);
lean_inc(v_auxDeclNGen_679_);
lean_inc(v_ngen_678_);
lean_inc(v_nextMacroScope_677_);
lean_inc(v_env_676_);
lean_dec(v___x_674_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_702_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
uint64_t v_tid_687_; lean_object* v_traces_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_701_; 
v_tid_687_ = lean_ctor_get_uint64(v_traceState_675_, sizeof(void*)*1);
v_traces_688_ = lean_ctor_get(v_traceState_675_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v_traceState_675_);
if (v_isSharedCheck_701_ == 0)
{
v___x_690_ = v_traceState_675_;
v_isShared_691_ = v_isSharedCheck_701_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_traces_688_);
lean_dec(v_traceState_675_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_701_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_692_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_613_, v_traces_688_);
lean_dec_ref(v_traces_688_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_692_);
v___x_694_ = v___x_690_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_692_);
lean_ctor_set_uint64(v_reuseFailAlloc_700_, sizeof(void*)*1, v_tid_687_);
v___x_694_ = v_reuseFailAlloc_700_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_696_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 4, v___x_694_);
v___x_696_ = v___x_685_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_env_676_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v_nextMacroScope_677_);
lean_ctor_set(v_reuseFailAlloc_699_, 2, v_ngen_678_);
lean_ctor_set(v_reuseFailAlloc_699_, 3, v_auxDeclNGen_679_);
lean_ctor_set(v_reuseFailAlloc_699_, 4, v___x_694_);
lean_ctor_set(v_reuseFailAlloc_699_, 5, v_cache_680_);
lean_ctor_set(v_reuseFailAlloc_699_, 6, v_messages_681_);
lean_ctor_set(v_reuseFailAlloc_699_, 7, v_infoState_682_);
lean_ctor_set(v_reuseFailAlloc_699_, 8, v_snapshotTasks_683_);
v___x_696_ = v_reuseFailAlloc_699_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_st_ref_set(v___y_619_, v___x_696_);
v___x_698_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5___redArg(v_fst_621_);
return v___x_698_;
}
}
}
}
}
else
{
goto v___jp_667_;
}
}
else
{
goto v___jp_667_;
}
}
v___jp_703_:
{
double v___x_705_; double v___x_706_; double v___x_707_; uint8_t v___x_708_; 
v___x_705_ = lean_unbox_float(v_snd_641_);
v___x_706_ = lean_unbox_float(v_fst_640_);
v___x_707_ = lean_float_sub(v___x_705_, v___x_706_);
v___x_708_ = lean_float_decLt(v___y_704_, v___x_707_);
v___y_673_ = v___x_708_;
goto v___jp_672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___boxed(lean_object* v_cls_721_, lean_object* v_collapsed_722_, lean_object* v_tag_723_, lean_object* v_opts_724_, lean_object* v_clsEnabled_725_, lean_object* v_oldTraces_726_, lean_object* v_msg_727_, lean_object* v_resStartStop_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
uint8_t v_collapsed_boxed_734_; uint8_t v_clsEnabled_boxed_735_; lean_object* v_res_736_; 
v_collapsed_boxed_734_ = lean_unbox(v_collapsed_722_);
v_clsEnabled_boxed_735_ = lean_unbox(v_clsEnabled_725_);
v_res_736_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3(v_cls_721_, v_collapsed_boxed_734_, v_tag_723_, v_opts_724_, v_clsEnabled_boxed_735_, v_oldTraces_726_, v_msg_727_, v_resStartStop_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec_ref(v_opts_724_);
return v_res_736_;
}
}
static double _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1(void){
_start:
{
lean_object* v___x_738_; double v___x_739_; 
v___x_738_ = lean_unsigned_to_nat(1000000000u);
v___x_739_ = lean_float_of_nat(v___x_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(lean_object* v_a_740_, lean_object* v_b_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v___x_747_; lean_object* v_options_748_; uint8_t v_hasTrace_749_; 
v___x_747_ = l_Lean_Meta_NormCast_normCastExt;
v_options_748_ = lean_ctor_get(v_a_744_, 2);
v_hasTrace_749_ = lean_ctor_get_uint8(v_options_748_, sizeof(void*)*1);
if (v_hasTrace_749_ == 0)
{
lean_object* v_down_750_; lean_object* v___x_751_; 
v_down_750_ = lean_ctor_get(v___x_747_, 1);
lean_inc_ref(v_down_750_);
v___x_751_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_down_750_, v_a_745_);
lean_dec_ref(v_down_750_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v_a_752_; lean_object* v___x_753_; 
v_a_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_a_752_);
lean_dec_ref(v___x_751_);
v___x_753_ = l_Lean_Elab_Tactic_NormCast_proveEqUsing(v_a_752_, v_a_740_, v_b_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
return v___x_753_;
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec_ref(v_b_741_);
lean_dec_ref(v_a_740_);
v_a_754_ = lean_ctor_get(v___x_751_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_751_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_751_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
else
{
lean_object* v_down_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_859_; 
v_down_762_ = lean_ctor_get(v___x_747_, 1);
lean_inc_ref(v_down_762_);
v___x_763_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__2_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_));
v___x_764_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___x_763_, v_a_744_);
v_a_765_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_859_ == 0)
{
v___x_767_ = v___x_764_;
v_isShared_768_ = v_isSharedCheck_859_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_764_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_859_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___f_769_; lean_object* v___x_770_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v_a_774_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v_a_790_; lean_object* v___y_795_; lean_object* v___y_796_; lean_object* v_a_797_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v_a_810_; uint8_t v___x_845_; 
lean_inc_ref(v_b_741_);
lean_inc_ref(v_a_740_);
v___f_769_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___boxed), 8, 2);
lean_closure_set(v___f_769_, 0, v_a_740_);
lean_closure_set(v___f_769_, 1, v_b_741_);
v___x_770_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_845_ = lean_unbox(v_a_765_);
if (v___x_845_ == 0)
{
lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_846_ = l_Lean_trace_profiler;
v___x_847_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_748_, v___x_846_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; 
lean_dec_ref(v___f_769_);
lean_del_object(v___x_767_);
lean_dec(v_a_765_);
v___x_848_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_down_762_, v_a_745_);
lean_dec_ref(v_down_762_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_850_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref(v___x_848_);
v___x_850_ = l_Lean_Elab_Tactic_NormCast_proveEqUsing(v_a_849_, v_a_740_, v_b_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
return v___x_850_;
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
lean_dec_ref(v_b_741_);
lean_dec_ref(v_a_740_);
v_a_851_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_848_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_848_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
else
{
goto v___jp_812_;
}
}
else
{
goto v___jp_812_;
}
v___jp_771_:
{
lean_object* v___x_775_; double v___x_776_; double v___x_777_; double v___x_778_; double v___x_779_; double v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; uint8_t v___x_785_; lean_object* v___x_786_; 
v___x_775_ = lean_io_mono_nanos_now();
v___x_776_ = lean_float_of_nat(v___y_773_);
v___x_777_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1);
v___x_778_ = lean_float_div(v___x_776_, v___x_777_);
v___x_779_ = lean_float_of_nat(v___x_775_);
v___x_780_ = lean_float_div(v___x_779_, v___x_777_);
v___x_781_ = lean_box_float(v___x_778_);
v___x_782_ = lean_box_float(v___x_780_);
v___x_783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_781_);
lean_ctor_set(v___x_783_, 1, v___x_782_);
v___x_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_784_, 0, v_a_774_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
v___x_785_ = lean_unbox(v_a_765_);
lean_dec(v_a_765_);
v___x_786_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3(v___x_763_, v_hasTrace_749_, v___x_770_, v_options_748_, v___x_785_, v___y_772_, v___f_769_, v___x_784_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
return v___x_786_;
}
v___jp_787_:
{
lean_object* v___x_792_; 
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v_a_790_);
v___x_792_ = v___x_767_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
v___y_772_ = v___y_788_;
v___y_773_ = v___y_789_;
v_a_774_ = v___x_792_;
goto v___jp_771_;
}
}
v___jp_794_:
{
lean_object* v___x_798_; double v___x_799_; double v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; uint8_t v___x_805_; lean_object* v___x_806_; 
v___x_798_ = lean_io_get_num_heartbeats();
v___x_799_ = lean_float_of_nat(v___y_795_);
v___x_800_ = lean_float_of_nat(v___x_798_);
v___x_801_ = lean_box_float(v___x_799_);
v___x_802_ = lean_box_float(v___x_800_);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_801_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v_a_797_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = lean_unbox(v_a_765_);
lean_dec(v_a_765_);
v___x_806_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3(v___x_763_, v_hasTrace_749_, v___x_770_, v_options_748_, v___x_805_, v___y_796_, v___f_769_, v___x_804_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
return v___x_806_;
}
v___jp_807_:
{
lean_object* v___x_811_; 
v___x_811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_811_, 0, v_a_810_);
v___y_795_ = v___y_808_;
v___y_796_ = v___y_809_;
v_a_797_ = v___x_811_;
goto v___jp_794_;
}
v___jp_812_:
{
lean_object* v___x_813_; lean_object* v_a_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v___x_813_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg(v_a_745_);
v_a_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_814_);
lean_dec_ref(v___x_813_);
v___x_815_ = l_Lean_trace_profiler_useHeartbeats;
v___x_816_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_748_, v___x_815_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = lean_io_mono_nanos_now();
v___x_818_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_down_762_, v_a_745_);
lean_dec_ref(v_down_762_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_820_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
lean_dec_ref(v___x_818_);
v___x_820_ = l_Lean_Elab_Tactic_NormCast_proveEqUsing(v_a_819_, v_a_740_, v_b_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
if (lean_obj_tag(v___x_820_) == 0)
{
lean_object* v_a_821_; lean_object* v___x_823_; uint8_t v_isShared_824_; uint8_t v_isSharedCheck_828_; 
lean_del_object(v___x_767_);
v_a_821_ = lean_ctor_get(v___x_820_, 0);
v_isSharedCheck_828_ = !lean_is_exclusive(v___x_820_);
if (v_isSharedCheck_828_ == 0)
{
v___x_823_ = v___x_820_;
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
else
{
lean_inc(v_a_821_);
lean_dec(v___x_820_);
v___x_823_ = lean_box(0);
v_isShared_824_ = v_isSharedCheck_828_;
goto v_resetjp_822_;
}
v_resetjp_822_:
{
lean_object* v___x_826_; 
if (v_isShared_824_ == 0)
{
lean_ctor_set_tag(v___x_823_, 1);
v___x_826_ = v___x_823_;
goto v_reusejp_825_;
}
else
{
lean_object* v_reuseFailAlloc_827_; 
v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_821_);
v___x_826_ = v_reuseFailAlloc_827_;
goto v_reusejp_825_;
}
v_reusejp_825_:
{
v___y_772_ = v_a_814_;
v___y_773_ = v___x_817_;
v_a_774_ = v___x_826_;
goto v___jp_771_;
}
}
}
else
{
lean_object* v_a_829_; 
v_a_829_ = lean_ctor_get(v___x_820_, 0);
lean_inc(v_a_829_);
lean_dec_ref(v___x_820_);
v___y_788_ = v_a_814_;
v___y_789_ = v___x_817_;
v_a_790_ = v_a_829_;
goto v___jp_787_;
}
}
else
{
lean_object* v_a_830_; 
lean_dec_ref(v_b_741_);
lean_dec_ref(v_a_740_);
v_a_830_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_830_);
lean_dec_ref(v___x_818_);
v___y_788_ = v_a_814_;
v___y_789_ = v___x_817_;
v_a_790_ = v_a_830_;
goto v___jp_787_;
}
}
else
{
lean_object* v___x_831_; lean_object* v___x_832_; 
lean_del_object(v___x_767_);
v___x_831_ = lean_io_get_num_heartbeats();
v___x_832_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_down_762_, v_a_745_);
lean_dec_ref(v_down_762_);
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v___x_834_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref(v___x_832_);
v___x_834_ = l_Lean_Elab_Tactic_NormCast_proveEqUsing(v_a_833_, v_a_740_, v_b_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
if (lean_obj_tag(v___x_834_) == 0)
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
v_a_835_ = lean_ctor_get(v___x_834_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_834_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_834_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_834_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
lean_ctor_set_tag(v___x_837_, 1);
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
v___y_795_ = v___x_831_;
v___y_796_ = v_a_814_;
v_a_797_ = v___x_840_;
goto v___jp_794_;
}
}
}
else
{
lean_object* v_a_843_; 
v_a_843_ = lean_ctor_get(v___x_834_, 0);
lean_inc(v_a_843_);
lean_dec_ref(v___x_834_);
v___y_808_ = v___x_831_;
v___y_809_ = v_a_814_;
v_a_810_ = v_a_843_;
goto v___jp_807_;
}
}
else
{
lean_object* v_a_844_; 
lean_dec_ref(v_b_741_);
lean_dec_ref(v_a_740_);
v_a_844_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_844_);
lean_dec_ref(v___x_832_);
v___y_808_ = v___x_831_;
v___y_809_ = v_a_814_;
v_a_810_ = v_a_844_;
goto v___jp_807_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___boxed(lean_object* v_a_860_, lean_object* v_b_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v_res_867_; 
v_res_867_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_a_860_, v_b_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
lean_dec(v_a_863_);
lean_dec_ref(v_a_862_);
return v_res_867_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5(lean_object* v_00_u03b1_868_, lean_object* v_x_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5___redArg(v_x_869_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5___boxed(lean_object* v_00_u03b1_876_, lean_object* v_x_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5(v_00_u03b1_876_, v_x_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(lean_object* v_msg_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
lean_object* v_ref_890_; lean_object* v___x_891_; lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_900_; 
v_ref_890_ = lean_ctor_get(v___y_887_, 5);
v___x_891_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__6(v_msg_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
v_a_892_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_900_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_900_ == 0)
{
v___x_894_ = v___x_891_;
v_isShared_895_ = v_isSharedCheck_900_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_891_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_900_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_896_; lean_object* v___x_898_; 
lean_inc(v_ref_890_);
v___x_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_896_, 0, v_ref_890_);
lean_ctor_set(v___x_896_, 1, v_a_892_);
if (v_isShared_895_ == 0)
{
lean_ctor_set_tag(v___x_894_, 1);
lean_ctor_set(v___x_894_, 0, v___x_896_);
v___x_898_ = v___x_894_;
goto v_reusejp_897_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_896_);
v___x_898_ = v_reuseFailAlloc_899_;
goto v_reusejp_897_;
}
v_reusejp_897_:
{
return v___x_898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg___boxed(lean_object* v_msg_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v_msg_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
return v_res_907_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_mkCoe___closed__0));
v___x_910_ = l_Lean_stringToMessageData(v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_mkCoe(lean_object* v_e_911_, lean_object* v_ty_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l_Lean_Meta_coerce_x3f(v_e_911_, v_ty_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_929_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_929_ == 0)
{
v___x_921_ = v___x_918_;
v_isShared_922_ = v_isSharedCheck_929_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_918_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_929_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
if (lean_obj_tag(v_a_919_) == 1)
{
lean_object* v_a_923_; lean_object* v___x_925_; 
v_a_923_ = lean_ctor_get(v_a_919_, 0);
lean_inc(v_a_923_);
lean_dec_ref(v_a_919_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v_a_923_);
v___x_925_ = v___x_921_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_923_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; 
lean_del_object(v___x_921_);
lean_dec(v_a_919_);
v___x_927_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_928_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_927_, v_a_913_, v_a_914_, v_a_915_, v_a_916_);
return v___x_928_;
}
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
v_a_930_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_918_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_918_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_mkCoe___boxed(lean_object* v_e_938_, lean_object* v_ty_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_e_938_, v_ty_939_, v_a_940_, v_a_941_, v_a_942_, v_a_943_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0(lean_object* v_00_u03b1_946_, lean_object* v_msg_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v___x_953_; 
v___x_953_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v_msg_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___boxed(lean_object* v_00_u03b1_954_, lean_object* v_msg_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0(v_00_u03b1_954_, v_msg_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(lean_object* v_e_962_, lean_object* v_a_963_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Lean_Expr_getAppFn(v_e_962_);
if (lean_obj_tag(v___x_968_) == 4)
{
lean_object* v_declName_969_; lean_object* v___x_970_; 
v_declName_969_ = lean_ctor_get(v___x_968_, 0);
lean_inc(v_declName_969_);
lean_dec_ref(v___x_968_);
v___x_970_ = l_Lean_Meta_getCoeFnInfo_x3f___redArg(v_declName_969_, v_a_963_);
lean_dec(v_declName_969_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_994_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_994_ == 0)
{
v___x_973_ = v___x_970_;
v_isShared_974_ = v_isSharedCheck_994_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_970_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_994_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
if (lean_obj_tag(v_a_971_) == 1)
{
lean_object* v_val_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_993_; 
v_val_975_ = lean_ctor_get(v_a_971_, 0);
v_isSharedCheck_993_ = !lean_is_exclusive(v_a_971_);
if (v_isSharedCheck_993_ == 0)
{
v___x_977_ = v_a_971_;
v_isShared_978_ = v_isSharedCheck_993_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_val_975_);
lean_dec(v_a_971_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_993_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v_numArgs_979_; lean_object* v_coercee_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
v_numArgs_979_ = lean_ctor_get(v_val_975_, 0);
lean_inc(v_numArgs_979_);
v_coercee_980_ = lean_ctor_get(v_val_975_, 1);
lean_inc(v_coercee_980_);
lean_dec(v_val_975_);
v___x_981_ = l_Lean_Expr_getAppNumArgs(v_e_962_);
v___x_982_ = lean_nat_dec_eq(v___x_981_, v_numArgs_979_);
lean_dec(v_numArgs_979_);
if (v___x_982_ == 0)
{
lean_dec(v___x_981_);
lean_dec(v_coercee_980_);
lean_del_object(v___x_977_);
lean_del_object(v___x_973_);
goto v___jp_965_;
}
else
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_988_; 
v___x_983_ = lean_nat_sub(v___x_981_, v_coercee_980_);
lean_dec(v_coercee_980_);
lean_dec(v___x_981_);
v___x_984_ = lean_unsigned_to_nat(1u);
v___x_985_ = lean_nat_sub(v___x_983_, v___x_984_);
lean_dec(v___x_983_);
v___x_986_ = l_Lean_Expr_getRevArg_x21(v_e_962_, v___x_985_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_986_);
v___x_988_ = v___x_977_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v___x_986_);
v___x_988_ = v_reuseFailAlloc_992_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
lean_object* v___x_990_; 
if (v_isShared_974_ == 0)
{
lean_ctor_set(v___x_973_, 0, v___x_988_);
v___x_990_ = v___x_973_;
goto v_reusejp_989_;
}
else
{
lean_object* v_reuseFailAlloc_991_; 
v_reuseFailAlloc_991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_991_, 0, v___x_988_);
v___x_990_ = v_reuseFailAlloc_991_;
goto v_reusejp_989_;
}
v_reusejp_989_:
{
return v___x_990_;
}
}
}
}
}
else
{
lean_del_object(v___x_973_);
lean_dec(v_a_971_);
goto v___jp_965_;
}
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
v_a_995_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_970_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_970_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
else
{
lean_dec_ref(v___x_968_);
goto v___jp_965_;
}
v___jp_965_:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = lean_box(0);
v___x_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
return v___x_967_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg___boxed(lean_object* v_e_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_e_1003_, v_a_1004_);
lean_dec(v_a_1004_);
lean_dec_ref(v_e_1003_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f(lean_object* v_e_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_e_1007_, v_a_1011_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___boxed(lean_object* v_e_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f(v_e_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec_ref(v_e_1014_);
return v_res_1020_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__6(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1030_ = lean_box(0);
v___x_1031_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__5));
v___x_1032_ = l_Lean_mkConst(v___x_1031_, v___x_1030_);
return v___x_1032_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__7(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1033_ = lean_unsigned_to_nat(0u);
v___x_1034_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__6, &l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__6_once, _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__6);
v___x_1035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
lean_ctor_set(v___x_1035_, 1, v___x_1033_);
return v___x_1035_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__8(void){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__7, &l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__7_once, _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__7);
v___x_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(lean_object* v_e_1038_){
_start:
{
lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1039_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__2));
v___x_1040_ = l_Lean_Expr_isConstOf(v_e_1038_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Lean_Expr_consumeMData(v_e_1038_);
if (lean_obj_tag(v___x_1041_) == 5)
{
lean_object* v_fn_1042_; 
v_fn_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc_ref(v_fn_1042_);
lean_dec_ref(v___x_1041_);
if (lean_obj_tag(v_fn_1042_) == 5)
{
lean_object* v_fn_1043_; 
v_fn_1043_ = lean_ctor_get(v_fn_1042_, 0);
lean_inc_ref(v_fn_1043_);
if (lean_obj_tag(v_fn_1043_) == 5)
{
lean_object* v_fn_1044_; 
v_fn_1044_ = lean_ctor_get(v_fn_1043_, 0);
if (lean_obj_tag(v_fn_1044_) == 4)
{
lean_object* v_declName_1045_; 
v_declName_1045_ = lean_ctor_get(v_fn_1044_, 0);
lean_inc(v_declName_1045_);
if (lean_obj_tag(v_declName_1045_) == 1)
{
lean_object* v_pre_1046_; 
v_pre_1046_ = lean_ctor_get(v_declName_1045_, 0);
lean_inc(v_pre_1046_);
if (lean_obj_tag(v_pre_1046_) == 1)
{
lean_object* v_pre_1047_; 
v_pre_1047_ = lean_ctor_get(v_pre_1046_, 0);
if (lean_obj_tag(v_pre_1047_) == 0)
{
lean_object* v_arg_1048_; lean_object* v_arg_1049_; lean_object* v_str_1050_; lean_object* v_str_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
v_arg_1048_ = lean_ctor_get(v_fn_1042_, 1);
lean_inc_ref(v_arg_1048_);
lean_dec_ref(v_fn_1042_);
v_arg_1049_ = lean_ctor_get(v_fn_1043_, 1);
lean_inc_ref(v_arg_1049_);
lean_dec_ref(v_fn_1043_);
v_str_1050_ = lean_ctor_get(v_declName_1045_, 1);
lean_inc_ref(v_str_1050_);
lean_dec_ref(v_declName_1045_);
v_str_1051_ = lean_ctor_get(v_pre_1046_, 1);
lean_inc_ref(v_str_1051_);
lean_dec_ref(v_pre_1046_);
v___x_1052_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__3));
v___x_1053_ = lean_string_dec_eq(v_str_1051_, v___x_1052_);
lean_dec_ref(v_str_1051_);
if (v___x_1053_ == 0)
{
lean_object* v___x_1054_; 
lean_dec_ref(v_str_1050_);
lean_dec_ref(v_arg_1049_);
lean_dec_ref(v_arg_1048_);
v___x_1054_ = lean_box(0);
return v___x_1054_;
}
else
{
lean_object* v___x_1055_; uint8_t v___x_1056_; 
v___x_1055_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__4));
v___x_1056_ = lean_string_dec_eq(v_str_1050_, v___x_1055_);
lean_dec_ref(v_str_1050_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; 
lean_dec_ref(v_arg_1049_);
lean_dec_ref(v_arg_1048_);
v___x_1057_ = lean_box(0);
return v___x_1057_;
}
else
{
if (lean_obj_tag(v_arg_1048_) == 9)
{
lean_object* v_a_1058_; 
v_a_1058_ = lean_ctor_get(v_arg_1048_, 0);
lean_inc_ref(v_a_1058_);
lean_dec_ref(v_arg_1048_);
if (lean_obj_tag(v_a_1058_) == 0)
{
lean_object* v_val_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1067_; 
v_val_1059_ = lean_ctor_get(v_a_1058_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_a_1058_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1061_ = v_a_1058_;
v_isShared_1062_ = v_isSharedCheck_1067_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_val_1059_);
lean_dec(v_a_1058_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1067_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1065_; 
v___x_1063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1063_, 0, v_arg_1049_);
lean_ctor_set(v___x_1063_, 1, v_val_1059_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set_tag(v___x_1061_, 1);
lean_ctor_set(v___x_1061_, 0, v___x_1063_);
v___x_1065_ = v___x_1061_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1063_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
else
{
lean_object* v___x_1068_; 
lean_dec_ref(v_a_1058_);
lean_dec_ref(v_arg_1049_);
v___x_1068_ = lean_box(0);
return v___x_1068_;
}
}
else
{
lean_object* v___x_1069_; 
lean_dec_ref(v_arg_1049_);
lean_dec_ref(v_arg_1048_);
v___x_1069_ = lean_box(0);
return v___x_1069_;
}
}
}
}
else
{
lean_object* v___x_1070_; 
lean_dec_ref(v_pre_1046_);
lean_dec_ref(v_declName_1045_);
lean_dec_ref(v_fn_1043_);
lean_dec_ref(v_fn_1042_);
v___x_1070_ = lean_box(0);
return v___x_1070_;
}
}
else
{
lean_object* v___x_1071_; 
lean_dec(v_pre_1046_);
lean_dec_ref(v_declName_1045_);
lean_dec_ref(v_fn_1043_);
lean_dec_ref(v_fn_1042_);
v___x_1071_ = lean_box(0);
return v___x_1071_;
}
}
else
{
lean_object* v___x_1072_; 
lean_dec(v_declName_1045_);
lean_dec_ref(v_fn_1043_);
lean_dec_ref(v_fn_1042_);
v___x_1072_ = lean_box(0);
return v___x_1072_;
}
}
else
{
lean_object* v___x_1073_; 
lean_dec_ref(v_fn_1043_);
lean_dec_ref(v_fn_1042_);
v___x_1073_ = lean_box(0);
return v___x_1073_;
}
}
else
{
lean_object* v___x_1074_; 
lean_dec_ref(v_fn_1042_);
lean_dec_ref(v_fn_1043_);
v___x_1074_ = lean_box(0);
return v___x_1074_;
}
}
else
{
lean_object* v___x_1075_; 
lean_dec_ref(v_fn_1042_);
v___x_1075_ = lean_box(0);
return v___x_1075_;
}
}
else
{
lean_object* v___x_1076_; 
lean_dec_ref(v___x_1041_);
v___x_1076_ = lean_box(0);
return v___x_1076_;
}
}
else
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__8, &l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__8);
return v___x_1077_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___boxed(lean_object* v_e_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_e_1078_);
lean_dec_ref(v_e_1078_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(lean_object* v_x_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
v___x_1086_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1087_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1086_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1087_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1087_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0___boxed(lean_object* v_x_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v_x_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec(v___y_1100_);
lean_dec_ref(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v_x_1096_);
return v_res_1102_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___closed__0));
v___x_1105_ = l_Lean_stringToMessageData(v___x_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4(lean_object* v___x_1106_, lean_object* v_expr_1107_, lean_object* v_x_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
if (lean_obj_tag(v_x_1108_) == 0)
{
lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
v_isSharedCheck_1120_ = !lean_is_exclusive(v_x_1108_);
if (v_isSharedCheck_1120_ == 0)
{
lean_object* v_unused_1121_; 
v_unused_1121_ = lean_ctor_get(v_x_1108_, 0);
lean_dec(v_unused_1121_);
v___x_1115_ = v_x_1108_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_dec(v_x_1108_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1106_);
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1106_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1138_; 
v_a_1122_ = lean_ctor_get(v_x_1108_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_x_1108_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1124_ = v_x_1108_;
v_isShared_1125_ = v_isSharedCheck_1138_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v_x_1108_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1138_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v_expr_1126_; uint8_t v___x_1127_; 
v_expr_1126_ = lean_ctor_get(v_a_1122_, 0);
lean_inc_ref(v_expr_1126_);
lean_dec(v_a_1122_);
v___x_1127_ = lean_expr_eqv(v_expr_1126_, v_expr_1107_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1133_; 
v___x_1128_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___closed__1, &l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___closed__1);
v___x_1129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1106_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___x_1130_ = l_Lean_MessageData_ofExpr(v_expr_1126_);
v___x_1131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1129_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set_tag(v___x_1124_, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1131_);
v___x_1133_ = v___x_1124_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v___x_1131_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
else
{
lean_object* v___x_1136_; 
lean_dec_ref(v_expr_1126_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set_tag(v___x_1124_, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1106_);
v___x_1136_ = v___x_1124_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1106_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___boxed(lean_object* v___x_1139_, lean_object* v_expr_1140_, lean_object* v_x_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4(v___x_1139_, v_expr_1140_, v_x_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec_ref(v_expr_1140_);
return v_res_1147_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0_spec__0(lean_object* v_e_1148_){
_start:
{
if (lean_obj_tag(v_e_1148_) == 0)
{
uint8_t v___x_1149_; 
v___x_1149_ = 2;
return v___x_1149_;
}
else
{
uint8_t v___x_1150_; 
v___x_1150_ = 0;
return v___x_1150_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0_spec__0___boxed(lean_object* v_e_1151_){
_start:
{
uint8_t v_res_1152_; lean_object* v_r_1153_; 
v_res_1152_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0_spec__0(v_e_1151_);
lean_dec_ref(v_e_1151_);
v_r_1153_ = lean_box(v_res_1152_);
return v_r_1153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(lean_object* v_cls_1154_, uint8_t v_collapsed_1155_, lean_object* v_tag_1156_, lean_object* v_opts_1157_, uint8_t v_clsEnabled_1158_, lean_object* v_oldTraces_1159_, lean_object* v_msg_1160_, lean_object* v_resStartStop_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_fst_1167_; lean_object* v_snd_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1266_; 
v_fst_1167_ = lean_ctor_get(v_resStartStop_1161_, 0);
v_snd_1168_ = lean_ctor_get(v_resStartStop_1161_, 1);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_resStartStop_1161_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1170_ = v_resStartStop_1161_;
v_isShared_1171_ = v_isSharedCheck_1266_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_snd_1168_);
lean_inc(v_fst_1167_);
lean_dec(v_resStartStop_1161_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1266_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v_data_1175_; lean_object* v_fst_1186_; lean_object* v_snd_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1265_; 
v_fst_1186_ = lean_ctor_get(v_snd_1168_, 0);
v_snd_1187_ = lean_ctor_get(v_snd_1168_, 1);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_snd_1168_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1189_ = v_snd_1168_;
v_isShared_1190_ = v_isSharedCheck_1265_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_snd_1187_);
lean_inc(v_fst_1186_);
lean_dec(v_snd_1168_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1265_;
goto v_resetjp_1188_;
}
v___jp_1172_:
{
lean_object* v___x_1176_; 
lean_inc(v___y_1173_);
v___x_1176_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4(v_oldTraces_1159_, v_data_1175_, v___y_1173_, v___y_1174_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v___x_1177_; 
lean_dec_ref(v___x_1176_);
v___x_1177_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5___redArg(v_fst_1167_);
return v___x_1177_;
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec(v_fst_1167_);
v_a_1178_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1176_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1176_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; uint8_t v___x_1192_; lean_object* v___y_1194_; lean_object* v_a_1195_; uint8_t v___y_1219_; double v___y_1250_; 
v___x_1191_ = l_Lean_trace_profiler;
v___x_1192_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_opts_1157_, v___x_1191_);
if (v___x_1192_ == 0)
{
v___y_1219_ = v___x_1192_;
goto v___jp_1218_;
}
else
{
lean_object* v___x_1255_; uint8_t v___x_1256_; 
v___x_1255_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1256_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_opts_1157_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; double v___x_1259_; double v___x_1260_; double v___x_1261_; 
v___x_1257_ = l_Lean_trace_profiler_threshold;
v___x_1258_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__6(v_opts_1157_, v___x_1257_);
v___x_1259_ = lean_float_of_nat(v___x_1258_);
v___x_1260_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__5);
v___x_1261_ = lean_float_div(v___x_1259_, v___x_1260_);
v___y_1250_ = v___x_1261_;
goto v___jp_1249_;
}
else
{
lean_object* v___x_1262_; lean_object* v___x_1263_; double v___x_1264_; 
v___x_1262_ = l_Lean_trace_profiler_threshold;
v___x_1263_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__6(v_opts_1157_, v___x_1262_);
v___x_1264_ = lean_float_of_nat(v___x_1263_);
v___y_1250_ = v___x_1264_;
goto v___jp_1249_;
}
}
v___jp_1193_:
{
uint8_t v_result_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1201_; 
v_result_1196_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0_spec__0(v_fst_1167_);
v___x_1197_ = l_Lean_TraceResult_toEmoji(v_result_1196_);
v___x_1198_ = l_Lean_stringToMessageData(v___x_1197_);
v___x_1199_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1);
if (v_isShared_1190_ == 0)
{
lean_ctor_set_tag(v___x_1189_, 7);
lean_ctor_set(v___x_1189_, 1, v___x_1199_);
lean_ctor_set(v___x_1189_, 0, v___x_1198_);
v___x_1201_ = v___x_1189_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1198_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
lean_object* v_m_1203_; 
if (v_isShared_1171_ == 0)
{
lean_ctor_set_tag(v___x_1170_, 7);
lean_ctor_set(v___x_1170_, 1, v_a_1195_);
lean_ctor_set(v___x_1170_, 0, v___x_1201_);
v_m_1203_ = v___x_1170_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1201_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_a_1195_);
v_m_1203_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; double v___x_1206_; lean_object* v_data_1207_; 
v___x_1204_ = lean_box(v_result_1196_);
v___x_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1204_);
v___x_1206_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2);
lean_inc_ref(v_tag_1156_);
lean_inc_ref(v___x_1205_);
lean_inc(v_cls_1154_);
v_data_1207_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1207_, 0, v_cls_1154_);
lean_ctor_set(v_data_1207_, 1, v___x_1205_);
lean_ctor_set(v_data_1207_, 2, v_tag_1156_);
lean_ctor_set_float(v_data_1207_, sizeof(void*)*3, v___x_1206_);
lean_ctor_set_float(v_data_1207_, sizeof(void*)*3 + 8, v___x_1206_);
lean_ctor_set_uint8(v_data_1207_, sizeof(void*)*3 + 16, v_collapsed_1155_);
if (v___x_1192_ == 0)
{
lean_dec_ref(v___x_1205_);
lean_dec(v_snd_1187_);
lean_dec(v_fst_1186_);
lean_dec_ref(v_tag_1156_);
lean_dec(v_cls_1154_);
v___y_1173_ = v___y_1194_;
v___y_1174_ = v_m_1203_;
v_data_1175_ = v_data_1207_;
goto v___jp_1172_;
}
else
{
lean_object* v_data_1208_; double v___x_1209_; double v___x_1210_; 
lean_dec_ref(v_data_1207_);
v_data_1208_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1208_, 0, v_cls_1154_);
lean_ctor_set(v_data_1208_, 1, v___x_1205_);
lean_ctor_set(v_data_1208_, 2, v_tag_1156_);
v___x_1209_ = lean_unbox_float(v_fst_1186_);
lean_dec(v_fst_1186_);
lean_ctor_set_float(v_data_1208_, sizeof(void*)*3, v___x_1209_);
v___x_1210_ = lean_unbox_float(v_snd_1187_);
lean_dec(v_snd_1187_);
lean_ctor_set_float(v_data_1208_, sizeof(void*)*3 + 8, v___x_1210_);
lean_ctor_set_uint8(v_data_1208_, sizeof(void*)*3 + 16, v_collapsed_1155_);
v___y_1173_ = v___y_1194_;
v___y_1174_ = v_m_1203_;
v_data_1175_ = v_data_1208_;
goto v___jp_1172_;
}
}
}
}
v___jp_1213_:
{
lean_object* v_ref_1214_; lean_object* v___x_1215_; 
v_ref_1214_ = lean_ctor_get(v___y_1164_, 5);
lean_inc(v___y_1165_);
lean_inc_ref(v___y_1164_);
lean_inc(v___y_1163_);
lean_inc_ref(v___y_1162_);
lean_inc(v_fst_1167_);
v___x_1215_ = lean_apply_6(v_msg_1160_, v_fst_1167_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, lean_box(0));
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref(v___x_1215_);
v___y_1194_ = v_ref_1214_;
v_a_1195_ = v_a_1216_;
goto v___jp_1193_;
}
else
{
lean_object* v___x_1217_; 
lean_dec_ref(v___x_1215_);
v___x_1217_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__4);
v___y_1194_ = v_ref_1214_;
v_a_1195_ = v___x_1217_;
goto v___jp_1193_;
}
}
v___jp_1218_:
{
if (v_clsEnabled_1158_ == 0)
{
if (v___y_1219_ == 0)
{
lean_object* v___x_1220_; lean_object* v_traceState_1221_; lean_object* v_env_1222_; lean_object* v_nextMacroScope_1223_; lean_object* v_ngen_1224_; lean_object* v_auxDeclNGen_1225_; lean_object* v_cache_1226_; lean_object* v_messages_1227_; lean_object* v_infoState_1228_; lean_object* v_snapshotTasks_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1248_; 
lean_del_object(v___x_1189_);
lean_dec(v_snd_1187_);
lean_dec(v_fst_1186_);
lean_del_object(v___x_1170_);
lean_dec_ref(v_msg_1160_);
lean_dec_ref(v_tag_1156_);
lean_dec(v_cls_1154_);
v___x_1220_ = lean_st_ref_take(v___y_1165_);
v_traceState_1221_ = lean_ctor_get(v___x_1220_, 4);
v_env_1222_ = lean_ctor_get(v___x_1220_, 0);
v_nextMacroScope_1223_ = lean_ctor_get(v___x_1220_, 1);
v_ngen_1224_ = lean_ctor_get(v___x_1220_, 2);
v_auxDeclNGen_1225_ = lean_ctor_get(v___x_1220_, 3);
v_cache_1226_ = lean_ctor_get(v___x_1220_, 5);
v_messages_1227_ = lean_ctor_get(v___x_1220_, 6);
v_infoState_1228_ = lean_ctor_get(v___x_1220_, 7);
v_snapshotTasks_1229_ = lean_ctor_get(v___x_1220_, 8);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1220_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1231_ = v___x_1220_;
v_isShared_1232_ = v_isSharedCheck_1248_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_snapshotTasks_1229_);
lean_inc(v_infoState_1228_);
lean_inc(v_messages_1227_);
lean_inc(v_cache_1226_);
lean_inc(v_traceState_1221_);
lean_inc(v_auxDeclNGen_1225_);
lean_inc(v_ngen_1224_);
lean_inc(v_nextMacroScope_1223_);
lean_inc(v_env_1222_);
lean_dec(v___x_1220_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1248_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
uint64_t v_tid_1233_; lean_object* v_traces_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1247_; 
v_tid_1233_ = lean_ctor_get_uint64(v_traceState_1221_, sizeof(void*)*1);
v_traces_1234_ = lean_ctor_get(v_traceState_1221_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_traceState_1221_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1236_ = v_traceState_1221_;
v_isShared_1237_ = v_isSharedCheck_1247_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_traces_1234_);
lean_dec(v_traceState_1221_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1247_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1238_; lean_object* v___x_1240_; 
v___x_1238_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1159_, v_traces_1234_);
lean_dec_ref(v_traces_1234_);
if (v_isShared_1237_ == 0)
{
lean_ctor_set(v___x_1236_, 0, v___x_1238_);
v___x_1240_ = v___x_1236_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1238_);
lean_ctor_set_uint64(v_reuseFailAlloc_1246_, sizeof(void*)*1, v_tid_1233_);
v___x_1240_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
lean_object* v___x_1242_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 4, v___x_1240_);
v___x_1242_ = v___x_1231_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_env_1222_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v_nextMacroScope_1223_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v_ngen_1224_);
lean_ctor_set(v_reuseFailAlloc_1245_, 3, v_auxDeclNGen_1225_);
lean_ctor_set(v_reuseFailAlloc_1245_, 4, v___x_1240_);
lean_ctor_set(v_reuseFailAlloc_1245_, 5, v_cache_1226_);
lean_ctor_set(v_reuseFailAlloc_1245_, 6, v_messages_1227_);
lean_ctor_set(v_reuseFailAlloc_1245_, 7, v_infoState_1228_);
lean_ctor_set(v_reuseFailAlloc_1245_, 8, v_snapshotTasks_1229_);
v___x_1242_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_st_ref_set(v___y_1165_, v___x_1242_);
v___x_1244_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5___redArg(v_fst_1167_);
return v___x_1244_;
}
}
}
}
}
else
{
goto v___jp_1213_;
}
}
else
{
goto v___jp_1213_;
}
}
v___jp_1249_:
{
double v___x_1251_; double v___x_1252_; double v___x_1253_; uint8_t v___x_1254_; 
v___x_1251_ = lean_unbox_float(v_snd_1187_);
v___x_1252_ = lean_unbox_float(v_fst_1186_);
v___x_1253_ = lean_float_sub(v___x_1251_, v___x_1252_);
v___x_1254_ = lean_float_decLt(v___y_1250_, v___x_1253_);
v___y_1219_ = v___x_1254_;
goto v___jp_1218_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0___boxed(lean_object* v_cls_1267_, lean_object* v_collapsed_1268_, lean_object* v_tag_1269_, lean_object* v_opts_1270_, lean_object* v_clsEnabled_1271_, lean_object* v_oldTraces_1272_, lean_object* v_msg_1273_, lean_object* v_resStartStop_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
uint8_t v_collapsed_boxed_1280_; uint8_t v_clsEnabled_boxed_1281_; lean_object* v_res_1282_; 
v_collapsed_boxed_1280_ = lean_unbox(v_collapsed_1268_);
v_clsEnabled_boxed_1281_ = lean_unbox(v_clsEnabled_1271_);
v_res_1282_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v_cls_1267_, v_collapsed_boxed_1280_, v_tag_1269_, v_opts_1270_, v_clsEnabled_boxed_1281_, v_oldTraces_1272_, v_msg_1273_, v_resStartStop_1274_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec_ref(v_opts_1270_);
return v_res_1282_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___closed__1(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_splittingProcedure___closed__0));
v___x_1285_ = l_Lean_stringToMessageData(v___x_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure(lean_object* v_expr_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_){
_start:
{
lean_object* v___y_1293_; uint8_t v___y_1294_; uint8_t v___y_1295_; uint8_t v___y_1301_; lean_object* v_a_1302_; uint8_t v___y_1306_; lean_object* v___y_1307_; uint8_t v___y_1308_; uint8_t v___y_1314_; lean_object* v_a_1315_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; uint8_t v___y_1323_; uint8_t v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v_a_1327_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; uint8_t v___y_1344_; uint8_t v___y_1345_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v_a_1348_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; uint8_t v___y_1355_; uint8_t v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v_a_1359_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; lean_object* v___y_1366_; uint8_t v___y_1367_; uint8_t v___y_1368_; lean_object* v___y_1369_; lean_object* v___y_1370_; uint8_t v___y_1371_; lean_object* v___y_1375_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; uint8_t v___y_1379_; uint8_t v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v_a_1383_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; uint8_t v___y_1391_; uint8_t v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v_a_1395_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1402_; uint8_t v___y_1403_; uint8_t v___y_1404_; lean_object* v___y_1405_; lean_object* v_a_1406_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; uint8_t v___y_1421_; uint8_t v___y_1422_; lean_object* v___y_1423_; lean_object* v_a_1424_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; uint8_t v___y_1432_; uint8_t v___y_1433_; lean_object* v___y_1434_; lean_object* v_a_1435_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; uint8_t v___y_1444_; uint8_t v___y_1445_; lean_object* v___y_1446_; uint8_t v___y_1447_; lean_object* v___y_1451_; lean_object* v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; uint8_t v___y_1456_; uint8_t v___y_1457_; lean_object* v___y_1458_; lean_object* v_a_1459_; lean_object* v___y_1463_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; uint8_t v___y_1468_; uint8_t v___y_1469_; lean_object* v___y_1470_; lean_object* v_a_1471_; lean_object* v_a_1474_; lean_object* v_a_1484_; 
if (lean_obj_tag(v_expr_1286_) == 5)
{
lean_object* v_fn_1498_; 
v_fn_1498_ = lean_ctor_get(v_expr_1286_, 0);
if (lean_obj_tag(v_fn_1498_) == 5)
{
lean_object* v_arg_1499_; lean_object* v_fn_1500_; lean_object* v_arg_1501_; lean_object* v___x_1502_; 
v_arg_1499_ = lean_ctor_get(v_expr_1286_, 1);
v_fn_1500_ = lean_ctor_get(v_fn_1498_, 0);
v_arg_1501_ = lean_ctor_get(v_fn_1498_, 1);
lean_inc(v_a_1290_);
lean_inc_ref(v_a_1289_);
lean_inc(v_a_1288_);
lean_inc_ref(v_a_1287_);
lean_inc_ref(v_fn_1500_);
v___x_1502_ = lean_infer_type(v_fn_1500_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_2354_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_1505_ = v___x_1502_;
v_isShared_1506_ = v_isSharedCheck_2354_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v___x_1502_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_2354_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
if (lean_obj_tag(v_a_1503_) == 7)
{
lean_object* v_body_1514_; 
v_body_1514_ = lean_ctor_get(v_a_1503_, 2);
lean_inc_ref(v_body_1514_);
if (lean_obj_tag(v_body_1514_) == 7)
{
lean_object* v_binderType_1515_; lean_object* v_binderType_1516_; lean_object* v_body_1517_; lean_object* v___y_1519_; uint8_t v___y_1520_; uint8_t v___y_1521_; uint8_t v___y_1560_; lean_object* v_a_1561_; lean_object* v___y_1565_; uint8_t v___y_1566_; uint8_t v___y_1567_; uint8_t v___y_1604_; lean_object* v_a_1605_; uint8_t v___y_1609_; lean_object* v___y_1610_; lean_object* v___y_1613_; lean_object* v___y_1614_; uint8_t v___y_1615_; lean_object* v___y_1616_; uint8_t v___y_1617_; lean_object* v___y_1635_; uint8_t v___y_1636_; lean_object* v___y_1637_; lean_object* v_a_1638_; lean_object* v___y_1642_; uint8_t v___y_1643_; lean_object* v___y_1644_; lean_object* v___y_1645_; lean_object* v___y_1648_; lean_object* v___y_1649_; lean_object* v___y_1650_; lean_object* v___y_1651_; lean_object* v___y_1652_; uint8_t v___y_1653_; uint8_t v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; uint8_t v___y_1657_; lean_object* v___y_1696_; lean_object* v___y_1697_; lean_object* v___y_1698_; lean_object* v___y_1699_; lean_object* v___y_1700_; uint8_t v___y_1701_; uint8_t v___y_1702_; lean_object* v___y_1703_; lean_object* v_a_1704_; lean_object* v___y_1708_; lean_object* v___y_1709_; lean_object* v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; uint8_t v___y_1714_; uint8_t v___y_1715_; lean_object* v___y_1716_; uint8_t v___y_1717_; lean_object* v___y_1754_; lean_object* v___y_1755_; lean_object* v___y_1756_; lean_object* v___y_1757_; lean_object* v___y_1758_; uint8_t v___y_1759_; uint8_t v___y_1760_; lean_object* v___y_1761_; lean_object* v_a_1762_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___y_1769_; lean_object* v___y_1770_; uint8_t v___y_1771_; uint8_t v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1778_; lean_object* v___y_1779_; lean_object* v___y_1780_; lean_object* v___y_1781_; lean_object* v___y_1782_; lean_object* v___y_1783_; lean_object* v___y_1784_; uint8_t v___y_1785_; uint8_t v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; uint8_t v___y_1789_; lean_object* v___y_1807_; lean_object* v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; uint8_t v___y_1813_; uint8_t v___y_1814_; lean_object* v___y_1815_; lean_object* v___y_1816_; lean_object* v_a_1817_; lean_object* v___y_1821_; lean_object* v___y_1822_; lean_object* v___y_1823_; lean_object* v___y_1824_; lean_object* v___y_1825_; lean_object* v___y_1826_; uint8_t v___y_1827_; uint8_t v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1835_; lean_object* v___y_1836_; lean_object* v___y_1837_; lean_object* v___y_1838_; uint8_t v___y_1839_; uint8_t v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; uint8_t v___y_1844_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; uint8_t v___y_1887_; uint8_t v___y_1888_; lean_object* v___y_1889_; lean_object* v___y_1890_; lean_object* v_a_1891_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; uint8_t v___y_1900_; uint8_t v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; uint8_t v___y_1904_; lean_object* v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; uint8_t v___y_1945_; uint8_t v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; lean_object* v_a_1949_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; uint8_t v___y_1957_; uint8_t v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; uint8_t v___y_1970_; uint8_t v___y_1971_; lean_object* v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; uint8_t v___y_1976_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; uint8_t v___y_1999_; uint8_t v___y_2000_; lean_object* v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v_a_2004_; lean_object* v___y_2008_; lean_object* v___y_2009_; lean_object* v___y_2010_; lean_object* v___y_2011_; lean_object* v___y_2012_; uint8_t v___y_2013_; uint8_t v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2022_; lean_object* v___y_2023_; lean_object* v___y_2024_; uint8_t v___y_2025_; uint8_t v___y_2026_; lean_object* v___y_2027_; lean_object* v___y_2109_; uint8_t v___y_2110_; uint8_t v___y_2111_; uint8_t v___y_2150_; lean_object* v_a_2151_; lean_object* v___y_2155_; uint8_t v___y_2156_; uint8_t v___y_2157_; uint8_t v___y_2194_; lean_object* v_a_2195_; uint8_t v___y_2199_; lean_object* v___y_2200_; lean_object* v___y_2203_; uint8_t v___y_2204_; lean_object* v___y_2205_; lean_object* v___y_2206_; uint8_t v___y_2207_; lean_object* v___y_2225_; uint8_t v___y_2226_; lean_object* v___y_2227_; lean_object* v_a_2228_; lean_object* v___y_2232_; uint8_t v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2235_; uint8_t v___y_2238_; uint8_t v___x_2352_; 
lean_del_object(v___x_1505_);
v_binderType_1515_ = lean_ctor_get(v_a_1503_, 1);
lean_inc_ref(v_binderType_1515_);
lean_dec_ref(v_a_1503_);
v_binderType_1516_ = lean_ctor_get(v_body_1514_, 1);
lean_inc_ref(v_binderType_1516_);
v_body_1517_ = lean_ctor_get(v_body_1514_, 2);
lean_inc_ref(v_body_1517_);
lean_dec_ref(v_body_1514_);
v___x_2352_ = l_Lean_Expr_hasLooseBVars(v_binderType_1516_);
if (v___x_2352_ == 0)
{
uint8_t v___x_2353_; 
v___x_2353_ = l_Lean_Expr_hasLooseBVars(v_body_1517_);
lean_dec_ref(v_body_1517_);
v___y_2238_ = v___x_2353_;
goto v___jp_2237_;
}
else
{
lean_dec_ref(v_body_1517_);
v___y_2238_ = v___x_2352_;
goto v___jp_2237_;
}
v___jp_1518_:
{
if (v___y_1521_ == 0)
{
lean_object* v___x_1522_; 
lean_dec_ref(v___y_1519_);
v___x_1522_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1501_);
if (lean_obj_tag(v___x_1522_) == 1)
{
lean_object* v_val_1523_; lean_object* v_snd_1524_; lean_object* v___x_1525_; 
v_val_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_val_1523_);
lean_dec_ref(v___x_1522_);
v_snd_1524_ = lean_ctor_get(v_val_1523_, 1);
lean_inc(v_snd_1524_);
lean_dec(v_val_1523_);
v___x_1525_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1499_, v_a_1290_);
if (lean_obj_tag(v___x_1525_) == 0)
{
lean_object* v_a_1526_; 
v_a_1526_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_a_1526_);
lean_dec_ref(v___x_1525_);
if (lean_obj_tag(v_a_1526_) == 1)
{
lean_object* v_val_1527_; lean_object* v___x_1528_; 
v_val_1527_ = lean_ctor_get(v_a_1526_, 0);
lean_inc(v_val_1527_);
lean_dec_ref(v_a_1526_);
lean_inc(v_a_1290_);
lean_inc_ref(v_a_1289_);
lean_inc(v_a_1288_);
lean_inc_ref(v_a_1287_);
v___x_1528_ = lean_infer_type(v_val_1527_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1530_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref(v___x_1528_);
v___x_1530_ = l_Lean_Meta_mkNumeral(v_a_1529_, v_snd_1524_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; lean_object* v___x_1532_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1531_);
lean_dec_ref(v___x_1530_);
v___x_1532_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1531_, v_binderType_1515_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1532_) == 0)
{
lean_object* v_a_1533_; lean_object* v___x_1534_; 
v_a_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1533_);
lean_dec_ref(v___x_1532_);
lean_inc_ref(v_arg_1501_);
v___x_1534_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1501_, v_a_1533_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref(v___x_1534_);
if (lean_obj_tag(v_a_1535_) == 1)
{
lean_object* v_val_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v_val_1536_ = lean_ctor_get(v_a_1535_, 0);
lean_inc(v_val_1536_);
lean_dec_ref(v_a_1535_);
v___x_1537_ = lean_box(0);
lean_inc_ref(v_fn_1500_);
v___x_1538_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1538_, 0, v_fn_1500_);
lean_ctor_set(v___x_1538_, 1, v___x_1537_);
lean_ctor_set_uint8(v___x_1538_, sizeof(void*)*2, v___y_1520_);
v___x_1539_ = l_Lean_Meta_Simp_mkCongr(v___x_1538_, v_val_1536_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1541_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1540_);
lean_dec_ref(v___x_1539_);
lean_inc_ref(v_arg_1499_);
v___x_1541_ = l_Lean_Meta_Simp_mkCongrFun(v_a_1540_, v_arg_1499_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_dec_ref(v_expr_1286_);
return v___x_1541_;
}
else
{
lean_object* v_a_1542_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1542_);
lean_dec_ref(v___x_1541_);
v___y_1314_ = v___y_1520_;
v_a_1315_ = v_a_1542_;
goto v___jp_1313_;
}
}
else
{
lean_object* v_a_1543_; 
v_a_1543_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1543_);
lean_dec_ref(v___x_1539_);
v___y_1314_ = v___y_1520_;
v_a_1315_ = v_a_1543_;
goto v___jp_1313_;
}
}
else
{
lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v_a_1546_; 
lean_dec(v_a_1535_);
v___x_1544_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1545_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1544_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref(v___x_1545_);
v___y_1314_ = v___y_1520_;
v_a_1315_ = v_a_1546_;
goto v___jp_1313_;
}
}
else
{
lean_object* v_a_1547_; 
v_a_1547_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1547_);
lean_dec_ref(v___x_1534_);
v___y_1314_ = v___y_1520_;
v_a_1315_ = v_a_1547_;
goto v___jp_1313_;
}
}
else
{
lean_object* v_a_1548_; 
v_a_1548_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_a_1548_);
lean_dec_ref(v___x_1532_);
v___y_1314_ = v___y_1520_;
v_a_1315_ = v_a_1548_;
goto v___jp_1313_;
}
}
else
{
lean_object* v_a_1549_; 
lean_dec_ref(v_binderType_1515_);
v_a_1549_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1549_);
lean_dec_ref(v___x_1530_);
v___y_1314_ = v___y_1520_;
v_a_1315_ = v_a_1549_;
goto v___jp_1313_;
}
}
else
{
lean_object* v_a_1550_; 
lean_dec(v_snd_1524_);
lean_dec_ref(v_binderType_1515_);
v_a_1550_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1550_);
lean_dec_ref(v___x_1528_);
v___y_1314_ = v___y_1520_;
v_a_1315_ = v_a_1550_;
goto v___jp_1313_;
}
}
else
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v_a_1553_; 
lean_dec(v_a_1526_);
lean_dec(v_snd_1524_);
lean_dec_ref(v_binderType_1515_);
v___x_1551_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1552_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1551_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref(v___x_1552_);
v___y_1314_ = v___y_1520_;
v_a_1315_ = v_a_1553_;
goto v___jp_1313_;
}
}
else
{
lean_object* v_a_1554_; 
lean_dec(v_snd_1524_);
lean_dec_ref(v_binderType_1515_);
v_a_1554_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_a_1554_);
lean_dec_ref(v___x_1525_);
v___y_1314_ = v___y_1520_;
v_a_1315_ = v_a_1554_;
goto v___jp_1313_;
}
}
else
{
lean_object* v___x_1555_; 
lean_dec_ref(v_binderType_1515_);
v___x_1555_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1522_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
lean_dec(v___x_1522_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; 
lean_dec_ref(v_expr_1286_);
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1556_);
lean_dec_ref(v___x_1555_);
v_a_1484_ = v_a_1556_;
goto v___jp_1483_;
}
else
{
lean_object* v_a_1557_; 
v_a_1557_ = lean_ctor_get(v___x_1555_, 0);
lean_inc(v_a_1557_);
lean_dec_ref(v___x_1555_);
v___y_1314_ = v___y_1520_;
v_a_1315_ = v_a_1557_;
goto v___jp_1313_;
}
}
}
else
{
lean_object* v___x_1558_; 
lean_dec_ref(v_binderType_1515_);
lean_dec_ref(v_expr_1286_);
v___x_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1558_, 0, v___y_1519_);
return v___x_1558_;
}
}
v___jp_1559_:
{
uint8_t v___x_1562_; 
v___x_1562_ = l_Lean_Exception_isInterrupt(v_a_1561_);
if (v___x_1562_ == 0)
{
uint8_t v___x_1563_; 
lean_inc_ref(v_a_1561_);
v___x_1563_ = l_Lean_Exception_isRuntime(v_a_1561_);
v___y_1519_ = v_a_1561_;
v___y_1520_ = v___y_1560_;
v___y_1521_ = v___x_1563_;
goto v___jp_1518_;
}
else
{
v___y_1519_ = v_a_1561_;
v___y_1520_ = v___y_1560_;
v___y_1521_ = v___x_1562_;
goto v___jp_1518_;
}
}
v___jp_1564_:
{
if (v___y_1567_ == 0)
{
lean_object* v___x_1568_; 
lean_dec_ref(v___y_1565_);
v___x_1568_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1499_);
if (lean_obj_tag(v___x_1568_) == 1)
{
lean_object* v_val_1569_; lean_object* v_snd_1570_; lean_object* v___x_1571_; 
v_val_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_val_1569_);
lean_dec_ref(v___x_1568_);
v_snd_1570_ = lean_ctor_get(v_val_1569_, 1);
lean_inc(v_snd_1570_);
lean_dec(v_val_1569_);
v___x_1571_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1501_, v_a_1290_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1572_);
lean_dec_ref(v___x_1571_);
if (lean_obj_tag(v_a_1572_) == 1)
{
lean_object* v_val_1573_; lean_object* v___x_1574_; 
v_val_1573_ = lean_ctor_get(v_a_1572_, 0);
lean_inc(v_val_1573_);
lean_dec_ref(v_a_1572_);
lean_inc(v_a_1290_);
lean_inc_ref(v_a_1289_);
lean_inc(v_a_1288_);
lean_inc_ref(v_a_1287_);
v___x_1574_ = lean_infer_type(v_val_1573_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; lean_object* v___x_1576_; 
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1575_);
lean_dec_ref(v___x_1574_);
v___x_1576_ = l_Lean_Meta_mkNumeral(v_a_1575_, v_snd_1570_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1578_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1577_);
lean_dec_ref(v___x_1576_);
lean_inc_ref(v_binderType_1515_);
v___x_1578_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1577_, v_binderType_1515_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1578_) == 0)
{
lean_object* v_a_1579_; lean_object* v___x_1580_; 
v_a_1579_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref(v___x_1578_);
lean_inc_ref(v_arg_1499_);
v___x_1580_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1499_, v_a_1579_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1580_) == 0)
{
lean_object* v_a_1581_; 
v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1581_);
lean_dec_ref(v___x_1580_);
if (lean_obj_tag(v_a_1581_) == 1)
{
lean_object* v_val_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v_val_1582_ = lean_ctor_get(v_a_1581_, 0);
lean_inc(v_val_1582_);
lean_dec_ref(v_a_1581_);
lean_inc_ref(v_arg_1501_);
lean_inc_ref(v_fn_1500_);
v___x_1583_ = l_Lean_Expr_app___override(v_fn_1500_, v_arg_1501_);
v___x_1584_ = lean_box(0);
v___x_1585_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1585_, 0, v___x_1583_);
lean_ctor_set(v___x_1585_, 1, v___x_1584_);
lean_ctor_set_uint8(v___x_1585_, sizeof(void*)*2, v___y_1566_);
v___x_1586_ = l_Lean_Meta_Simp_mkCongr(v___x_1585_, v_val_1582_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_dec_ref(v_binderType_1515_);
lean_dec_ref(v_expr_1286_);
return v___x_1586_;
}
else
{
lean_object* v_a_1587_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref(v___x_1586_);
v___y_1560_ = v___y_1566_;
v_a_1561_ = v_a_1587_;
goto v___jp_1559_;
}
}
else
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v_a_1590_; 
lean_dec(v_a_1581_);
v___x_1588_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1589_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1588_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1590_);
lean_dec_ref(v___x_1589_);
v___y_1560_ = v___y_1566_;
v_a_1561_ = v_a_1590_;
goto v___jp_1559_;
}
}
else
{
lean_object* v_a_1591_; 
v_a_1591_ = lean_ctor_get(v___x_1580_, 0);
lean_inc(v_a_1591_);
lean_dec_ref(v___x_1580_);
v___y_1560_ = v___y_1566_;
v_a_1561_ = v_a_1591_;
goto v___jp_1559_;
}
}
else
{
lean_object* v_a_1592_; 
v_a_1592_ = lean_ctor_get(v___x_1578_, 0);
lean_inc(v_a_1592_);
lean_dec_ref(v___x_1578_);
v___y_1560_ = v___y_1566_;
v_a_1561_ = v_a_1592_;
goto v___jp_1559_;
}
}
else
{
lean_object* v_a_1593_; 
v_a_1593_ = lean_ctor_get(v___x_1576_, 0);
lean_inc(v_a_1593_);
lean_dec_ref(v___x_1576_);
v___y_1560_ = v___y_1566_;
v_a_1561_ = v_a_1593_;
goto v___jp_1559_;
}
}
else
{
lean_object* v_a_1594_; 
lean_dec(v_snd_1570_);
v_a_1594_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1594_);
lean_dec_ref(v___x_1574_);
v___y_1560_ = v___y_1566_;
v_a_1561_ = v_a_1594_;
goto v___jp_1559_;
}
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v_a_1597_; 
lean_dec(v_a_1572_);
lean_dec(v_snd_1570_);
v___x_1595_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1596_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1595_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_a_1597_);
lean_dec_ref(v___x_1596_);
v___y_1560_ = v___y_1566_;
v_a_1561_ = v_a_1597_;
goto v___jp_1559_;
}
}
else
{
lean_object* v_a_1598_; 
lean_dec(v_snd_1570_);
v_a_1598_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1598_);
lean_dec_ref(v___x_1571_);
v___y_1560_ = v___y_1566_;
v_a_1561_ = v_a_1598_;
goto v___jp_1559_;
}
}
else
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1568_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
lean_dec(v___x_1568_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; 
lean_dec_ref(v_binderType_1515_);
lean_dec_ref(v_expr_1286_);
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1600_);
lean_dec_ref(v___x_1599_);
v_a_1484_ = v_a_1600_;
goto v___jp_1483_;
}
else
{
lean_object* v_a_1601_; 
v_a_1601_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1601_);
lean_dec_ref(v___x_1599_);
v___y_1560_ = v___y_1566_;
v_a_1561_ = v_a_1601_;
goto v___jp_1559_;
}
}
}
else
{
lean_object* v___x_1602_; 
lean_dec_ref(v_binderType_1515_);
lean_dec_ref(v_expr_1286_);
v___x_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1602_, 0, v___y_1565_);
return v___x_1602_;
}
}
v___jp_1603_:
{
uint8_t v___x_1606_; 
v___x_1606_ = l_Lean_Exception_isInterrupt(v_a_1605_);
if (v___x_1606_ == 0)
{
uint8_t v___x_1607_; 
lean_inc_ref(v_a_1605_);
v___x_1607_ = l_Lean_Exception_isRuntime(v_a_1605_);
v___y_1565_ = v_a_1605_;
v___y_1566_ = v___y_1604_;
v___y_1567_ = v___x_1607_;
goto v___jp_1564_;
}
else
{
v___y_1565_ = v_a_1605_;
v___y_1566_ = v___y_1604_;
v___y_1567_ = v___x_1606_;
goto v___jp_1564_;
}
}
v___jp_1608_:
{
if (lean_obj_tag(v___y_1610_) == 0)
{
lean_dec_ref(v_binderType_1515_);
lean_dec_ref(v_expr_1286_);
return v___y_1610_;
}
else
{
lean_object* v_a_1611_; 
v_a_1611_ = lean_ctor_get(v___y_1610_, 0);
lean_inc(v_a_1611_);
lean_dec_ref(v___y_1610_);
v___y_1604_ = v___y_1609_;
v_a_1605_ = v_a_1611_;
goto v___jp_1603_;
}
}
v___jp_1612_:
{
if (v___y_1617_ == 0)
{
lean_object* v___x_1618_; 
lean_dec_ref(v___y_1613_);
v___x_1618_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v___y_1614_, v___y_1616_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1620_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1619_);
lean_dec_ref(v___x_1618_);
lean_inc_ref(v_binderType_1515_);
v___x_1620_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1619_, v_binderType_1515_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v___x_1622_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1621_);
lean_dec_ref(v___x_1620_);
lean_inc_ref(v_arg_1499_);
v___x_1622_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1499_, v_a_1621_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1623_);
lean_dec_ref(v___x_1622_);
if (lean_obj_tag(v_a_1623_) == 1)
{
lean_object* v_val_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v_val_1624_ = lean_ctor_get(v_a_1623_, 0);
lean_inc(v_val_1624_);
lean_dec_ref(v_a_1623_);
lean_inc_ref(v_arg_1501_);
lean_inc_ref(v_fn_1500_);
v___x_1625_ = l_Lean_Expr_app___override(v_fn_1500_, v_arg_1501_);
v___x_1626_ = lean_box(0);
v___x_1627_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1627_, 0, v___x_1625_);
lean_ctor_set(v___x_1627_, 1, v___x_1626_);
lean_ctor_set_uint8(v___x_1627_, sizeof(void*)*2, v___y_1615_);
v___x_1628_ = l_Lean_Meta_Simp_mkCongr(v___x_1627_, v_val_1624_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v___y_1609_ = v___y_1615_;
v___y_1610_ = v___x_1628_;
goto v___jp_1608_;
}
else
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
lean_dec(v_a_1623_);
v___x_1629_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1630_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1629_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v___y_1609_ = v___y_1615_;
v___y_1610_ = v___x_1630_;
goto v___jp_1608_;
}
}
else
{
lean_object* v_a_1631_; 
v_a_1631_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1631_);
lean_dec_ref(v___x_1622_);
v___y_1604_ = v___y_1615_;
v_a_1605_ = v_a_1631_;
goto v___jp_1603_;
}
}
else
{
lean_object* v_a_1632_; 
v_a_1632_ = lean_ctor_get(v___x_1620_, 0);
lean_inc(v_a_1632_);
lean_dec_ref(v___x_1620_);
v___y_1604_ = v___y_1615_;
v_a_1605_ = v_a_1632_;
goto v___jp_1603_;
}
}
else
{
lean_object* v_a_1633_; 
v_a_1633_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1633_);
lean_dec_ref(v___x_1618_);
v___y_1604_ = v___y_1615_;
v_a_1605_ = v_a_1633_;
goto v___jp_1603_;
}
}
else
{
lean_dec_ref(v___y_1616_);
lean_dec_ref(v___y_1614_);
v___y_1604_ = v___y_1615_;
v_a_1605_ = v___y_1613_;
goto v___jp_1603_;
}
}
v___jp_1634_:
{
uint8_t v___x_1639_; 
v___x_1639_ = l_Lean_Exception_isInterrupt(v_a_1638_);
if (v___x_1639_ == 0)
{
uint8_t v___x_1640_; 
lean_inc_ref(v_a_1638_);
v___x_1640_ = l_Lean_Exception_isRuntime(v_a_1638_);
v___y_1613_ = v_a_1638_;
v___y_1614_ = v___y_1635_;
v___y_1615_ = v___y_1636_;
v___y_1616_ = v___y_1637_;
v___y_1617_ = v___x_1640_;
goto v___jp_1612_;
}
else
{
v___y_1613_ = v_a_1638_;
v___y_1614_ = v___y_1635_;
v___y_1615_ = v___y_1636_;
v___y_1616_ = v___y_1637_;
v___y_1617_ = v___x_1639_;
goto v___jp_1612_;
}
}
v___jp_1641_:
{
if (lean_obj_tag(v___y_1645_) == 0)
{
lean_dec_ref(v___y_1644_);
lean_dec_ref(v___y_1642_);
lean_dec_ref(v_binderType_1515_);
lean_dec_ref(v_expr_1286_);
return v___y_1645_;
}
else
{
lean_object* v_a_1646_; 
v_a_1646_ = lean_ctor_get(v___y_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref(v___y_1645_);
v___y_1635_ = v___y_1642_;
v___y_1636_ = v___y_1643_;
v___y_1637_ = v___y_1644_;
v_a_1638_ = v_a_1646_;
goto v___jp_1634_;
}
}
v___jp_1647_:
{
if (v___y_1657_ == 0)
{
lean_object* v___x_1658_; 
lean_dec_ref(v___y_1655_);
v___x_1658_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1501_);
if (lean_obj_tag(v___x_1658_) == 1)
{
lean_object* v_val_1659_; lean_object* v_snd_1660_; lean_object* v___x_1661_; 
v_val_1659_ = lean_ctor_get(v___x_1658_, 0);
lean_inc(v_val_1659_);
lean_dec_ref(v___x_1658_);
v_snd_1660_ = lean_ctor_get(v_val_1659_, 1);
lean_inc(v_snd_1660_);
lean_dec(v_val_1659_);
v___x_1661_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1499_, v_a_1290_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref(v___x_1661_);
if (lean_obj_tag(v_a_1662_) == 1)
{
lean_object* v_val_1663_; lean_object* v___x_1664_; 
v_val_1663_ = lean_ctor_get(v_a_1662_, 0);
lean_inc(v_val_1663_);
lean_dec_ref(v_a_1662_);
lean_inc(v_a_1290_);
lean_inc_ref(v_a_1289_);
lean_inc(v_a_1288_);
lean_inc_ref(v_a_1287_);
v___x_1664_ = lean_infer_type(v_val_1663_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; lean_object* v___x_1666_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_a_1665_);
lean_dec_ref(v___x_1664_);
v___x_1666_ = l_Lean_Meta_mkNumeral(v_a_1665_, v_snd_1660_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v___x_1668_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1667_);
lean_dec_ref(v___x_1666_);
v___x_1668_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1667_, v_binderType_1515_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; lean_object* v___x_1670_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1669_);
lean_dec_ref(v___x_1668_);
lean_inc_ref(v_arg_1501_);
v___x_1670_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1501_, v_a_1669_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1670_) == 0)
{
lean_object* v_a_1671_; 
v_a_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1671_);
lean_dec_ref(v___x_1670_);
if (lean_obj_tag(v_a_1671_) == 1)
{
lean_object* v_val_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v_val_1672_ = lean_ctor_get(v_a_1671_, 0);
lean_inc(v_val_1672_);
lean_dec_ref(v_a_1671_);
v___x_1673_ = lean_box(0);
lean_inc_ref(v_fn_1500_);
v___x_1674_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1674_, 0, v_fn_1500_);
lean_ctor_set(v___x_1674_, 1, v___x_1673_);
lean_ctor_set_uint8(v___x_1674_, sizeof(void*)*2, v___y_1654_);
v___x_1675_ = l_Lean_Meta_Simp_mkCongr(v___x_1674_, v_val_1672_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v___x_1677_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1676_);
lean_dec_ref(v___x_1675_);
lean_inc_ref(v_arg_1499_);
v___x_1677_ = l_Lean_Meta_Simp_mkCongrFun(v_a_1676_, v_arg_1499_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; 
lean_dec_ref(v_expr_1286_);
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_a_1678_);
lean_dec_ref(v___x_1677_);
v___y_1427_ = v___y_1648_;
v___y_1428_ = v___y_1649_;
v___y_1429_ = v___y_1650_;
v___y_1430_ = v___y_1651_;
v___y_1431_ = v___y_1652_;
v___y_1432_ = v___y_1654_;
v___y_1433_ = v___y_1653_;
v___y_1434_ = v___y_1656_;
v_a_1435_ = v_a_1678_;
goto v___jp_1426_;
}
else
{
lean_object* v_a_1679_; 
v_a_1679_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_a_1679_);
lean_dec_ref(v___x_1677_);
v___y_1451_ = v___y_1648_;
v___y_1452_ = v___y_1649_;
v___y_1453_ = v___y_1650_;
v___y_1454_ = v___y_1651_;
v___y_1455_ = v___y_1652_;
v___y_1456_ = v___y_1654_;
v___y_1457_ = v___y_1653_;
v___y_1458_ = v___y_1656_;
v_a_1459_ = v_a_1679_;
goto v___jp_1450_;
}
}
else
{
lean_object* v_a_1680_; 
v_a_1680_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1680_);
lean_dec_ref(v___x_1675_);
v___y_1451_ = v___y_1648_;
v___y_1452_ = v___y_1649_;
v___y_1453_ = v___y_1650_;
v___y_1454_ = v___y_1651_;
v___y_1455_ = v___y_1652_;
v___y_1456_ = v___y_1654_;
v___y_1457_ = v___y_1653_;
v___y_1458_ = v___y_1656_;
v_a_1459_ = v_a_1680_;
goto v___jp_1450_;
}
}
else
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v_a_1683_; 
lean_dec(v_a_1671_);
v___x_1681_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1682_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1681_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
lean_inc(v_a_1683_);
lean_dec_ref(v___x_1682_);
v___y_1451_ = v___y_1648_;
v___y_1452_ = v___y_1649_;
v___y_1453_ = v___y_1650_;
v___y_1454_ = v___y_1651_;
v___y_1455_ = v___y_1652_;
v___y_1456_ = v___y_1654_;
v___y_1457_ = v___y_1653_;
v___y_1458_ = v___y_1656_;
v_a_1459_ = v_a_1683_;
goto v___jp_1450_;
}
}
else
{
lean_object* v_a_1684_; 
v_a_1684_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_a_1684_);
lean_dec_ref(v___x_1670_);
v___y_1451_ = v___y_1648_;
v___y_1452_ = v___y_1649_;
v___y_1453_ = v___y_1650_;
v___y_1454_ = v___y_1651_;
v___y_1455_ = v___y_1652_;
v___y_1456_ = v___y_1654_;
v___y_1457_ = v___y_1653_;
v___y_1458_ = v___y_1656_;
v_a_1459_ = v_a_1684_;
goto v___jp_1450_;
}
}
else
{
lean_object* v_a_1685_; 
v_a_1685_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1685_);
lean_dec_ref(v___x_1668_);
v___y_1451_ = v___y_1648_;
v___y_1452_ = v___y_1649_;
v___y_1453_ = v___y_1650_;
v___y_1454_ = v___y_1651_;
v___y_1455_ = v___y_1652_;
v___y_1456_ = v___y_1654_;
v___y_1457_ = v___y_1653_;
v___y_1458_ = v___y_1656_;
v_a_1459_ = v_a_1685_;
goto v___jp_1450_;
}
}
else
{
lean_object* v_a_1686_; 
lean_dec_ref(v_binderType_1515_);
v_a_1686_ = lean_ctor_get(v___x_1666_, 0);
lean_inc(v_a_1686_);
lean_dec_ref(v___x_1666_);
v___y_1451_ = v___y_1648_;
v___y_1452_ = v___y_1649_;
v___y_1453_ = v___y_1650_;
v___y_1454_ = v___y_1651_;
v___y_1455_ = v___y_1652_;
v___y_1456_ = v___y_1654_;
v___y_1457_ = v___y_1653_;
v___y_1458_ = v___y_1656_;
v_a_1459_ = v_a_1686_;
goto v___jp_1450_;
}
}
else
{
lean_object* v_a_1687_; 
lean_dec(v_snd_1660_);
lean_dec_ref(v_binderType_1515_);
v_a_1687_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_a_1687_);
lean_dec_ref(v___x_1664_);
v___y_1451_ = v___y_1648_;
v___y_1452_ = v___y_1649_;
v___y_1453_ = v___y_1650_;
v___y_1454_ = v___y_1651_;
v___y_1455_ = v___y_1652_;
v___y_1456_ = v___y_1654_;
v___y_1457_ = v___y_1653_;
v___y_1458_ = v___y_1656_;
v_a_1459_ = v_a_1687_;
goto v___jp_1450_;
}
}
else
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v_a_1690_; 
lean_dec(v_a_1662_);
lean_dec(v_snd_1660_);
lean_dec_ref(v_binderType_1515_);
v___x_1688_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1689_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1688_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1690_);
lean_dec_ref(v___x_1689_);
v___y_1451_ = v___y_1648_;
v___y_1452_ = v___y_1649_;
v___y_1453_ = v___y_1650_;
v___y_1454_ = v___y_1651_;
v___y_1455_ = v___y_1652_;
v___y_1456_ = v___y_1654_;
v___y_1457_ = v___y_1653_;
v___y_1458_ = v___y_1656_;
v_a_1459_ = v_a_1690_;
goto v___jp_1450_;
}
}
else
{
lean_object* v_a_1691_; 
lean_dec(v_snd_1660_);
lean_dec_ref(v_binderType_1515_);
v_a_1691_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1691_);
lean_dec_ref(v___x_1661_);
v___y_1451_ = v___y_1648_;
v___y_1452_ = v___y_1649_;
v___y_1453_ = v___y_1650_;
v___y_1454_ = v___y_1651_;
v___y_1455_ = v___y_1652_;
v___y_1456_ = v___y_1654_;
v___y_1457_ = v___y_1653_;
v___y_1458_ = v___y_1656_;
v_a_1459_ = v_a_1691_;
goto v___jp_1450_;
}
}
else
{
lean_object* v___x_1692_; 
lean_dec_ref(v_binderType_1515_);
v___x_1692_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1658_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
lean_dec(v___x_1658_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; 
lean_dec_ref(v_expr_1286_);
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1693_);
lean_dec_ref(v___x_1692_);
v___y_1463_ = v___y_1648_;
v___y_1464_ = v___y_1649_;
v___y_1465_ = v___y_1650_;
v___y_1466_ = v___y_1651_;
v___y_1467_ = v___y_1652_;
v___y_1468_ = v___y_1653_;
v___y_1469_ = v___y_1654_;
v___y_1470_ = v___y_1656_;
v_a_1471_ = v_a_1693_;
goto v___jp_1462_;
}
else
{
lean_object* v_a_1694_; 
v_a_1694_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1694_);
lean_dec_ref(v___x_1692_);
v___y_1451_ = v___y_1648_;
v___y_1452_ = v___y_1649_;
v___y_1453_ = v___y_1650_;
v___y_1454_ = v___y_1651_;
v___y_1455_ = v___y_1652_;
v___y_1456_ = v___y_1654_;
v___y_1457_ = v___y_1653_;
v___y_1458_ = v___y_1656_;
v_a_1459_ = v_a_1694_;
goto v___jp_1450_;
}
}
}
else
{
lean_dec_ref(v_binderType_1515_);
lean_dec_ref(v_expr_1286_);
v___y_1416_ = v___y_1648_;
v___y_1417_ = v___y_1649_;
v___y_1418_ = v___y_1650_;
v___y_1419_ = v___y_1651_;
v___y_1420_ = v___y_1652_;
v___y_1421_ = v___y_1654_;
v___y_1422_ = v___y_1653_;
v___y_1423_ = v___y_1656_;
v_a_1424_ = v___y_1655_;
goto v___jp_1415_;
}
}
v___jp_1695_:
{
uint8_t v___x_1705_; 
v___x_1705_ = l_Lean_Exception_isInterrupt(v_a_1704_);
if (v___x_1705_ == 0)
{
uint8_t v___x_1706_; 
lean_inc_ref(v_a_1704_);
v___x_1706_ = l_Lean_Exception_isRuntime(v_a_1704_);
v___y_1648_ = v___y_1696_;
v___y_1649_ = v___y_1697_;
v___y_1650_ = v___y_1698_;
v___y_1651_ = v___y_1699_;
v___y_1652_ = v___y_1700_;
v___y_1653_ = v___y_1702_;
v___y_1654_ = v___y_1701_;
v___y_1655_ = v_a_1704_;
v___y_1656_ = v___y_1703_;
v___y_1657_ = v___x_1706_;
goto v___jp_1647_;
}
else
{
v___y_1648_ = v___y_1696_;
v___y_1649_ = v___y_1697_;
v___y_1650_ = v___y_1698_;
v___y_1651_ = v___y_1699_;
v___y_1652_ = v___y_1700_;
v___y_1653_ = v___y_1702_;
v___y_1654_ = v___y_1701_;
v___y_1655_ = v_a_1704_;
v___y_1656_ = v___y_1703_;
v___y_1657_ = v___x_1705_;
goto v___jp_1647_;
}
}
v___jp_1707_:
{
if (v___y_1717_ == 0)
{
lean_object* v___x_1718_; 
lean_dec_ref(v___y_1712_);
v___x_1718_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1499_);
if (lean_obj_tag(v___x_1718_) == 1)
{
lean_object* v_val_1719_; lean_object* v_snd_1720_; lean_object* v___x_1721_; 
v_val_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_val_1719_);
lean_dec_ref(v___x_1718_);
v_snd_1720_ = lean_ctor_get(v_val_1719_, 1);
lean_inc(v_snd_1720_);
lean_dec(v_val_1719_);
v___x_1721_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1501_, v_a_1290_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1722_);
lean_dec_ref(v___x_1721_);
if (lean_obj_tag(v_a_1722_) == 1)
{
lean_object* v_val_1723_; lean_object* v___x_1724_; 
v_val_1723_ = lean_ctor_get(v_a_1722_, 0);
lean_inc(v_val_1723_);
lean_dec_ref(v_a_1722_);
lean_inc(v_a_1290_);
lean_inc_ref(v_a_1289_);
lean_inc(v_a_1288_);
lean_inc_ref(v_a_1287_);
v___x_1724_ = lean_infer_type(v_val_1723_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; lean_object* v___x_1726_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref(v___x_1724_);
v___x_1726_ = l_Lean_Meta_mkNumeral(v_a_1725_, v_snd_1720_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1726_) == 0)
{
lean_object* v_a_1727_; lean_object* v___x_1728_; 
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1727_);
lean_dec_ref(v___x_1726_);
lean_inc_ref(v_binderType_1515_);
v___x_1728_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1727_, v_binderType_1515_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v___x_1730_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1729_);
lean_dec_ref(v___x_1728_);
lean_inc_ref(v_arg_1499_);
v___x_1730_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1499_, v_a_1729_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1730_) == 0)
{
lean_object* v_a_1731_; 
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_a_1731_);
lean_dec_ref(v___x_1730_);
if (lean_obj_tag(v_a_1731_) == 1)
{
lean_object* v_val_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v_val_1732_ = lean_ctor_get(v_a_1731_, 0);
lean_inc(v_val_1732_);
lean_dec_ref(v_a_1731_);
lean_inc_ref(v_arg_1501_);
lean_inc_ref(v_fn_1500_);
v___x_1733_ = l_Lean_Expr_app___override(v_fn_1500_, v_arg_1501_);
v___x_1734_ = lean_box(0);
v___x_1735_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1735_, 0, v___x_1733_);
lean_ctor_set(v___x_1735_, 1, v___x_1734_);
lean_ctor_set_uint8(v___x_1735_, sizeof(void*)*2, v___y_1715_);
v___x_1736_ = l_Lean_Meta_Simp_mkCongr(v___x_1735_, v_val_1732_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; 
lean_dec_ref(v_binderType_1515_);
lean_dec_ref(v_expr_1286_);
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_a_1737_);
lean_dec_ref(v___x_1736_);
v___y_1427_ = v___y_1708_;
v___y_1428_ = v___y_1709_;
v___y_1429_ = v___y_1710_;
v___y_1430_ = v___y_1711_;
v___y_1431_ = v___y_1713_;
v___y_1432_ = v___y_1715_;
v___y_1433_ = v___y_1714_;
v___y_1434_ = v___y_1716_;
v_a_1435_ = v_a_1737_;
goto v___jp_1426_;
}
else
{
lean_object* v_a_1738_; 
v_a_1738_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_a_1738_);
lean_dec_ref(v___x_1736_);
v___y_1696_ = v___y_1708_;
v___y_1697_ = v___y_1709_;
v___y_1698_ = v___y_1710_;
v___y_1699_ = v___y_1711_;
v___y_1700_ = v___y_1713_;
v___y_1701_ = v___y_1715_;
v___y_1702_ = v___y_1714_;
v___y_1703_ = v___y_1716_;
v_a_1704_ = v_a_1738_;
goto v___jp_1695_;
}
}
else
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v_a_1741_; 
lean_dec(v_a_1731_);
v___x_1739_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1740_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1739_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
lean_dec_ref(v___x_1740_);
v___y_1696_ = v___y_1708_;
v___y_1697_ = v___y_1709_;
v___y_1698_ = v___y_1710_;
v___y_1699_ = v___y_1711_;
v___y_1700_ = v___y_1713_;
v___y_1701_ = v___y_1715_;
v___y_1702_ = v___y_1714_;
v___y_1703_ = v___y_1716_;
v_a_1704_ = v_a_1741_;
goto v___jp_1695_;
}
}
else
{
lean_object* v_a_1742_; 
v_a_1742_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_a_1742_);
lean_dec_ref(v___x_1730_);
v___y_1696_ = v___y_1708_;
v___y_1697_ = v___y_1709_;
v___y_1698_ = v___y_1710_;
v___y_1699_ = v___y_1711_;
v___y_1700_ = v___y_1713_;
v___y_1701_ = v___y_1715_;
v___y_1702_ = v___y_1714_;
v___y_1703_ = v___y_1716_;
v_a_1704_ = v_a_1742_;
goto v___jp_1695_;
}
}
else
{
lean_object* v_a_1743_; 
v_a_1743_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1743_);
lean_dec_ref(v___x_1728_);
v___y_1696_ = v___y_1708_;
v___y_1697_ = v___y_1709_;
v___y_1698_ = v___y_1710_;
v___y_1699_ = v___y_1711_;
v___y_1700_ = v___y_1713_;
v___y_1701_ = v___y_1715_;
v___y_1702_ = v___y_1714_;
v___y_1703_ = v___y_1716_;
v_a_1704_ = v_a_1743_;
goto v___jp_1695_;
}
}
else
{
lean_object* v_a_1744_; 
v_a_1744_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1744_);
lean_dec_ref(v___x_1726_);
v___y_1696_ = v___y_1708_;
v___y_1697_ = v___y_1709_;
v___y_1698_ = v___y_1710_;
v___y_1699_ = v___y_1711_;
v___y_1700_ = v___y_1713_;
v___y_1701_ = v___y_1715_;
v___y_1702_ = v___y_1714_;
v___y_1703_ = v___y_1716_;
v_a_1704_ = v_a_1744_;
goto v___jp_1695_;
}
}
else
{
lean_object* v_a_1745_; 
lean_dec(v_snd_1720_);
v_a_1745_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1745_);
lean_dec_ref(v___x_1724_);
v___y_1696_ = v___y_1708_;
v___y_1697_ = v___y_1709_;
v___y_1698_ = v___y_1710_;
v___y_1699_ = v___y_1711_;
v___y_1700_ = v___y_1713_;
v___y_1701_ = v___y_1715_;
v___y_1702_ = v___y_1714_;
v___y_1703_ = v___y_1716_;
v_a_1704_ = v_a_1745_;
goto v___jp_1695_;
}
}
else
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v_a_1748_; 
lean_dec(v_a_1722_);
lean_dec(v_snd_1720_);
v___x_1746_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1747_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1746_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_a_1748_);
lean_dec_ref(v___x_1747_);
v___y_1696_ = v___y_1708_;
v___y_1697_ = v___y_1709_;
v___y_1698_ = v___y_1710_;
v___y_1699_ = v___y_1711_;
v___y_1700_ = v___y_1713_;
v___y_1701_ = v___y_1715_;
v___y_1702_ = v___y_1714_;
v___y_1703_ = v___y_1716_;
v_a_1704_ = v_a_1748_;
goto v___jp_1695_;
}
}
else
{
lean_object* v_a_1749_; 
lean_dec(v_snd_1720_);
v_a_1749_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1749_);
lean_dec_ref(v___x_1721_);
v___y_1696_ = v___y_1708_;
v___y_1697_ = v___y_1709_;
v___y_1698_ = v___y_1710_;
v___y_1699_ = v___y_1711_;
v___y_1700_ = v___y_1713_;
v___y_1701_ = v___y_1715_;
v___y_1702_ = v___y_1714_;
v___y_1703_ = v___y_1716_;
v_a_1704_ = v_a_1749_;
goto v___jp_1695_;
}
}
else
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1718_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
lean_dec(v___x_1718_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; 
lean_dec_ref(v_binderType_1515_);
lean_dec_ref(v_expr_1286_);
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref(v___x_1750_);
v___y_1463_ = v___y_1708_;
v___y_1464_ = v___y_1709_;
v___y_1465_ = v___y_1710_;
v___y_1466_ = v___y_1711_;
v___y_1467_ = v___y_1713_;
v___y_1468_ = v___y_1714_;
v___y_1469_ = v___y_1715_;
v___y_1470_ = v___y_1716_;
v_a_1471_ = v_a_1751_;
goto v___jp_1462_;
}
else
{
lean_object* v_a_1752_; 
v_a_1752_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1752_);
lean_dec_ref(v___x_1750_);
v___y_1696_ = v___y_1708_;
v___y_1697_ = v___y_1709_;
v___y_1698_ = v___y_1710_;
v___y_1699_ = v___y_1711_;
v___y_1700_ = v___y_1713_;
v___y_1701_ = v___y_1715_;
v___y_1702_ = v___y_1714_;
v___y_1703_ = v___y_1716_;
v_a_1704_ = v_a_1752_;
goto v___jp_1695_;
}
}
}
else
{
lean_dec_ref(v_binderType_1515_);
lean_dec_ref(v_expr_1286_);
v___y_1416_ = v___y_1708_;
v___y_1417_ = v___y_1709_;
v___y_1418_ = v___y_1710_;
v___y_1419_ = v___y_1711_;
v___y_1420_ = v___y_1713_;
v___y_1421_ = v___y_1715_;
v___y_1422_ = v___y_1714_;
v___y_1423_ = v___y_1716_;
v_a_1424_ = v___y_1712_;
goto v___jp_1415_;
}
}
v___jp_1753_:
{
uint8_t v___x_1763_; 
v___x_1763_ = l_Lean_Exception_isInterrupt(v_a_1762_);
if (v___x_1763_ == 0)
{
uint8_t v___x_1764_; 
lean_inc_ref(v_a_1762_);
v___x_1764_ = l_Lean_Exception_isRuntime(v_a_1762_);
v___y_1708_ = v___y_1754_;
v___y_1709_ = v___y_1755_;
v___y_1710_ = v___y_1756_;
v___y_1711_ = v___y_1757_;
v___y_1712_ = v_a_1762_;
v___y_1713_ = v___y_1758_;
v___y_1714_ = v___y_1760_;
v___y_1715_ = v___y_1759_;
v___y_1716_ = v___y_1761_;
v___y_1717_ = v___x_1764_;
goto v___jp_1707_;
}
else
{
v___y_1708_ = v___y_1754_;
v___y_1709_ = v___y_1755_;
v___y_1710_ = v___y_1756_;
v___y_1711_ = v___y_1757_;
v___y_1712_ = v_a_1762_;
v___y_1713_ = v___y_1758_;
v___y_1714_ = v___y_1760_;
v___y_1715_ = v___y_1759_;
v___y_1716_ = v___y_1761_;
v___y_1717_ = v___x_1763_;
goto v___jp_1707_;
}
}
v___jp_1765_:
{
if (lean_obj_tag(v___y_1774_) == 0)
{
lean_object* v_a_1775_; 
lean_dec_ref(v_binderType_1515_);
lean_dec_ref(v_expr_1286_);
v_a_1775_ = lean_ctor_get(v___y_1774_, 0);
lean_inc(v_a_1775_);
lean_dec_ref(v___y_1774_);
v___y_1427_ = v___y_1766_;
v___y_1428_ = v___y_1767_;
v___y_1429_ = v___y_1768_;
v___y_1430_ = v___y_1769_;
v___y_1431_ = v___y_1770_;
v___y_1432_ = v___y_1772_;
v___y_1433_ = v___y_1771_;
v___y_1434_ = v___y_1773_;
v_a_1435_ = v_a_1775_;
goto v___jp_1426_;
}
else
{
lean_object* v_a_1776_; 
v_a_1776_ = lean_ctor_get(v___y_1774_, 0);
lean_inc(v_a_1776_);
lean_dec_ref(v___y_1774_);
v___y_1754_ = v___y_1766_;
v___y_1755_ = v___y_1767_;
v___y_1756_ = v___y_1768_;
v___y_1757_ = v___y_1769_;
v___y_1758_ = v___y_1770_;
v___y_1759_ = v___y_1772_;
v___y_1760_ = v___y_1771_;
v___y_1761_ = v___y_1773_;
v_a_1762_ = v_a_1776_;
goto v___jp_1753_;
}
}
v___jp_1777_:
{
if (v___y_1789_ == 0)
{
lean_object* v___x_1790_; 
lean_dec_ref(v___y_1783_);
v___x_1790_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v___y_1780_, v___y_1788_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v___x_1792_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1791_);
lean_dec_ref(v___x_1790_);
lean_inc_ref(v_binderType_1515_);
v___x_1792_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1791_, v_binderType_1515_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1792_) == 0)
{
lean_object* v_a_1793_; lean_object* v___x_1794_; 
v_a_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1793_);
lean_dec_ref(v___x_1792_);
lean_inc_ref(v_arg_1499_);
v___x_1794_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1499_, v_a_1793_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_object* v_a_1795_; 
v_a_1795_ = lean_ctor_get(v___x_1794_, 0);
lean_inc(v_a_1795_);
lean_dec_ref(v___x_1794_);
if (lean_obj_tag(v_a_1795_) == 1)
{
lean_object* v_val_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v_val_1796_ = lean_ctor_get(v_a_1795_, 0);
lean_inc(v_val_1796_);
lean_dec_ref(v_a_1795_);
lean_inc_ref(v_arg_1501_);
lean_inc_ref(v_fn_1500_);
v___x_1797_ = l_Lean_Expr_app___override(v_fn_1500_, v_arg_1501_);
v___x_1798_ = lean_box(0);
v___x_1799_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1799_, 0, v___x_1797_);
lean_ctor_set(v___x_1799_, 1, v___x_1798_);
lean_ctor_set_uint8(v___x_1799_, sizeof(void*)*2, v___y_1786_);
v___x_1800_ = l_Lean_Meta_Simp_mkCongr(v___x_1799_, v_val_1796_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v___y_1766_ = v___y_1778_;
v___y_1767_ = v___y_1779_;
v___y_1768_ = v___y_1781_;
v___y_1769_ = v___y_1782_;
v___y_1770_ = v___y_1784_;
v___y_1771_ = v___y_1785_;
v___y_1772_ = v___y_1786_;
v___y_1773_ = v___y_1787_;
v___y_1774_ = v___x_1800_;
goto v___jp_1765_;
}
else
{
lean_object* v___x_1801_; lean_object* v___x_1802_; 
lean_dec(v_a_1795_);
v___x_1801_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1802_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1801_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v___y_1766_ = v___y_1778_;
v___y_1767_ = v___y_1779_;
v___y_1768_ = v___y_1781_;
v___y_1769_ = v___y_1782_;
v___y_1770_ = v___y_1784_;
v___y_1771_ = v___y_1785_;
v___y_1772_ = v___y_1786_;
v___y_1773_ = v___y_1787_;
v___y_1774_ = v___x_1802_;
goto v___jp_1765_;
}
}
else
{
lean_object* v_a_1803_; 
v_a_1803_ = lean_ctor_get(v___x_1794_, 0);
lean_inc(v_a_1803_);
lean_dec_ref(v___x_1794_);
v___y_1754_ = v___y_1778_;
v___y_1755_ = v___y_1779_;
v___y_1756_ = v___y_1781_;
v___y_1757_ = v___y_1782_;
v___y_1758_ = v___y_1784_;
v___y_1759_ = v___y_1786_;
v___y_1760_ = v___y_1785_;
v___y_1761_ = v___y_1787_;
v_a_1762_ = v_a_1803_;
goto v___jp_1753_;
}
}
else
{
lean_object* v_a_1804_; 
v_a_1804_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_a_1804_);
lean_dec_ref(v___x_1792_);
v___y_1754_ = v___y_1778_;
v___y_1755_ = v___y_1779_;
v___y_1756_ = v___y_1781_;
v___y_1757_ = v___y_1782_;
v___y_1758_ = v___y_1784_;
v___y_1759_ = v___y_1786_;
v___y_1760_ = v___y_1785_;
v___y_1761_ = v___y_1787_;
v_a_1762_ = v_a_1804_;
goto v___jp_1753_;
}
}
else
{
lean_object* v_a_1805_; 
v_a_1805_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_a_1805_);
lean_dec_ref(v___x_1790_);
v___y_1754_ = v___y_1778_;
v___y_1755_ = v___y_1779_;
v___y_1756_ = v___y_1781_;
v___y_1757_ = v___y_1782_;
v___y_1758_ = v___y_1784_;
v___y_1759_ = v___y_1786_;
v___y_1760_ = v___y_1785_;
v___y_1761_ = v___y_1787_;
v_a_1762_ = v_a_1805_;
goto v___jp_1753_;
}
}
else
{
lean_dec_ref(v___y_1788_);
lean_dec_ref(v___y_1780_);
v___y_1754_ = v___y_1778_;
v___y_1755_ = v___y_1779_;
v___y_1756_ = v___y_1781_;
v___y_1757_ = v___y_1782_;
v___y_1758_ = v___y_1784_;
v___y_1759_ = v___y_1786_;
v___y_1760_ = v___y_1785_;
v___y_1761_ = v___y_1787_;
v_a_1762_ = v___y_1783_;
goto v___jp_1753_;
}
}
v___jp_1806_:
{
uint8_t v___x_1818_; 
v___x_1818_ = l_Lean_Exception_isInterrupt(v_a_1817_);
if (v___x_1818_ == 0)
{
uint8_t v___x_1819_; 
lean_inc_ref(v_a_1817_);
v___x_1819_ = l_Lean_Exception_isRuntime(v_a_1817_);
v___y_1778_ = v___y_1807_;
v___y_1779_ = v___y_1808_;
v___y_1780_ = v___y_1809_;
v___y_1781_ = v___y_1810_;
v___y_1782_ = v___y_1811_;
v___y_1783_ = v_a_1817_;
v___y_1784_ = v___y_1812_;
v___y_1785_ = v___y_1814_;
v___y_1786_ = v___y_1813_;
v___y_1787_ = v___y_1815_;
v___y_1788_ = v___y_1816_;
v___y_1789_ = v___x_1819_;
goto v___jp_1777_;
}
else
{
v___y_1778_ = v___y_1807_;
v___y_1779_ = v___y_1808_;
v___y_1780_ = v___y_1809_;
v___y_1781_ = v___y_1810_;
v___y_1782_ = v___y_1811_;
v___y_1783_ = v_a_1817_;
v___y_1784_ = v___y_1812_;
v___y_1785_ = v___y_1814_;
v___y_1786_ = v___y_1813_;
v___y_1787_ = v___y_1815_;
v___y_1788_ = v___y_1816_;
v___y_1789_ = v___x_1818_;
goto v___jp_1777_;
}
}
v___jp_1820_:
{
if (lean_obj_tag(v___y_1831_) == 0)
{
lean_object* v_a_1832_; 
lean_dec_ref(v___y_1830_);
lean_dec_ref(v___y_1823_);
lean_dec_ref(v_binderType_1515_);
lean_dec_ref(v_expr_1286_);
v_a_1832_ = lean_ctor_get(v___y_1831_, 0);
lean_inc(v_a_1832_);
lean_dec_ref(v___y_1831_);
v___y_1427_ = v___y_1821_;
v___y_1428_ = v___y_1822_;
v___y_1429_ = v___y_1824_;
v___y_1430_ = v___y_1825_;
v___y_1431_ = v___y_1826_;
v___y_1432_ = v___y_1828_;
v___y_1433_ = v___y_1827_;
v___y_1434_ = v___y_1829_;
v_a_1435_ = v_a_1832_;
goto v___jp_1426_;
}
else
{
lean_object* v_a_1833_; 
v_a_1833_ = lean_ctor_get(v___y_1831_, 0);
lean_inc(v_a_1833_);
lean_dec_ref(v___y_1831_);
v___y_1807_ = v___y_1821_;
v___y_1808_ = v___y_1822_;
v___y_1809_ = v___y_1823_;
v___y_1810_ = v___y_1824_;
v___y_1811_ = v___y_1825_;
v___y_1812_ = v___y_1826_;
v___y_1813_ = v___y_1828_;
v___y_1814_ = v___y_1827_;
v___y_1815_ = v___y_1829_;
v___y_1816_ = v___y_1830_;
v_a_1817_ = v_a_1833_;
goto v___jp_1806_;
}
}
v___jp_1834_:
{
if (v___y_1844_ == 0)
{
lean_object* v___x_1845_; 
lean_dec_ref(v___y_1841_);
v___x_1845_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1501_);
if (lean_obj_tag(v___x_1845_) == 1)
{
lean_object* v_val_1846_; lean_object* v_snd_1847_; lean_object* v___x_1848_; 
v_val_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_val_1846_);
lean_dec_ref(v___x_1845_);
v_snd_1847_ = lean_ctor_get(v_val_1846_, 1);
lean_inc(v_snd_1847_);
lean_dec(v_val_1846_);
v___x_1848_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1499_, v_a_1290_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref(v___x_1848_);
if (lean_obj_tag(v_a_1849_) == 1)
{
lean_object* v_val_1850_; lean_object* v___x_1851_; 
v_val_1850_ = lean_ctor_get(v_a_1849_, 0);
lean_inc(v_val_1850_);
lean_dec_ref(v_a_1849_);
lean_inc(v_a_1290_);
lean_inc_ref(v_a_1289_);
lean_inc(v_a_1288_);
lean_inc_ref(v_a_1287_);
v___x_1851_ = lean_infer_type(v_val_1850_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; lean_object* v___x_1853_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
lean_inc(v_a_1852_);
lean_dec_ref(v___x_1851_);
v___x_1853_ = l_Lean_Meta_mkNumeral(v_a_1852_, v_snd_1847_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1855_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1854_);
lean_dec_ref(v___x_1853_);
v___x_1855_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1854_, v_binderType_1515_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; lean_object* v___x_1857_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_a_1856_);
lean_dec_ref(v___x_1855_);
lean_inc_ref(v_arg_1501_);
v___x_1857_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1501_, v_a_1856_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
lean_inc(v_a_1858_);
lean_dec_ref(v___x_1857_);
if (lean_obj_tag(v_a_1858_) == 1)
{
lean_object* v_val_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v_val_1859_ = lean_ctor_get(v_a_1858_, 0);
lean_inc(v_val_1859_);
lean_dec_ref(v_a_1858_);
v___x_1860_ = lean_box(0);
lean_inc_ref(v_fn_1500_);
v___x_1861_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1861_, 0, v_fn_1500_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
lean_ctor_set_uint8(v___x_1861_, sizeof(void*)*2, v___y_1840_);
v___x_1862_ = l_Lean_Meta_Simp_mkCongr(v___x_1861_, v_val_1859_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; lean_object* v___x_1864_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_a_1863_);
lean_dec_ref(v___x_1862_);
lean_inc_ref(v_arg_1499_);
v___x_1864_ = l_Lean_Meta_Simp_mkCongrFun(v_a_1863_, v_arg_1499_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; 
lean_dec_ref(v_expr_1286_);
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_a_1865_);
lean_dec_ref(v___x_1864_);
v___y_1351_ = v___y_1835_;
v___y_1352_ = v___y_1836_;
v___y_1353_ = v___y_1837_;
v___y_1354_ = v___y_1838_;
v___y_1355_ = v___y_1840_;
v___y_1356_ = v___y_1839_;
v___y_1357_ = v___y_1842_;
v___y_1358_ = v___y_1843_;
v_a_1359_ = v_a_1865_;
goto v___jp_1350_;
}
else
{
lean_object* v_a_1866_; 
v_a_1866_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_a_1866_);
lean_dec_ref(v___x_1864_);
v___y_1375_ = v___y_1835_;
v___y_1376_ = v___y_1836_;
v___y_1377_ = v___y_1837_;
v___y_1378_ = v___y_1838_;
v___y_1379_ = v___y_1840_;
v___y_1380_ = v___y_1839_;
v___y_1381_ = v___y_1842_;
v___y_1382_ = v___y_1843_;
v_a_1383_ = v_a_1866_;
goto v___jp_1374_;
}
}
else
{
lean_object* v_a_1867_; 
v_a_1867_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_a_1867_);
lean_dec_ref(v___x_1862_);
v___y_1375_ = v___y_1835_;
v___y_1376_ = v___y_1836_;
v___y_1377_ = v___y_1837_;
v___y_1378_ = v___y_1838_;
v___y_1379_ = v___y_1840_;
v___y_1380_ = v___y_1839_;
v___y_1381_ = v___y_1842_;
v___y_1382_ = v___y_1843_;
v_a_1383_ = v_a_1867_;
goto v___jp_1374_;
}
}
else
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v_a_1870_; 
lean_dec(v_a_1858_);
v___x_1868_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1869_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1868_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_a_1870_);
lean_dec_ref(v___x_1869_);
v___y_1375_ = v___y_1835_;
v___y_1376_ = v___y_1836_;
v___y_1377_ = v___y_1837_;
v___y_1378_ = v___y_1838_;
v___y_1379_ = v___y_1840_;
v___y_1380_ = v___y_1839_;
v___y_1381_ = v___y_1842_;
v___y_1382_ = v___y_1843_;
v_a_1383_ = v_a_1870_;
goto v___jp_1374_;
}
}
else
{
lean_object* v_a_1871_; 
v_a_1871_ = lean_ctor_get(v___x_1857_, 0);
lean_inc(v_a_1871_);
lean_dec_ref(v___x_1857_);
v___y_1375_ = v___y_1835_;
v___y_1376_ = v___y_1836_;
v___y_1377_ = v___y_1837_;
v___y_1378_ = v___y_1838_;
v___y_1379_ = v___y_1840_;
v___y_1380_ = v___y_1839_;
v___y_1381_ = v___y_1842_;
v___y_1382_ = v___y_1843_;
v_a_1383_ = v_a_1871_;
goto v___jp_1374_;
}
}
else
{
lean_object* v_a_1872_; 
v_a_1872_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_a_1872_);
lean_dec_ref(v___x_1855_);
v___y_1375_ = v___y_1835_;
v___y_1376_ = v___y_1836_;
v___y_1377_ = v___y_1837_;
v___y_1378_ = v___y_1838_;
v___y_1379_ = v___y_1840_;
v___y_1380_ = v___y_1839_;
v___y_1381_ = v___y_1842_;
v___y_1382_ = v___y_1843_;
v_a_1383_ = v_a_1872_;
goto v___jp_1374_;
}
}
else
{
lean_object* v_a_1873_; 
lean_dec_ref(v_binderType_1515_);
v_a_1873_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1873_);
lean_dec_ref(v___x_1853_);
v___y_1375_ = v___y_1835_;
v___y_1376_ = v___y_1836_;
v___y_1377_ = v___y_1837_;
v___y_1378_ = v___y_1838_;
v___y_1379_ = v___y_1840_;
v___y_1380_ = v___y_1839_;
v___y_1381_ = v___y_1842_;
v___y_1382_ = v___y_1843_;
v_a_1383_ = v_a_1873_;
goto v___jp_1374_;
}
}
else
{
lean_object* v_a_1874_; 
lean_dec(v_snd_1847_);
lean_dec_ref(v_binderType_1515_);
v_a_1874_ = lean_ctor_get(v___x_1851_, 0);
lean_inc(v_a_1874_);
lean_dec_ref(v___x_1851_);
v___y_1375_ = v___y_1835_;
v___y_1376_ = v___y_1836_;
v___y_1377_ = v___y_1837_;
v___y_1378_ = v___y_1838_;
v___y_1379_ = v___y_1840_;
v___y_1380_ = v___y_1839_;
v___y_1381_ = v___y_1842_;
v___y_1382_ = v___y_1843_;
v_a_1383_ = v_a_1874_;
goto v___jp_1374_;
}
}
else
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v_a_1877_; 
lean_dec(v_a_1849_);
lean_dec(v_snd_1847_);
lean_dec_ref(v_binderType_1515_);
v___x_1875_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1876_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1875_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref(v___x_1876_);
v___y_1375_ = v___y_1835_;
v___y_1376_ = v___y_1836_;
v___y_1377_ = v___y_1837_;
v___y_1378_ = v___y_1838_;
v___y_1379_ = v___y_1840_;
v___y_1380_ = v___y_1839_;
v___y_1381_ = v___y_1842_;
v___y_1382_ = v___y_1843_;
v_a_1383_ = v_a_1877_;
goto v___jp_1374_;
}
}
else
{
lean_object* v_a_1878_; 
lean_dec(v_snd_1847_);
lean_dec_ref(v_binderType_1515_);
v_a_1878_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1878_);
lean_dec_ref(v___x_1848_);
v___y_1375_ = v___y_1835_;
v___y_1376_ = v___y_1836_;
v___y_1377_ = v___y_1837_;
v___y_1378_ = v___y_1838_;
v___y_1379_ = v___y_1840_;
v___y_1380_ = v___y_1839_;
v___y_1381_ = v___y_1842_;
v___y_1382_ = v___y_1843_;
v_a_1383_ = v_a_1878_;
goto v___jp_1374_;
}
}
else
{
lean_object* v___x_1879_; 
lean_dec_ref(v_binderType_1515_);
v___x_1879_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1845_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
lean_dec(v___x_1845_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1880_; 
lean_dec_ref(v_expr_1286_);
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_a_1880_);
lean_dec_ref(v___x_1879_);
v___y_1387_ = v___y_1835_;
v___y_1388_ = v___y_1836_;
v___y_1389_ = v___y_1837_;
v___y_1390_ = v___y_1838_;
v___y_1391_ = v___y_1839_;
v___y_1392_ = v___y_1840_;
v___y_1393_ = v___y_1842_;
v___y_1394_ = v___y_1843_;
v_a_1395_ = v_a_1880_;
goto v___jp_1386_;
}
else
{
lean_object* v_a_1881_; 
v_a_1881_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_a_1881_);
lean_dec_ref(v___x_1879_);
v___y_1375_ = v___y_1835_;
v___y_1376_ = v___y_1836_;
v___y_1377_ = v___y_1837_;
v___y_1378_ = v___y_1838_;
v___y_1379_ = v___y_1840_;
v___y_1380_ = v___y_1839_;
v___y_1381_ = v___y_1842_;
v___y_1382_ = v___y_1843_;
v_a_1383_ = v_a_1881_;
goto v___jp_1374_;
}
}
}
else
{
lean_dec_ref(v_binderType_1515_);
lean_dec_ref(v_expr_1286_);
v___y_1340_ = v___y_1835_;
v___y_1341_ = v___y_1836_;
v___y_1342_ = v___y_1837_;
v___y_1343_ = v___y_1838_;
v___y_1344_ = v___y_1840_;
v___y_1345_ = v___y_1839_;
v___y_1346_ = v___y_1842_;
v___y_1347_ = v___y_1843_;
v_a_1348_ = v___y_1841_;
goto v___jp_1339_;
}
}
v___jp_1882_:
{
uint8_t v___x_1892_; 
v___x_1892_ = l_Lean_Exception_isInterrupt(v_a_1891_);
if (v___x_1892_ == 0)
{
uint8_t v___x_1893_; 
lean_inc_ref(v_a_1891_);
v___x_1893_ = l_Lean_Exception_isRuntime(v_a_1891_);
v___y_1835_ = v___y_1883_;
v___y_1836_ = v___y_1884_;
v___y_1837_ = v___y_1885_;
v___y_1838_ = v___y_1886_;
v___y_1839_ = v___y_1888_;
v___y_1840_ = v___y_1887_;
v___y_1841_ = v_a_1891_;
v___y_1842_ = v___y_1889_;
v___y_1843_ = v___y_1890_;
v___y_1844_ = v___x_1893_;
goto v___jp_1834_;
}
else
{
v___y_1835_ = v___y_1883_;
v___y_1836_ = v___y_1884_;
v___y_1837_ = v___y_1885_;
v___y_1838_ = v___y_1886_;
v___y_1839_ = v___y_1888_;
v___y_1840_ = v___y_1887_;
v___y_1841_ = v_a_1891_;
v___y_1842_ = v___y_1889_;
v___y_1843_ = v___y_1890_;
v___y_1844_ = v___x_1892_;
goto v___jp_1834_;
}
}
v___jp_1894_:
{
if (v___y_1904_ == 0)
{
lean_object* v___x_1905_; 
lean_dec_ref(v___y_1896_);
v___x_1905_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1499_);
if (lean_obj_tag(v___x_1905_) == 1)
{
lean_object* v_val_1906_; lean_object* v_snd_1907_; lean_object* v___x_1908_; 
v_val_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_val_1906_);
lean_dec_ref(v___x_1905_);
v_snd_1907_ = lean_ctor_get(v_val_1906_, 1);
lean_inc(v_snd_1907_);
lean_dec(v_val_1906_);
v___x_1908_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1501_, v_a_1290_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1909_);
lean_dec_ref(v___x_1908_);
if (lean_obj_tag(v_a_1909_) == 1)
{
lean_object* v_val_1910_; lean_object* v___x_1911_; 
v_val_1910_ = lean_ctor_get(v_a_1909_, 0);
lean_inc(v_val_1910_);
lean_dec_ref(v_a_1909_);
lean_inc(v_a_1290_);
lean_inc_ref(v_a_1289_);
lean_inc(v_a_1288_);
lean_inc_ref(v_a_1287_);
v___x_1911_ = lean_infer_type(v_val_1910_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1913_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref(v___x_1911_);
v___x_1913_ = l_Lean_Meta_mkNumeral(v_a_1912_, v_snd_1907_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1915_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref(v___x_1913_);
lean_inc_ref(v_binderType_1515_);
v___x_1915_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1914_, v_binderType_1515_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1917_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref(v___x_1915_);
lean_inc_ref(v_arg_1499_);
v___x_1917_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1499_, v_a_1916_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref(v___x_1917_);
if (lean_obj_tag(v_a_1918_) == 1)
{
lean_object* v_val_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v_val_1919_ = lean_ctor_get(v_a_1918_, 0);
lean_inc(v_val_1919_);
lean_dec_ref(v_a_1918_);
lean_inc_ref(v_arg_1501_);
lean_inc_ref(v_fn_1500_);
v___x_1920_ = l_Lean_Expr_app___override(v_fn_1500_, v_arg_1501_);
v___x_1921_ = lean_box(0);
v___x_1922_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1922_, 0, v___x_1920_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
lean_ctor_set_uint8(v___x_1922_, sizeof(void*)*2, v___y_1901_);
v___x_1923_ = l_Lean_Meta_Simp_mkCongr(v___x_1922_, v_val_1919_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; 
lean_dec_ref(v_binderType_1515_);
lean_dec_ref(v_expr_1286_);
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref(v___x_1923_);
v___y_1351_ = v___y_1895_;
v___y_1352_ = v___y_1897_;
v___y_1353_ = v___y_1898_;
v___y_1354_ = v___y_1899_;
v___y_1355_ = v___y_1901_;
v___y_1356_ = v___y_1900_;
v___y_1357_ = v___y_1902_;
v___y_1358_ = v___y_1903_;
v_a_1359_ = v_a_1924_;
goto v___jp_1350_;
}
else
{
lean_object* v_a_1925_; 
v_a_1925_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1925_);
lean_dec_ref(v___x_1923_);
v___y_1883_ = v___y_1895_;
v___y_1884_ = v___y_1897_;
v___y_1885_ = v___y_1898_;
v___y_1886_ = v___y_1899_;
v___y_1887_ = v___y_1901_;
v___y_1888_ = v___y_1900_;
v___y_1889_ = v___y_1902_;
v___y_1890_ = v___y_1903_;
v_a_1891_ = v_a_1925_;
goto v___jp_1882_;
}
}
else
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v_a_1928_; 
lean_dec(v_a_1918_);
v___x_1926_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1927_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1926_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref(v___x_1927_);
v___y_1883_ = v___y_1895_;
v___y_1884_ = v___y_1897_;
v___y_1885_ = v___y_1898_;
v___y_1886_ = v___y_1899_;
v___y_1887_ = v___y_1901_;
v___y_1888_ = v___y_1900_;
v___y_1889_ = v___y_1902_;
v___y_1890_ = v___y_1903_;
v_a_1891_ = v_a_1928_;
goto v___jp_1882_;
}
}
else
{
lean_object* v_a_1929_; 
v_a_1929_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1929_);
lean_dec_ref(v___x_1917_);
v___y_1883_ = v___y_1895_;
v___y_1884_ = v___y_1897_;
v___y_1885_ = v___y_1898_;
v___y_1886_ = v___y_1899_;
v___y_1887_ = v___y_1901_;
v___y_1888_ = v___y_1900_;
v___y_1889_ = v___y_1902_;
v___y_1890_ = v___y_1903_;
v_a_1891_ = v_a_1929_;
goto v___jp_1882_;
}
}
else
{
lean_object* v_a_1930_; 
v_a_1930_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1930_);
lean_dec_ref(v___x_1915_);
v___y_1883_ = v___y_1895_;
v___y_1884_ = v___y_1897_;
v___y_1885_ = v___y_1898_;
v___y_1886_ = v___y_1899_;
v___y_1887_ = v___y_1901_;
v___y_1888_ = v___y_1900_;
v___y_1889_ = v___y_1902_;
v___y_1890_ = v___y_1903_;
v_a_1891_ = v_a_1930_;
goto v___jp_1882_;
}
}
else
{
lean_object* v_a_1931_; 
v_a_1931_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1931_);
lean_dec_ref(v___x_1913_);
v___y_1883_ = v___y_1895_;
v___y_1884_ = v___y_1897_;
v___y_1885_ = v___y_1898_;
v___y_1886_ = v___y_1899_;
v___y_1887_ = v___y_1901_;
v___y_1888_ = v___y_1900_;
v___y_1889_ = v___y_1902_;
v___y_1890_ = v___y_1903_;
v_a_1891_ = v_a_1931_;
goto v___jp_1882_;
}
}
else
{
lean_object* v_a_1932_; 
lean_dec(v_snd_1907_);
v_a_1932_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1932_);
lean_dec_ref(v___x_1911_);
v___y_1883_ = v___y_1895_;
v___y_1884_ = v___y_1897_;
v___y_1885_ = v___y_1898_;
v___y_1886_ = v___y_1899_;
v___y_1887_ = v___y_1901_;
v___y_1888_ = v___y_1900_;
v___y_1889_ = v___y_1902_;
v___y_1890_ = v___y_1903_;
v_a_1891_ = v_a_1932_;
goto v___jp_1882_;
}
}
else
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v_a_1935_; 
lean_dec(v_a_1909_);
lean_dec(v_snd_1907_);
v___x_1933_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1934_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1933_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref(v___x_1934_);
v___y_1883_ = v___y_1895_;
v___y_1884_ = v___y_1897_;
v___y_1885_ = v___y_1898_;
v___y_1886_ = v___y_1899_;
v___y_1887_ = v___y_1901_;
v___y_1888_ = v___y_1900_;
v___y_1889_ = v___y_1902_;
v___y_1890_ = v___y_1903_;
v_a_1891_ = v_a_1935_;
goto v___jp_1882_;
}
}
else
{
lean_object* v_a_1936_; 
lean_dec(v_snd_1907_);
v_a_1936_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1936_);
lean_dec_ref(v___x_1908_);
v___y_1883_ = v___y_1895_;
v___y_1884_ = v___y_1897_;
v___y_1885_ = v___y_1898_;
v___y_1886_ = v___y_1899_;
v___y_1887_ = v___y_1901_;
v___y_1888_ = v___y_1900_;
v___y_1889_ = v___y_1902_;
v___y_1890_ = v___y_1903_;
v_a_1891_ = v_a_1936_;
goto v___jp_1882_;
}
}
else
{
lean_object* v___x_1937_; 
v___x_1937_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1905_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
lean_dec(v___x_1905_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; 
lean_dec_ref(v_binderType_1515_);
lean_dec_ref(v_expr_1286_);
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
lean_dec_ref(v___x_1937_);
v___y_1387_ = v___y_1895_;
v___y_1388_ = v___y_1897_;
v___y_1389_ = v___y_1898_;
v___y_1390_ = v___y_1899_;
v___y_1391_ = v___y_1900_;
v___y_1392_ = v___y_1901_;
v___y_1393_ = v___y_1902_;
v___y_1394_ = v___y_1903_;
v_a_1395_ = v_a_1938_;
goto v___jp_1386_;
}
else
{
lean_object* v_a_1939_; 
v_a_1939_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1939_);
lean_dec_ref(v___x_1937_);
v___y_1883_ = v___y_1895_;
v___y_1884_ = v___y_1897_;
v___y_1885_ = v___y_1898_;
v___y_1886_ = v___y_1899_;
v___y_1887_ = v___y_1901_;
v___y_1888_ = v___y_1900_;
v___y_1889_ = v___y_1902_;
v___y_1890_ = v___y_1903_;
v_a_1891_ = v_a_1939_;
goto v___jp_1882_;
}
}
}
else
{
lean_dec_ref(v_binderType_1515_);
lean_dec_ref(v_expr_1286_);
v___y_1340_ = v___y_1895_;
v___y_1341_ = v___y_1897_;
v___y_1342_ = v___y_1898_;
v___y_1343_ = v___y_1899_;
v___y_1344_ = v___y_1901_;
v___y_1345_ = v___y_1900_;
v___y_1346_ = v___y_1902_;
v___y_1347_ = v___y_1903_;
v_a_1348_ = v___y_1896_;
goto v___jp_1339_;
}
}
v___jp_1940_:
{
uint8_t v___x_1950_; 
v___x_1950_ = l_Lean_Exception_isInterrupt(v_a_1949_);
if (v___x_1950_ == 0)
{
uint8_t v___x_1951_; 
lean_inc_ref(v_a_1949_);
v___x_1951_ = l_Lean_Exception_isRuntime(v_a_1949_);
v___y_1895_ = v___y_1941_;
v___y_1896_ = v_a_1949_;
v___y_1897_ = v___y_1942_;
v___y_1898_ = v___y_1943_;
v___y_1899_ = v___y_1944_;
v___y_1900_ = v___y_1946_;
v___y_1901_ = v___y_1945_;
v___y_1902_ = v___y_1947_;
v___y_1903_ = v___y_1948_;
v___y_1904_ = v___x_1951_;
goto v___jp_1894_;
}
else
{
v___y_1895_ = v___y_1941_;
v___y_1896_ = v_a_1949_;
v___y_1897_ = v___y_1942_;
v___y_1898_ = v___y_1943_;
v___y_1899_ = v___y_1944_;
v___y_1900_ = v___y_1946_;
v___y_1901_ = v___y_1945_;
v___y_1902_ = v___y_1947_;
v___y_1903_ = v___y_1948_;
v___y_1904_ = v___x_1950_;
goto v___jp_1894_;
}
}
v___jp_1952_:
{
if (lean_obj_tag(v___y_1961_) == 0)
{
lean_object* v_a_1962_; 
lean_dec_ref(v_binderType_1515_);
lean_dec_ref(v_expr_1286_);
v_a_1962_ = lean_ctor_get(v___y_1961_, 0);
lean_inc(v_a_1962_);
lean_dec_ref(v___y_1961_);
v___y_1351_ = v___y_1953_;
v___y_1352_ = v___y_1954_;
v___y_1353_ = v___y_1955_;
v___y_1354_ = v___y_1956_;
v___y_1355_ = v___y_1958_;
v___y_1356_ = v___y_1957_;
v___y_1357_ = v___y_1959_;
v___y_1358_ = v___y_1960_;
v_a_1359_ = v_a_1962_;
goto v___jp_1350_;
}
else
{
lean_object* v_a_1963_; 
v_a_1963_ = lean_ctor_get(v___y_1961_, 0);
lean_inc(v_a_1963_);
lean_dec_ref(v___y_1961_);
v___y_1941_ = v___y_1953_;
v___y_1942_ = v___y_1954_;
v___y_1943_ = v___y_1955_;
v___y_1944_ = v___y_1956_;
v___y_1945_ = v___y_1958_;
v___y_1946_ = v___y_1957_;
v___y_1947_ = v___y_1959_;
v___y_1948_ = v___y_1960_;
v_a_1949_ = v_a_1963_;
goto v___jp_1940_;
}
}
v___jp_1964_:
{
if (v___y_1976_ == 0)
{
lean_object* v___x_1977_; 
lean_dec_ref(v___y_1975_);
v___x_1977_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v___y_1966_, v___y_1972_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1977_) == 0)
{
lean_object* v_a_1978_; lean_object* v___x_1979_; 
v_a_1978_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1978_);
lean_dec_ref(v___x_1977_);
lean_inc_ref(v_binderType_1515_);
v___x_1979_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1978_, v_binderType_1515_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1979_) == 0)
{
lean_object* v_a_1980_; lean_object* v___x_1981_; 
v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref(v___x_1979_);
lean_inc_ref(v_arg_1499_);
v___x_1981_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1499_, v_a_1980_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_a_1982_);
lean_dec_ref(v___x_1981_);
if (lean_obj_tag(v_a_1982_) == 1)
{
lean_object* v_val_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v_val_1983_ = lean_ctor_get(v_a_1982_, 0);
lean_inc(v_val_1983_);
lean_dec_ref(v_a_1982_);
lean_inc_ref(v_arg_1501_);
lean_inc_ref(v_fn_1500_);
v___x_1984_ = l_Lean_Expr_app___override(v_fn_1500_, v_arg_1501_);
v___x_1985_ = lean_box(0);
v___x_1986_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1986_, 0, v___x_1984_);
lean_ctor_set(v___x_1986_, 1, v___x_1985_);
lean_ctor_set_uint8(v___x_1986_, sizeof(void*)*2, v___y_1971_);
v___x_1987_ = l_Lean_Meta_Simp_mkCongr(v___x_1986_, v_val_1983_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v___y_1953_ = v___y_1965_;
v___y_1954_ = v___y_1967_;
v___y_1955_ = v___y_1968_;
v___y_1956_ = v___y_1969_;
v___y_1957_ = v___y_1970_;
v___y_1958_ = v___y_1971_;
v___y_1959_ = v___y_1973_;
v___y_1960_ = v___y_1974_;
v___y_1961_ = v___x_1987_;
goto v___jp_1952_;
}
else
{
lean_object* v___x_1988_; lean_object* v___x_1989_; 
lean_dec(v_a_1982_);
v___x_1988_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1989_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1988_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v___y_1953_ = v___y_1965_;
v___y_1954_ = v___y_1967_;
v___y_1955_ = v___y_1968_;
v___y_1956_ = v___y_1969_;
v___y_1957_ = v___y_1970_;
v___y_1958_ = v___y_1971_;
v___y_1959_ = v___y_1973_;
v___y_1960_ = v___y_1974_;
v___y_1961_ = v___x_1989_;
goto v___jp_1952_;
}
}
else
{
lean_object* v_a_1990_; 
v_a_1990_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_a_1990_);
lean_dec_ref(v___x_1981_);
v___y_1941_ = v___y_1965_;
v___y_1942_ = v___y_1967_;
v___y_1943_ = v___y_1968_;
v___y_1944_ = v___y_1969_;
v___y_1945_ = v___y_1971_;
v___y_1946_ = v___y_1970_;
v___y_1947_ = v___y_1973_;
v___y_1948_ = v___y_1974_;
v_a_1949_ = v_a_1990_;
goto v___jp_1940_;
}
}
else
{
lean_object* v_a_1991_; 
v_a_1991_ = lean_ctor_get(v___x_1979_, 0);
lean_inc(v_a_1991_);
lean_dec_ref(v___x_1979_);
v___y_1941_ = v___y_1965_;
v___y_1942_ = v___y_1967_;
v___y_1943_ = v___y_1968_;
v___y_1944_ = v___y_1969_;
v___y_1945_ = v___y_1971_;
v___y_1946_ = v___y_1970_;
v___y_1947_ = v___y_1973_;
v___y_1948_ = v___y_1974_;
v_a_1949_ = v_a_1991_;
goto v___jp_1940_;
}
}
else
{
lean_object* v_a_1992_; 
v_a_1992_ = lean_ctor_get(v___x_1977_, 0);
lean_inc(v_a_1992_);
lean_dec_ref(v___x_1977_);
v___y_1941_ = v___y_1965_;
v___y_1942_ = v___y_1967_;
v___y_1943_ = v___y_1968_;
v___y_1944_ = v___y_1969_;
v___y_1945_ = v___y_1971_;
v___y_1946_ = v___y_1970_;
v___y_1947_ = v___y_1973_;
v___y_1948_ = v___y_1974_;
v_a_1949_ = v_a_1992_;
goto v___jp_1940_;
}
}
else
{
lean_dec_ref(v___y_1972_);
lean_dec_ref(v___y_1966_);
v___y_1941_ = v___y_1965_;
v___y_1942_ = v___y_1967_;
v___y_1943_ = v___y_1968_;
v___y_1944_ = v___y_1969_;
v___y_1945_ = v___y_1971_;
v___y_1946_ = v___y_1970_;
v___y_1947_ = v___y_1973_;
v___y_1948_ = v___y_1974_;
v_a_1949_ = v___y_1975_;
goto v___jp_1940_;
}
}
v___jp_1993_:
{
uint8_t v___x_2005_; 
v___x_2005_ = l_Lean_Exception_isInterrupt(v_a_2004_);
if (v___x_2005_ == 0)
{
uint8_t v___x_2006_; 
lean_inc_ref(v_a_2004_);
v___x_2006_ = l_Lean_Exception_isRuntime(v_a_2004_);
v___y_1965_ = v___y_1995_;
v___y_1966_ = v___y_1994_;
v___y_1967_ = v___y_1996_;
v___y_1968_ = v___y_1997_;
v___y_1969_ = v___y_1998_;
v___y_1970_ = v___y_2000_;
v___y_1971_ = v___y_1999_;
v___y_1972_ = v___y_2001_;
v___y_1973_ = v___y_2002_;
v___y_1974_ = v___y_2003_;
v___y_1975_ = v_a_2004_;
v___y_1976_ = v___x_2006_;
goto v___jp_1964_;
}
else
{
v___y_1965_ = v___y_1995_;
v___y_1966_ = v___y_1994_;
v___y_1967_ = v___y_1996_;
v___y_1968_ = v___y_1997_;
v___y_1969_ = v___y_1998_;
v___y_1970_ = v___y_2000_;
v___y_1971_ = v___y_1999_;
v___y_1972_ = v___y_2001_;
v___y_1973_ = v___y_2002_;
v___y_1974_ = v___y_2003_;
v___y_1975_ = v_a_2004_;
v___y_1976_ = v___x_2005_;
goto v___jp_1964_;
}
}
v___jp_2007_:
{
if (lean_obj_tag(v___y_2018_) == 0)
{
lean_object* v_a_2019_; 
lean_dec_ref(v___y_2015_);
lean_dec_ref(v___y_2008_);
lean_dec_ref(v_binderType_1515_);
lean_dec_ref(v_expr_1286_);
v_a_2019_ = lean_ctor_get(v___y_2018_, 0);
lean_inc(v_a_2019_);
lean_dec_ref(v___y_2018_);
v___y_1351_ = v___y_2009_;
v___y_1352_ = v___y_2010_;
v___y_1353_ = v___y_2011_;
v___y_1354_ = v___y_2012_;
v___y_1355_ = v___y_2014_;
v___y_1356_ = v___y_2013_;
v___y_1357_ = v___y_2016_;
v___y_1358_ = v___y_2017_;
v_a_1359_ = v_a_2019_;
goto v___jp_1350_;
}
else
{
lean_object* v_a_2020_; 
v_a_2020_ = lean_ctor_get(v___y_2018_, 0);
lean_inc(v_a_2020_);
lean_dec_ref(v___y_2018_);
v___y_1994_ = v___y_2008_;
v___y_1995_ = v___y_2009_;
v___y_1996_ = v___y_2010_;
v___y_1997_ = v___y_2011_;
v___y_1998_ = v___y_2012_;
v___y_1999_ = v___y_2014_;
v___y_2000_ = v___y_2013_;
v___y_2001_ = v___y_2015_;
v___y_2002_ = v___y_2016_;
v___y_2003_ = v___y_2017_;
v_a_2004_ = v_a_2020_;
goto v___jp_1993_;
}
}
v___jp_2021_:
{
lean_object* v___x_2028_; lean_object* v_a_2029_; lean_object* v___x_2030_; uint8_t v___x_2031_; 
v___x_2028_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg(v_a_1290_);
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc(v_a_2029_);
lean_dec_ref(v___x_2028_);
v___x_2030_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2031_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v___y_2023_, v___x_2030_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2032_ = lean_io_mono_nanos_now();
v___x_2033_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1501_, v_a_1290_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref(v___x_2033_);
if (lean_obj_tag(v_a_2034_) == 1)
{
lean_object* v_val_2035_; lean_object* v___x_2036_; 
v_val_2035_ = lean_ctor_get(v_a_2034_, 0);
lean_inc(v_val_2035_);
lean_dec_ref(v_a_2034_);
v___x_2036_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1499_, v_a_1290_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_a_2037_; 
v_a_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2037_);
lean_dec_ref(v___x_2036_);
if (lean_obj_tag(v_a_2037_) == 1)
{
lean_object* v_val_2038_; lean_object* v___x_2039_; 
v_val_2038_ = lean_ctor_get(v_a_2037_, 0);
lean_inc(v_val_2038_);
lean_dec_ref(v_a_2037_);
lean_inc(v_a_1290_);
lean_inc_ref(v_a_1289_);
lean_inc(v_a_1288_);
lean_inc_ref(v_a_1287_);
lean_inc(v_val_2035_);
v___x_2039_ = lean_infer_type(v_val_2035_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2041_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref(v___x_2039_);
lean_inc(v_a_1290_);
lean_inc_ref(v_a_1289_);
lean_inc(v_a_1288_);
lean_inc_ref(v_a_1287_);
lean_inc(v_val_2038_);
v___x_2041_ = lean_infer_type(v_val_2038_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2043_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref(v___x_2041_);
v___x_2043_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_val_2035_, v_a_2042_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; lean_object* v___x_2045_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref(v___x_2043_);
lean_inc_ref(v_binderType_1515_);
v___x_2045_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2044_, v_binderType_1515_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2045_) == 0)
{
lean_object* v_a_2046_; lean_object* v___x_2047_; 
v_a_2046_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2046_);
lean_dec_ref(v___x_2045_);
lean_inc_ref(v_arg_1501_);
v___x_2047_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1501_, v_a_2046_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref(v___x_2047_);
if (lean_obj_tag(v_a_2048_) == 1)
{
lean_object* v_val_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v_val_2049_ = lean_ctor_get(v_a_2048_, 0);
lean_inc(v_val_2049_);
lean_dec_ref(v_a_2048_);
v___x_2050_ = lean_box(0);
lean_inc_ref(v_fn_1500_);
v___x_2051_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2051_, 0, v_fn_1500_);
lean_ctor_set(v___x_2051_, 1, v___x_2050_);
lean_ctor_set_uint8(v___x_2051_, sizeof(void*)*2, v___y_2025_);
v___x_2052_ = l_Lean_Meta_Simp_mkCongr(v___x_2051_, v_val_2049_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; lean_object* v___x_2054_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2053_);
lean_dec_ref(v___x_2052_);
lean_inc_ref(v_arg_1499_);
v___x_2054_ = l_Lean_Meta_Simp_mkCongrFun(v_a_2053_, v_arg_1499_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v___y_2008_ = v_val_2038_;
v___y_2009_ = v_a_2029_;
v___y_2010_ = v___y_2022_;
v___y_2011_ = v___y_2023_;
v___y_2012_ = v___y_2024_;
v___y_2013_ = v___y_2026_;
v___y_2014_ = v___y_2025_;
v___y_2015_ = v_a_2040_;
v___y_2016_ = v___y_2027_;
v___y_2017_ = v___x_2032_;
v___y_2018_ = v___x_2054_;
goto v___jp_2007_;
}
else
{
v___y_2008_ = v_val_2038_;
v___y_2009_ = v_a_2029_;
v___y_2010_ = v___y_2022_;
v___y_2011_ = v___y_2023_;
v___y_2012_ = v___y_2024_;
v___y_2013_ = v___y_2026_;
v___y_2014_ = v___y_2025_;
v___y_2015_ = v_a_2040_;
v___y_2016_ = v___y_2027_;
v___y_2017_ = v___x_2032_;
v___y_2018_ = v___x_2052_;
goto v___jp_2007_;
}
}
else
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
lean_dec(v_a_2048_);
v___x_2055_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2056_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2055_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v___y_2008_ = v_val_2038_;
v___y_2009_ = v_a_2029_;
v___y_2010_ = v___y_2022_;
v___y_2011_ = v___y_2023_;
v___y_2012_ = v___y_2024_;
v___y_2013_ = v___y_2026_;
v___y_2014_ = v___y_2025_;
v___y_2015_ = v_a_2040_;
v___y_2016_ = v___y_2027_;
v___y_2017_ = v___x_2032_;
v___y_2018_ = v___x_2056_;
goto v___jp_2007_;
}
}
else
{
lean_object* v_a_2057_; 
v_a_2057_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2057_);
lean_dec_ref(v___x_2047_);
v___y_1994_ = v_val_2038_;
v___y_1995_ = v_a_2029_;
v___y_1996_ = v___y_2022_;
v___y_1997_ = v___y_2023_;
v___y_1998_ = v___y_2024_;
v___y_1999_ = v___y_2025_;
v___y_2000_ = v___y_2026_;
v___y_2001_ = v_a_2040_;
v___y_2002_ = v___y_2027_;
v___y_2003_ = v___x_2032_;
v_a_2004_ = v_a_2057_;
goto v___jp_1993_;
}
}
else
{
lean_object* v_a_2058_; 
v_a_2058_ = lean_ctor_get(v___x_2045_, 0);
lean_inc(v_a_2058_);
lean_dec_ref(v___x_2045_);
v___y_1994_ = v_val_2038_;
v___y_1995_ = v_a_2029_;
v___y_1996_ = v___y_2022_;
v___y_1997_ = v___y_2023_;
v___y_1998_ = v___y_2024_;
v___y_1999_ = v___y_2025_;
v___y_2000_ = v___y_2026_;
v___y_2001_ = v_a_2040_;
v___y_2002_ = v___y_2027_;
v___y_2003_ = v___x_2032_;
v_a_2004_ = v_a_2058_;
goto v___jp_1993_;
}
}
else
{
lean_object* v_a_2059_; 
v_a_2059_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2059_);
lean_dec_ref(v___x_2043_);
v___y_1994_ = v_val_2038_;
v___y_1995_ = v_a_2029_;
v___y_1996_ = v___y_2022_;
v___y_1997_ = v___y_2023_;
v___y_1998_ = v___y_2024_;
v___y_1999_ = v___y_2025_;
v___y_2000_ = v___y_2026_;
v___y_2001_ = v_a_2040_;
v___y_2002_ = v___y_2027_;
v___y_2003_ = v___x_2032_;
v_a_2004_ = v_a_2059_;
goto v___jp_1993_;
}
}
else
{
lean_object* v_a_2060_; 
lean_dec(v_a_2040_);
lean_dec(v_val_2038_);
lean_dec(v_val_2035_);
v_a_2060_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2060_);
lean_dec_ref(v___x_2041_);
v___y_1941_ = v_a_2029_;
v___y_1942_ = v___y_2022_;
v___y_1943_ = v___y_2023_;
v___y_1944_ = v___y_2024_;
v___y_1945_ = v___y_2025_;
v___y_1946_ = v___y_2026_;
v___y_1947_ = v___y_2027_;
v___y_1948_ = v___x_2032_;
v_a_1949_ = v_a_2060_;
goto v___jp_1940_;
}
}
else
{
lean_object* v_a_2061_; 
lean_dec(v_val_2038_);
lean_dec(v_val_2035_);
v_a_2061_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2061_);
lean_dec_ref(v___x_2039_);
v___y_1941_ = v_a_2029_;
v___y_1942_ = v___y_2022_;
v___y_1943_ = v___y_2023_;
v___y_1944_ = v___y_2024_;
v___y_1945_ = v___y_2025_;
v___y_1946_ = v___y_2026_;
v___y_1947_ = v___y_2027_;
v___y_1948_ = v___x_2032_;
v_a_1949_ = v_a_2061_;
goto v___jp_1940_;
}
}
else
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v_a_2064_; 
lean_dec(v_a_2037_);
lean_dec(v_val_2035_);
v___x_2062_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2063_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2062_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref(v___x_2063_);
v___y_1941_ = v_a_2029_;
v___y_1942_ = v___y_2022_;
v___y_1943_ = v___y_2023_;
v___y_1944_ = v___y_2024_;
v___y_1945_ = v___y_2025_;
v___y_1946_ = v___y_2026_;
v___y_1947_ = v___y_2027_;
v___y_1948_ = v___x_2032_;
v_a_1949_ = v_a_2064_;
goto v___jp_1940_;
}
}
else
{
lean_object* v_a_2065_; 
lean_dec(v_val_2035_);
v_a_2065_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_a_2065_);
lean_dec_ref(v___x_2036_);
v___y_1941_ = v_a_2029_;
v___y_1942_ = v___y_2022_;
v___y_1943_ = v___y_2023_;
v___y_1944_ = v___y_2024_;
v___y_1945_ = v___y_2025_;
v___y_1946_ = v___y_2026_;
v___y_1947_ = v___y_2027_;
v___y_1948_ = v___x_2032_;
v_a_1949_ = v_a_2065_;
goto v___jp_1940_;
}
}
else
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v_a_2068_; 
lean_dec(v_a_2034_);
v___x_2066_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2067_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2066_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v_a_2068_ = lean_ctor_get(v___x_2067_, 0);
lean_inc(v_a_2068_);
lean_dec_ref(v___x_2067_);
v___y_1941_ = v_a_2029_;
v___y_1942_ = v___y_2022_;
v___y_1943_ = v___y_2023_;
v___y_1944_ = v___y_2024_;
v___y_1945_ = v___y_2025_;
v___y_1946_ = v___y_2026_;
v___y_1947_ = v___y_2027_;
v___y_1948_ = v___x_2032_;
v_a_1949_ = v_a_2068_;
goto v___jp_1940_;
}
}
else
{
lean_object* v_a_2069_; 
v_a_2069_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2069_);
lean_dec_ref(v___x_2033_);
v___y_1941_ = v_a_2029_;
v___y_1942_ = v___y_2022_;
v___y_1943_ = v___y_2023_;
v___y_1944_ = v___y_2024_;
v___y_1945_ = v___y_2025_;
v___y_1946_ = v___y_2026_;
v___y_1947_ = v___y_2027_;
v___y_1948_ = v___x_2032_;
v_a_1949_ = v_a_2069_;
goto v___jp_1940_;
}
}
else
{
lean_object* v___x_2070_; lean_object* v___x_2071_; 
v___x_2070_ = lean_io_get_num_heartbeats();
v___x_2071_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1501_, v_a_1290_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2072_);
lean_dec_ref(v___x_2071_);
if (lean_obj_tag(v_a_2072_) == 1)
{
lean_object* v_val_2073_; lean_object* v___x_2074_; 
v_val_2073_ = lean_ctor_get(v_a_2072_, 0);
lean_inc(v_val_2073_);
lean_dec_ref(v_a_2072_);
v___x_2074_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1499_, v_a_1290_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2075_);
lean_dec_ref(v___x_2074_);
if (lean_obj_tag(v_a_2075_) == 1)
{
lean_object* v_val_2076_; lean_object* v___x_2077_; 
v_val_2076_ = lean_ctor_get(v_a_2075_, 0);
lean_inc(v_val_2076_);
lean_dec_ref(v_a_2075_);
lean_inc(v_a_1290_);
lean_inc_ref(v_a_1289_);
lean_inc(v_a_1288_);
lean_inc_ref(v_a_1287_);
lean_inc(v_val_2073_);
v___x_2077_ = lean_infer_type(v_val_2073_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2077_) == 0)
{
lean_object* v_a_2078_; lean_object* v___x_2079_; 
v_a_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2078_);
lean_dec_ref(v___x_2077_);
lean_inc(v_a_1290_);
lean_inc_ref(v_a_1289_);
lean_inc(v_a_1288_);
lean_inc_ref(v_a_1287_);
lean_inc(v_val_2076_);
v___x_2079_ = lean_infer_type(v_val_2076_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2081_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_a_2080_);
lean_dec_ref(v___x_2079_);
v___x_2081_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_val_2073_, v_a_2080_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v___x_2083_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2082_);
lean_dec_ref(v___x_2081_);
lean_inc_ref(v_binderType_1515_);
v___x_2083_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2082_, v_binderType_1515_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2083_) == 0)
{
lean_object* v_a_2084_; lean_object* v___x_2085_; 
v_a_2084_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_a_2084_);
lean_dec_ref(v___x_2083_);
lean_inc_ref(v_arg_1501_);
v___x_2085_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1501_, v_a_2084_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2086_);
lean_dec_ref(v___x_2085_);
if (lean_obj_tag(v_a_2086_) == 1)
{
lean_object* v_val_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v_val_2087_ = lean_ctor_get(v_a_2086_, 0);
lean_inc(v_val_2087_);
lean_dec_ref(v_a_2086_);
v___x_2088_ = lean_box(0);
lean_inc_ref(v_fn_1500_);
v___x_2089_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2089_, 0, v_fn_1500_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
lean_ctor_set_uint8(v___x_2089_, sizeof(void*)*2, v___y_2025_);
v___x_2090_ = l_Lean_Meta_Simp_mkCongr(v___x_2089_, v_val_2087_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; lean_object* v___x_2092_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref(v___x_2090_);
lean_inc_ref(v_arg_1499_);
v___x_2092_ = l_Lean_Meta_Simp_mkCongrFun(v_a_2091_, v_arg_1499_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v___y_1821_ = v___x_2070_;
v___y_1822_ = v_a_2029_;
v___y_1823_ = v_val_2076_;
v___y_1824_ = v___y_2022_;
v___y_1825_ = v___y_2023_;
v___y_1826_ = v___y_2024_;
v___y_1827_ = v___y_2026_;
v___y_1828_ = v___y_2025_;
v___y_1829_ = v___y_2027_;
v___y_1830_ = v_a_2078_;
v___y_1831_ = v___x_2092_;
goto v___jp_1820_;
}
else
{
v___y_1821_ = v___x_2070_;
v___y_1822_ = v_a_2029_;
v___y_1823_ = v_val_2076_;
v___y_1824_ = v___y_2022_;
v___y_1825_ = v___y_2023_;
v___y_1826_ = v___y_2024_;
v___y_1827_ = v___y_2026_;
v___y_1828_ = v___y_2025_;
v___y_1829_ = v___y_2027_;
v___y_1830_ = v_a_2078_;
v___y_1831_ = v___x_2090_;
goto v___jp_1820_;
}
}
else
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
lean_dec(v_a_2086_);
v___x_2093_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2094_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2093_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v___y_1821_ = v___x_2070_;
v___y_1822_ = v_a_2029_;
v___y_1823_ = v_val_2076_;
v___y_1824_ = v___y_2022_;
v___y_1825_ = v___y_2023_;
v___y_1826_ = v___y_2024_;
v___y_1827_ = v___y_2026_;
v___y_1828_ = v___y_2025_;
v___y_1829_ = v___y_2027_;
v___y_1830_ = v_a_2078_;
v___y_1831_ = v___x_2094_;
goto v___jp_1820_;
}
}
else
{
lean_object* v_a_2095_; 
v_a_2095_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2095_);
lean_dec_ref(v___x_2085_);
v___y_1807_ = v___x_2070_;
v___y_1808_ = v_a_2029_;
v___y_1809_ = v_val_2076_;
v___y_1810_ = v___y_2022_;
v___y_1811_ = v___y_2023_;
v___y_1812_ = v___y_2024_;
v___y_1813_ = v___y_2025_;
v___y_1814_ = v___y_2026_;
v___y_1815_ = v___y_2027_;
v___y_1816_ = v_a_2078_;
v_a_1817_ = v_a_2095_;
goto v___jp_1806_;
}
}
else
{
lean_object* v_a_2096_; 
v_a_2096_ = lean_ctor_get(v___x_2083_, 0);
lean_inc(v_a_2096_);
lean_dec_ref(v___x_2083_);
v___y_1807_ = v___x_2070_;
v___y_1808_ = v_a_2029_;
v___y_1809_ = v_val_2076_;
v___y_1810_ = v___y_2022_;
v___y_1811_ = v___y_2023_;
v___y_1812_ = v___y_2024_;
v___y_1813_ = v___y_2025_;
v___y_1814_ = v___y_2026_;
v___y_1815_ = v___y_2027_;
v___y_1816_ = v_a_2078_;
v_a_1817_ = v_a_2096_;
goto v___jp_1806_;
}
}
else
{
lean_object* v_a_2097_; 
v_a_2097_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2097_);
lean_dec_ref(v___x_2081_);
v___y_1807_ = v___x_2070_;
v___y_1808_ = v_a_2029_;
v___y_1809_ = v_val_2076_;
v___y_1810_ = v___y_2022_;
v___y_1811_ = v___y_2023_;
v___y_1812_ = v___y_2024_;
v___y_1813_ = v___y_2025_;
v___y_1814_ = v___y_2026_;
v___y_1815_ = v___y_2027_;
v___y_1816_ = v_a_2078_;
v_a_1817_ = v_a_2097_;
goto v___jp_1806_;
}
}
else
{
lean_object* v_a_2098_; 
lean_dec(v_a_2078_);
lean_dec(v_val_2076_);
lean_dec(v_val_2073_);
v_a_2098_ = lean_ctor_get(v___x_2079_, 0);
lean_inc(v_a_2098_);
lean_dec_ref(v___x_2079_);
v___y_1754_ = v___x_2070_;
v___y_1755_ = v_a_2029_;
v___y_1756_ = v___y_2022_;
v___y_1757_ = v___y_2023_;
v___y_1758_ = v___y_2024_;
v___y_1759_ = v___y_2025_;
v___y_1760_ = v___y_2026_;
v___y_1761_ = v___y_2027_;
v_a_1762_ = v_a_2098_;
goto v___jp_1753_;
}
}
else
{
lean_object* v_a_2099_; 
lean_dec(v_val_2076_);
lean_dec(v_val_2073_);
v_a_2099_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_a_2099_);
lean_dec_ref(v___x_2077_);
v___y_1754_ = v___x_2070_;
v___y_1755_ = v_a_2029_;
v___y_1756_ = v___y_2022_;
v___y_1757_ = v___y_2023_;
v___y_1758_ = v___y_2024_;
v___y_1759_ = v___y_2025_;
v___y_1760_ = v___y_2026_;
v___y_1761_ = v___y_2027_;
v_a_1762_ = v_a_2099_;
goto v___jp_1753_;
}
}
else
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v_a_2102_; 
lean_dec(v_a_2075_);
lean_dec(v_val_2073_);
v___x_2100_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2101_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2100_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v_a_2102_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_a_2102_);
lean_dec_ref(v___x_2101_);
v___y_1754_ = v___x_2070_;
v___y_1755_ = v_a_2029_;
v___y_1756_ = v___y_2022_;
v___y_1757_ = v___y_2023_;
v___y_1758_ = v___y_2024_;
v___y_1759_ = v___y_2025_;
v___y_1760_ = v___y_2026_;
v___y_1761_ = v___y_2027_;
v_a_1762_ = v_a_2102_;
goto v___jp_1753_;
}
}
else
{
lean_object* v_a_2103_; 
lean_dec(v_val_2073_);
v_a_2103_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2103_);
lean_dec_ref(v___x_2074_);
v___y_1754_ = v___x_2070_;
v___y_1755_ = v_a_2029_;
v___y_1756_ = v___y_2022_;
v___y_1757_ = v___y_2023_;
v___y_1758_ = v___y_2024_;
v___y_1759_ = v___y_2025_;
v___y_1760_ = v___y_2026_;
v___y_1761_ = v___y_2027_;
v_a_1762_ = v_a_2103_;
goto v___jp_1753_;
}
}
else
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v_a_2106_; 
lean_dec(v_a_2072_);
v___x_2104_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2105_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2104_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref(v___x_2105_);
v___y_1754_ = v___x_2070_;
v___y_1755_ = v_a_2029_;
v___y_1756_ = v___y_2022_;
v___y_1757_ = v___y_2023_;
v___y_1758_ = v___y_2024_;
v___y_1759_ = v___y_2025_;
v___y_1760_ = v___y_2026_;
v___y_1761_ = v___y_2027_;
v_a_1762_ = v_a_2106_;
goto v___jp_1753_;
}
}
else
{
lean_object* v_a_2107_; 
v_a_2107_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2107_);
lean_dec_ref(v___x_2071_);
v___y_1754_ = v___x_2070_;
v___y_1755_ = v_a_2029_;
v___y_1756_ = v___y_2022_;
v___y_1757_ = v___y_2023_;
v___y_1758_ = v___y_2024_;
v___y_1759_ = v___y_2025_;
v___y_1760_ = v___y_2026_;
v___y_1761_ = v___y_2027_;
v_a_1762_ = v_a_2107_;
goto v___jp_1753_;
}
}
}
v___jp_2108_:
{
if (v___y_2111_ == 0)
{
lean_object* v___x_2112_; 
lean_dec_ref(v___y_2109_);
v___x_2112_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1501_);
if (lean_obj_tag(v___x_2112_) == 1)
{
lean_object* v_val_2113_; lean_object* v_snd_2114_; lean_object* v___x_2115_; 
v_val_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_val_2113_);
lean_dec_ref(v___x_2112_);
v_snd_2114_ = lean_ctor_get(v_val_2113_, 1);
lean_inc(v_snd_2114_);
lean_dec(v_val_2113_);
v___x_2115_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1499_, v_a_1290_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v_a_2116_; 
v_a_2116_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref(v___x_2115_);
if (lean_obj_tag(v_a_2116_) == 1)
{
lean_object* v_val_2117_; lean_object* v___x_2118_; 
v_val_2117_ = lean_ctor_get(v_a_2116_, 0);
lean_inc(v_val_2117_);
lean_dec_ref(v_a_2116_);
lean_inc(v_a_1290_);
lean_inc_ref(v_a_1289_);
lean_inc(v_a_1288_);
lean_inc_ref(v_a_1287_);
v___x_2118_ = lean_infer_type(v_val_2117_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2120_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref(v___x_2118_);
v___x_2120_ = l_Lean_Meta_mkNumeral(v_a_2119_, v_snd_2114_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2122_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref(v___x_2120_);
v___x_2122_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2121_, v_binderType_1515_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v___x_2124_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref(v___x_2122_);
lean_inc_ref(v_arg_1501_);
v___x_2124_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1501_, v_a_2123_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref(v___x_2124_);
if (lean_obj_tag(v_a_2125_) == 1)
{
lean_object* v_val_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v_val_2126_ = lean_ctor_get(v_a_2125_, 0);
lean_inc(v_val_2126_);
lean_dec_ref(v_a_2125_);
v___x_2127_ = lean_box(0);
lean_inc_ref(v_fn_1500_);
v___x_2128_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2128_, 0, v_fn_1500_);
lean_ctor_set(v___x_2128_, 1, v___x_2127_);
lean_ctor_set_uint8(v___x_2128_, sizeof(void*)*2, v___y_2110_);
v___x_2129_ = l_Lean_Meta_Simp_mkCongr(v___x_2128_, v_val_2126_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2131_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref(v___x_2129_);
lean_inc_ref(v_arg_1499_);
v___x_2131_ = l_Lean_Meta_Simp_mkCongrFun(v_a_2130_, v_arg_1499_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_dec_ref(v_expr_1286_);
return v___x_2131_;
}
else
{
lean_object* v_a_2132_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref(v___x_2131_);
v___y_1301_ = v___y_2110_;
v_a_1302_ = v_a_2132_;
goto v___jp_1300_;
}
}
else
{
lean_object* v_a_2133_; 
v_a_2133_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2133_);
lean_dec_ref(v___x_2129_);
v___y_1301_ = v___y_2110_;
v_a_1302_ = v_a_2133_;
goto v___jp_1300_;
}
}
else
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v_a_2136_; 
lean_dec(v_a_2125_);
v___x_2134_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2135_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2134_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v_a_2136_ = lean_ctor_get(v___x_2135_, 0);
lean_inc(v_a_2136_);
lean_dec_ref(v___x_2135_);
v___y_1301_ = v___y_2110_;
v_a_1302_ = v_a_2136_;
goto v___jp_1300_;
}
}
else
{
lean_object* v_a_2137_; 
v_a_2137_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2137_);
lean_dec_ref(v___x_2124_);
v___y_1301_ = v___y_2110_;
v_a_1302_ = v_a_2137_;
goto v___jp_1300_;
}
}
else
{
lean_object* v_a_2138_; 
v_a_2138_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2138_);
lean_dec_ref(v___x_2122_);
v___y_1301_ = v___y_2110_;
v_a_1302_ = v_a_2138_;
goto v___jp_1300_;
}
}
else
{
lean_object* v_a_2139_; 
lean_dec_ref(v_binderType_1515_);
v_a_2139_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2139_);
lean_dec_ref(v___x_2120_);
v___y_1301_ = v___y_2110_;
v_a_1302_ = v_a_2139_;
goto v___jp_1300_;
}
}
else
{
lean_object* v_a_2140_; 
lean_dec(v_snd_2114_);
lean_dec_ref(v_binderType_1515_);
v_a_2140_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2140_);
lean_dec_ref(v___x_2118_);
v___y_1301_ = v___y_2110_;
v_a_1302_ = v_a_2140_;
goto v___jp_1300_;
}
}
else
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v_a_2143_; 
lean_dec(v_a_2116_);
lean_dec(v_snd_2114_);
lean_dec_ref(v_binderType_1515_);
v___x_2141_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2142_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2141_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref(v___x_2142_);
v___y_1301_ = v___y_2110_;
v_a_1302_ = v_a_2143_;
goto v___jp_1300_;
}
}
else
{
lean_object* v_a_2144_; 
lean_dec(v_snd_2114_);
lean_dec_ref(v_binderType_1515_);
v_a_2144_ = lean_ctor_get(v___x_2115_, 0);
lean_inc(v_a_2144_);
lean_dec_ref(v___x_2115_);
v___y_1301_ = v___y_2110_;
v_a_1302_ = v_a_2144_;
goto v___jp_1300_;
}
}
else
{
lean_object* v___x_2145_; 
lean_dec_ref(v_binderType_1515_);
v___x_2145_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_2112_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
lean_dec(v___x_2112_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; 
lean_dec_ref(v_expr_1286_);
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2146_);
lean_dec_ref(v___x_2145_);
v_a_1474_ = v_a_2146_;
goto v___jp_1473_;
}
else
{
lean_object* v_a_2147_; 
v_a_2147_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2147_);
lean_dec_ref(v___x_2145_);
v___y_1301_ = v___y_2110_;
v_a_1302_ = v_a_2147_;
goto v___jp_1300_;
}
}
}
else
{
lean_object* v___x_2148_; 
lean_dec_ref(v_binderType_1515_);
lean_dec_ref(v_expr_1286_);
v___x_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2148_, 0, v___y_2109_);
return v___x_2148_;
}
}
v___jp_2149_:
{
uint8_t v___x_2152_; 
v___x_2152_ = l_Lean_Exception_isInterrupt(v_a_2151_);
if (v___x_2152_ == 0)
{
uint8_t v___x_2153_; 
lean_inc_ref(v_a_2151_);
v___x_2153_ = l_Lean_Exception_isRuntime(v_a_2151_);
v___y_2109_ = v_a_2151_;
v___y_2110_ = v___y_2150_;
v___y_2111_ = v___x_2153_;
goto v___jp_2108_;
}
else
{
v___y_2109_ = v_a_2151_;
v___y_2110_ = v___y_2150_;
v___y_2111_ = v___x_2152_;
goto v___jp_2108_;
}
}
v___jp_2154_:
{
if (v___y_2157_ == 0)
{
lean_object* v___x_2158_; 
lean_dec_ref(v___y_2155_);
v___x_2158_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1499_);
if (lean_obj_tag(v___x_2158_) == 1)
{
lean_object* v_val_2159_; lean_object* v_snd_2160_; lean_object* v___x_2161_; 
v_val_2159_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_val_2159_);
lean_dec_ref(v___x_2158_);
v_snd_2160_ = lean_ctor_get(v_val_2159_, 1);
lean_inc(v_snd_2160_);
lean_dec(v_val_2159_);
v___x_2161_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1501_, v_a_1290_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v_a_2162_; 
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc(v_a_2162_);
lean_dec_ref(v___x_2161_);
if (lean_obj_tag(v_a_2162_) == 1)
{
lean_object* v_val_2163_; lean_object* v___x_2164_; 
v_val_2163_ = lean_ctor_get(v_a_2162_, 0);
lean_inc(v_val_2163_);
lean_dec_ref(v_a_2162_);
lean_inc(v_a_1290_);
lean_inc_ref(v_a_1289_);
lean_inc(v_a_1288_);
lean_inc_ref(v_a_1287_);
v___x_2164_ = lean_infer_type(v_val_2163_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; lean_object* v___x_2166_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2165_);
lean_dec_ref(v___x_2164_);
v___x_2166_ = l_Lean_Meta_mkNumeral(v_a_2165_, v_snd_2160_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; lean_object* v___x_2168_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_a_2167_);
lean_dec_ref(v___x_2166_);
lean_inc_ref(v_binderType_1515_);
v___x_2168_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2167_, v_binderType_1515_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; lean_object* v___x_2170_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2169_);
lean_dec_ref(v___x_2168_);
lean_inc_ref(v_arg_1499_);
v___x_2170_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1499_, v_a_2169_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref(v___x_2170_);
if (lean_obj_tag(v_a_2171_) == 1)
{
lean_object* v_val_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v_val_2172_ = lean_ctor_get(v_a_2171_, 0);
lean_inc(v_val_2172_);
lean_dec_ref(v_a_2171_);
lean_inc_ref(v_arg_1501_);
lean_inc_ref(v_fn_1500_);
v___x_2173_ = l_Lean_Expr_app___override(v_fn_1500_, v_arg_1501_);
v___x_2174_ = lean_box(0);
v___x_2175_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2175_, 0, v___x_2173_);
lean_ctor_set(v___x_2175_, 1, v___x_2174_);
lean_ctor_set_uint8(v___x_2175_, sizeof(void*)*2, v___y_2156_);
v___x_2176_ = l_Lean_Meta_Simp_mkCongr(v___x_2175_, v_val_2172_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_dec_ref(v_binderType_1515_);
lean_dec_ref(v_expr_1286_);
return v___x_2176_;
}
else
{
lean_object* v_a_2177_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref(v___x_2176_);
v___y_2150_ = v___y_2156_;
v_a_2151_ = v_a_2177_;
goto v___jp_2149_;
}
}
else
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v_a_2180_; 
lean_dec(v_a_2171_);
v___x_2178_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2179_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2178_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
lean_dec_ref(v___x_2179_);
v___y_2150_ = v___y_2156_;
v_a_2151_ = v_a_2180_;
goto v___jp_2149_;
}
}
else
{
lean_object* v_a_2181_; 
v_a_2181_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2181_);
lean_dec_ref(v___x_2170_);
v___y_2150_ = v___y_2156_;
v_a_2151_ = v_a_2181_;
goto v___jp_2149_;
}
}
else
{
lean_object* v_a_2182_; 
v_a_2182_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2182_);
lean_dec_ref(v___x_2168_);
v___y_2150_ = v___y_2156_;
v_a_2151_ = v_a_2182_;
goto v___jp_2149_;
}
}
else
{
lean_object* v_a_2183_; 
v_a_2183_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_a_2183_);
lean_dec_ref(v___x_2166_);
v___y_2150_ = v___y_2156_;
v_a_2151_ = v_a_2183_;
goto v___jp_2149_;
}
}
else
{
lean_object* v_a_2184_; 
lean_dec(v_snd_2160_);
v_a_2184_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2184_);
lean_dec_ref(v___x_2164_);
v___y_2150_ = v___y_2156_;
v_a_2151_ = v_a_2184_;
goto v___jp_2149_;
}
}
else
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v_a_2187_; 
lean_dec(v_a_2162_);
lean_dec(v_snd_2160_);
v___x_2185_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2186_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2185_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2187_);
lean_dec_ref(v___x_2186_);
v___y_2150_ = v___y_2156_;
v_a_2151_ = v_a_2187_;
goto v___jp_2149_;
}
}
else
{
lean_object* v_a_2188_; 
lean_dec(v_snd_2160_);
v_a_2188_ = lean_ctor_get(v___x_2161_, 0);
lean_inc(v_a_2188_);
lean_dec_ref(v___x_2161_);
v___y_2150_ = v___y_2156_;
v_a_2151_ = v_a_2188_;
goto v___jp_2149_;
}
}
else
{
lean_object* v___x_2189_; 
v___x_2189_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_2158_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
lean_dec(v___x_2158_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; 
lean_dec_ref(v_binderType_1515_);
lean_dec_ref(v_expr_1286_);
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2190_);
lean_dec_ref(v___x_2189_);
v_a_1474_ = v_a_2190_;
goto v___jp_1473_;
}
else
{
lean_object* v_a_2191_; 
v_a_2191_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2191_);
lean_dec_ref(v___x_2189_);
v___y_2150_ = v___y_2156_;
v_a_2151_ = v_a_2191_;
goto v___jp_2149_;
}
}
}
else
{
lean_object* v___x_2192_; 
lean_dec_ref(v_binderType_1515_);
lean_dec_ref(v_expr_1286_);
v___x_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2192_, 0, v___y_2155_);
return v___x_2192_;
}
}
v___jp_2193_:
{
uint8_t v___x_2196_; 
v___x_2196_ = l_Lean_Exception_isInterrupt(v_a_2195_);
if (v___x_2196_ == 0)
{
uint8_t v___x_2197_; 
lean_inc_ref(v_a_2195_);
v___x_2197_ = l_Lean_Exception_isRuntime(v_a_2195_);
v___y_2155_ = v_a_2195_;
v___y_2156_ = v___y_2194_;
v___y_2157_ = v___x_2197_;
goto v___jp_2154_;
}
else
{
v___y_2155_ = v_a_2195_;
v___y_2156_ = v___y_2194_;
v___y_2157_ = v___x_2196_;
goto v___jp_2154_;
}
}
v___jp_2198_:
{
if (lean_obj_tag(v___y_2200_) == 0)
{
lean_dec_ref(v_binderType_1515_);
lean_dec_ref(v_expr_1286_);
return v___y_2200_;
}
else
{
lean_object* v_a_2201_; 
v_a_2201_ = lean_ctor_get(v___y_2200_, 0);
lean_inc(v_a_2201_);
lean_dec_ref(v___y_2200_);
v___y_2194_ = v___y_2199_;
v_a_2195_ = v_a_2201_;
goto v___jp_2193_;
}
}
v___jp_2202_:
{
if (v___y_2207_ == 0)
{
lean_object* v___x_2208_; 
lean_dec_ref(v___y_2206_);
v___x_2208_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v___y_2203_, v___y_2205_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; lean_object* v___x_2210_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2209_);
lean_dec_ref(v___x_2208_);
lean_inc_ref(v_binderType_1515_);
v___x_2210_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2209_, v_binderType_1515_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; lean_object* v___x_2212_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_a_2211_);
lean_dec_ref(v___x_2210_);
lean_inc_ref(v_arg_1499_);
v___x_2212_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1499_, v_a_2211_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2213_);
lean_dec_ref(v___x_2212_);
if (lean_obj_tag(v_a_2213_) == 1)
{
lean_object* v_val_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v_val_2214_ = lean_ctor_get(v_a_2213_, 0);
lean_inc(v_val_2214_);
lean_dec_ref(v_a_2213_);
lean_inc_ref(v_arg_1501_);
lean_inc_ref(v_fn_1500_);
v___x_2215_ = l_Lean_Expr_app___override(v_fn_1500_, v_arg_1501_);
v___x_2216_ = lean_box(0);
v___x_2217_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2217_, 0, v___x_2215_);
lean_ctor_set(v___x_2217_, 1, v___x_2216_);
lean_ctor_set_uint8(v___x_2217_, sizeof(void*)*2, v___y_2204_);
v___x_2218_ = l_Lean_Meta_Simp_mkCongr(v___x_2217_, v_val_2214_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v___y_2199_ = v___y_2204_;
v___y_2200_ = v___x_2218_;
goto v___jp_2198_;
}
else
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
lean_dec(v_a_2213_);
v___x_2219_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2220_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2219_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v___y_2199_ = v___y_2204_;
v___y_2200_ = v___x_2220_;
goto v___jp_2198_;
}
}
else
{
lean_object* v_a_2221_; 
v_a_2221_ = lean_ctor_get(v___x_2212_, 0);
lean_inc(v_a_2221_);
lean_dec_ref(v___x_2212_);
v___y_2194_ = v___y_2204_;
v_a_2195_ = v_a_2221_;
goto v___jp_2193_;
}
}
else
{
lean_object* v_a_2222_; 
v_a_2222_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_a_2222_);
lean_dec_ref(v___x_2210_);
v___y_2194_ = v___y_2204_;
v_a_2195_ = v_a_2222_;
goto v___jp_2193_;
}
}
else
{
lean_object* v_a_2223_; 
v_a_2223_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2223_);
lean_dec_ref(v___x_2208_);
v___y_2194_ = v___y_2204_;
v_a_2195_ = v_a_2223_;
goto v___jp_2193_;
}
}
else
{
lean_dec_ref(v___y_2205_);
lean_dec_ref(v___y_2203_);
v___y_2194_ = v___y_2204_;
v_a_2195_ = v___y_2206_;
goto v___jp_2193_;
}
}
v___jp_2224_:
{
uint8_t v___x_2229_; 
v___x_2229_ = l_Lean_Exception_isInterrupt(v_a_2228_);
if (v___x_2229_ == 0)
{
uint8_t v___x_2230_; 
lean_inc_ref(v_a_2228_);
v___x_2230_ = l_Lean_Exception_isRuntime(v_a_2228_);
v___y_2203_ = v___y_2225_;
v___y_2204_ = v___y_2226_;
v___y_2205_ = v___y_2227_;
v___y_2206_ = v_a_2228_;
v___y_2207_ = v___x_2230_;
goto v___jp_2202_;
}
else
{
v___y_2203_ = v___y_2225_;
v___y_2204_ = v___y_2226_;
v___y_2205_ = v___y_2227_;
v___y_2206_ = v_a_2228_;
v___y_2207_ = v___x_2229_;
goto v___jp_2202_;
}
}
v___jp_2231_:
{
if (lean_obj_tag(v___y_2235_) == 0)
{
lean_dec_ref(v___y_2234_);
lean_dec_ref(v___y_2232_);
lean_dec_ref(v_binderType_1515_);
lean_dec_ref(v_expr_1286_);
return v___y_2235_;
}
else
{
lean_object* v_a_2236_; 
v_a_2236_ = lean_ctor_get(v___y_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref(v___y_2235_);
v___y_2225_ = v___y_2232_;
v___y_2226_ = v___y_2233_;
v___y_2227_ = v___y_2234_;
v_a_2228_ = v_a_2236_;
goto v___jp_2224_;
}
}
v___jp_2237_:
{
uint8_t v___x_2239_; 
v___x_2239_ = 1;
if (v___y_2238_ == 0)
{
lean_object* v___x_2240_; 
lean_inc_ref(v_binderType_1515_);
v___x_2240_ = l_Lean_Meta_isExprDefEq(v_binderType_1515_, v_binderType_1516_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v___x_2243_; uint8_t v_isShared_2244_; uint8_t v_isSharedCheck_2340_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2243_ = v___x_2240_;
v_isShared_2244_ = v_isSharedCheck_2340_;
goto v_resetjp_2242_;
}
else
{
lean_inc(v_a_2241_);
lean_dec(v___x_2240_);
v___x_2243_ = lean_box(0);
v_isShared_2244_ = v_isSharedCheck_2340_;
goto v_resetjp_2242_;
}
v_resetjp_2242_:
{
uint8_t v___x_2245_; 
v___x_2245_ = lean_unbox(v_a_2241_);
lean_dec(v_a_2241_);
if (v___x_2245_ == 0)
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2249_; 
lean_dec_ref(v_binderType_1515_);
v___x_2246_ = lean_box(0);
v___x_2247_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2247_, 0, v_expr_1286_);
lean_ctor_set(v___x_2247_, 1, v___x_2246_);
lean_ctor_set_uint8(v___x_2247_, sizeof(void*)*2, v___x_2239_);
if (v_isShared_2244_ == 0)
{
lean_ctor_set(v___x_2243_, 0, v___x_2247_);
v___x_2249_ = v___x_2243_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v___x_2247_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
else
{
lean_object* v_options_2251_; uint8_t v_hasTrace_2252_; 
lean_del_object(v___x_2243_);
v_options_2251_ = lean_ctor_get(v_a_1289_, 2);
v_hasTrace_2252_ = lean_ctor_get_uint8(v_options_2251_, sizeof(void*)*1);
if (v_hasTrace_2252_ == 0)
{
lean_object* v___x_2253_; 
v___x_2253_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1501_, v_a_1290_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_a_2254_);
lean_dec_ref(v___x_2253_);
if (lean_obj_tag(v_a_2254_) == 1)
{
lean_object* v_val_2255_; lean_object* v___x_2256_; 
v_val_2255_ = lean_ctor_get(v_a_2254_, 0);
lean_inc(v_val_2255_);
lean_dec_ref(v_a_2254_);
v___x_2256_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1499_, v_a_1290_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_a_2257_);
lean_dec_ref(v___x_2256_);
if (lean_obj_tag(v_a_2257_) == 1)
{
lean_object* v_val_2258_; lean_object* v___x_2259_; 
v_val_2258_ = lean_ctor_get(v_a_2257_, 0);
lean_inc(v_val_2258_);
lean_dec_ref(v_a_2257_);
lean_inc(v_a_1290_);
lean_inc_ref(v_a_1289_);
lean_inc(v_a_1288_);
lean_inc_ref(v_a_1287_);
lean_inc(v_val_2255_);
v___x_2259_ = lean_infer_type(v_val_2255_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; lean_object* v___x_2261_; 
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_a_2260_);
lean_dec_ref(v___x_2259_);
lean_inc(v_a_1290_);
lean_inc_ref(v_a_1289_);
lean_inc(v_a_1288_);
lean_inc_ref(v_a_1287_);
lean_inc(v_val_2258_);
v___x_2261_ = lean_infer_type(v_val_2258_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; lean_object* v___x_2263_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_a_2262_);
lean_dec_ref(v___x_2261_);
v___x_2263_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_val_2255_, v_a_2262_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_a_2264_; lean_object* v___x_2265_; 
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_a_2264_);
lean_dec_ref(v___x_2263_);
lean_inc_ref(v_binderType_1515_);
v___x_2265_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2264_, v_binderType_1515_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v___x_2267_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2266_);
lean_dec_ref(v___x_2265_);
lean_inc_ref(v_arg_1501_);
v___x_2267_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1501_, v_a_2266_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v_a_2268_; 
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_a_2268_);
lean_dec_ref(v___x_2267_);
if (lean_obj_tag(v_a_2268_) == 1)
{
lean_object* v_val_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v_val_2269_ = lean_ctor_get(v_a_2268_, 0);
lean_inc(v_val_2269_);
lean_dec_ref(v_a_2268_);
v___x_2270_ = lean_box(0);
lean_inc_ref(v_fn_1500_);
v___x_2271_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2271_, 0, v_fn_1500_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
lean_ctor_set_uint8(v___x_2271_, sizeof(void*)*2, v___x_2239_);
v___x_2272_ = l_Lean_Meta_Simp_mkCongr(v___x_2271_, v_val_2269_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; lean_object* v___x_2274_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_a_2273_);
lean_dec_ref(v___x_2272_);
lean_inc_ref(v_arg_1499_);
v___x_2274_ = l_Lean_Meta_Simp_mkCongrFun(v_a_2273_, v_arg_1499_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v___y_1642_ = v_val_2258_;
v___y_1643_ = v___x_2239_;
v___y_1644_ = v_a_2260_;
v___y_1645_ = v___x_2274_;
goto v___jp_1641_;
}
else
{
v___y_1642_ = v_val_2258_;
v___y_1643_ = v___x_2239_;
v___y_1644_ = v_a_2260_;
v___y_1645_ = v___x_2272_;
goto v___jp_1641_;
}
}
else
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
lean_dec(v_a_2268_);
v___x_2275_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2276_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2275_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v___y_1642_ = v_val_2258_;
v___y_1643_ = v___x_2239_;
v___y_1644_ = v_a_2260_;
v___y_1645_ = v___x_2276_;
goto v___jp_1641_;
}
}
else
{
lean_object* v_a_2277_; 
v_a_2277_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_a_2277_);
lean_dec_ref(v___x_2267_);
v___y_1635_ = v_val_2258_;
v___y_1636_ = v___x_2239_;
v___y_1637_ = v_a_2260_;
v_a_1638_ = v_a_2277_;
goto v___jp_1634_;
}
}
else
{
lean_object* v_a_2278_; 
v_a_2278_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2278_);
lean_dec_ref(v___x_2265_);
v___y_1635_ = v_val_2258_;
v___y_1636_ = v___x_2239_;
v___y_1637_ = v_a_2260_;
v_a_1638_ = v_a_2278_;
goto v___jp_1634_;
}
}
else
{
lean_object* v_a_2279_; 
v_a_2279_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_a_2279_);
lean_dec_ref(v___x_2263_);
v___y_1635_ = v_val_2258_;
v___y_1636_ = v___x_2239_;
v___y_1637_ = v_a_2260_;
v_a_1638_ = v_a_2279_;
goto v___jp_1634_;
}
}
else
{
lean_object* v_a_2280_; 
lean_dec(v_a_2260_);
lean_dec(v_val_2258_);
lean_dec(v_val_2255_);
v_a_2280_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_a_2280_);
lean_dec_ref(v___x_2261_);
v___y_1604_ = v___x_2239_;
v_a_1605_ = v_a_2280_;
goto v___jp_1603_;
}
}
else
{
lean_object* v_a_2281_; 
lean_dec(v_val_2258_);
lean_dec(v_val_2255_);
v_a_2281_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_a_2281_);
lean_dec_ref(v___x_2259_);
v___y_1604_ = v___x_2239_;
v_a_1605_ = v_a_2281_;
goto v___jp_1603_;
}
}
else
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v_a_2284_; 
lean_dec(v_a_2257_);
lean_dec(v_val_2255_);
v___x_2282_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2283_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2282_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_a_2284_);
lean_dec_ref(v___x_2283_);
v___y_1604_ = v___x_2239_;
v_a_1605_ = v_a_2284_;
goto v___jp_1603_;
}
}
else
{
lean_object* v_a_2285_; 
lean_dec(v_val_2255_);
v_a_2285_ = lean_ctor_get(v___x_2256_, 0);
lean_inc(v_a_2285_);
lean_dec_ref(v___x_2256_);
v___y_1604_ = v___x_2239_;
v_a_1605_ = v_a_2285_;
goto v___jp_1603_;
}
}
else
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v_a_2288_; 
lean_dec(v_a_2254_);
v___x_2286_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2287_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref(v___x_2287_);
v___y_1604_ = v___x_2239_;
v_a_1605_ = v_a_2288_;
goto v___jp_1603_;
}
}
else
{
lean_object* v_a_2289_; 
v_a_2289_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_a_2289_);
lean_dec_ref(v___x_2253_);
v___y_1604_ = v___x_2239_;
v_a_1605_ = v_a_2289_;
goto v___jp_1603_;
}
}
else
{
lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v_a_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___f_2296_; lean_object* v___x_2297_; uint8_t v___x_2298_; 
v___x_2290_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__2_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_));
v___x_2291_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___x_2290_, v_a_1289_);
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_a_2292_);
lean_dec_ref(v___x_2291_);
v___x_2293_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_splittingProcedure___closed__1, &l_Lean_Elab_Tactic_NormCast_splittingProcedure___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___closed__1);
lean_inc_ref(v_expr_1286_);
v___x_2294_ = l_Lean_MessageData_ofExpr(v_expr_1286_);
v___x_2295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2293_);
lean_ctor_set(v___x_2295_, 1, v___x_2294_);
lean_inc_ref(v_expr_1286_);
v___f_2296_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___boxed), 8, 2);
lean_closure_set(v___f_2296_, 0, v___x_2295_);
lean_closure_set(v___f_2296_, 1, v_expr_1286_);
v___x_2297_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_2298_ = lean_unbox(v_a_2292_);
if (v___x_2298_ == 0)
{
lean_object* v___x_2299_; uint8_t v___x_2300_; 
v___x_2299_ = l_Lean_trace_profiler;
v___x_2300_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_2251_, v___x_2299_);
if (v___x_2300_ == 0)
{
lean_object* v___x_2301_; 
lean_dec_ref(v___f_2296_);
lean_dec(v_a_2292_);
v___x_2301_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1501_, v_a_1290_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2302_);
lean_dec_ref(v___x_2301_);
if (lean_obj_tag(v_a_2302_) == 1)
{
lean_object* v_val_2303_; lean_object* v___x_2304_; 
v_val_2303_ = lean_ctor_get(v_a_2302_, 0);
lean_inc(v_val_2303_);
lean_dec_ref(v_a_2302_);
v___x_2304_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1499_, v_a_1290_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_object* v_a_2305_; 
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2305_);
lean_dec_ref(v___x_2304_);
if (lean_obj_tag(v_a_2305_) == 1)
{
lean_object* v_val_2306_; lean_object* v___x_2307_; 
v_val_2306_ = lean_ctor_get(v_a_2305_, 0);
lean_inc(v_val_2306_);
lean_dec_ref(v_a_2305_);
lean_inc(v_a_1290_);
lean_inc_ref(v_a_1289_);
lean_inc(v_a_1288_);
lean_inc_ref(v_a_1287_);
lean_inc(v_val_2303_);
v___x_2307_ = lean_infer_type(v_val_2303_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_object* v_a_2308_; lean_object* v___x_2309_; 
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2308_);
lean_dec_ref(v___x_2307_);
lean_inc(v_a_1290_);
lean_inc_ref(v_a_1289_);
lean_inc(v_a_1288_);
lean_inc_ref(v_a_1287_);
lean_inc(v_val_2306_);
v___x_2309_ = lean_infer_type(v_val_2306_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v___x_2311_; 
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2310_);
lean_dec_ref(v___x_2309_);
v___x_2311_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_val_2303_, v_a_2310_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2313_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
lean_dec_ref(v___x_2311_);
lean_inc_ref(v_binderType_1515_);
v___x_2313_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2312_, v_binderType_1515_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; lean_object* v___x_2315_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2314_);
lean_dec_ref(v___x_2313_);
lean_inc_ref(v_arg_1501_);
v___x_2315_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1501_, v_a_2314_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref(v___x_2315_);
if (lean_obj_tag(v_a_2316_) == 1)
{
lean_object* v_val_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; 
v_val_2317_ = lean_ctor_get(v_a_2316_, 0);
lean_inc(v_val_2317_);
lean_dec_ref(v_a_2316_);
v___x_2318_ = lean_box(0);
lean_inc_ref(v_fn_1500_);
v___x_2319_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2319_, 0, v_fn_1500_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
lean_ctor_set_uint8(v___x_2319_, sizeof(void*)*2, v___x_2239_);
v___x_2320_ = l_Lean_Meta_Simp_mkCongr(v___x_2319_, v_val_2317_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v___x_2322_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref(v___x_2320_);
lean_inc_ref(v_arg_1499_);
v___x_2322_ = l_Lean_Meta_Simp_mkCongrFun(v_a_2321_, v_arg_1499_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v___y_2232_ = v_val_2306_;
v___y_2233_ = v___x_2239_;
v___y_2234_ = v_a_2308_;
v___y_2235_ = v___x_2322_;
goto v___jp_2231_;
}
else
{
v___y_2232_ = v_val_2306_;
v___y_2233_ = v___x_2239_;
v___y_2234_ = v_a_2308_;
v___y_2235_ = v___x_2320_;
goto v___jp_2231_;
}
}
else
{
lean_object* v___x_2323_; lean_object* v___x_2324_; 
lean_dec(v_a_2316_);
v___x_2323_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2324_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2323_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v___y_2232_ = v_val_2306_;
v___y_2233_ = v___x_2239_;
v___y_2234_ = v_a_2308_;
v___y_2235_ = v___x_2324_;
goto v___jp_2231_;
}
}
else
{
lean_object* v_a_2325_; 
v_a_2325_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2325_);
lean_dec_ref(v___x_2315_);
v___y_2225_ = v_val_2306_;
v___y_2226_ = v___x_2239_;
v___y_2227_ = v_a_2308_;
v_a_2228_ = v_a_2325_;
goto v___jp_2224_;
}
}
else
{
lean_object* v_a_2326_; 
v_a_2326_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2326_);
lean_dec_ref(v___x_2313_);
v___y_2225_ = v_val_2306_;
v___y_2226_ = v___x_2239_;
v___y_2227_ = v_a_2308_;
v_a_2228_ = v_a_2326_;
goto v___jp_2224_;
}
}
else
{
lean_object* v_a_2327_; 
v_a_2327_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2327_);
lean_dec_ref(v___x_2311_);
v___y_2225_ = v_val_2306_;
v___y_2226_ = v___x_2239_;
v___y_2227_ = v_a_2308_;
v_a_2228_ = v_a_2327_;
goto v___jp_2224_;
}
}
else
{
lean_object* v_a_2328_; 
lean_dec(v_a_2308_);
lean_dec(v_val_2306_);
lean_dec(v_val_2303_);
v_a_2328_ = lean_ctor_get(v___x_2309_, 0);
lean_inc(v_a_2328_);
lean_dec_ref(v___x_2309_);
v___y_2194_ = v___x_2239_;
v_a_2195_ = v_a_2328_;
goto v___jp_2193_;
}
}
else
{
lean_object* v_a_2329_; 
lean_dec(v_val_2306_);
lean_dec(v_val_2303_);
v_a_2329_ = lean_ctor_get(v___x_2307_, 0);
lean_inc(v_a_2329_);
lean_dec_ref(v___x_2307_);
v___y_2194_ = v___x_2239_;
v_a_2195_ = v_a_2329_;
goto v___jp_2193_;
}
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v_a_2332_; 
lean_dec(v_a_2305_);
lean_dec(v_val_2303_);
v___x_2330_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2331_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2330_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
lean_inc(v_a_2332_);
lean_dec_ref(v___x_2331_);
v___y_2194_ = v___x_2239_;
v_a_2195_ = v_a_2332_;
goto v___jp_2193_;
}
}
else
{
lean_object* v_a_2333_; 
lean_dec(v_val_2303_);
v_a_2333_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2333_);
lean_dec_ref(v___x_2304_);
v___y_2194_ = v___x_2239_;
v_a_2195_ = v_a_2333_;
goto v___jp_2193_;
}
}
else
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v_a_2336_; 
lean_dec(v_a_2302_);
v___x_2334_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2335_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2334_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2336_);
lean_dec_ref(v___x_2335_);
v___y_2194_ = v___x_2239_;
v_a_2195_ = v_a_2336_;
goto v___jp_2193_;
}
}
else
{
lean_object* v_a_2337_; 
v_a_2337_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2337_);
lean_dec_ref(v___x_2301_);
v___y_2194_ = v___x_2239_;
v_a_2195_ = v_a_2337_;
goto v___jp_2193_;
}
}
else
{
uint8_t v___x_2338_; 
v___x_2338_ = lean_unbox(v_a_2292_);
lean_dec(v_a_2292_);
v___y_2022_ = v___x_2290_;
v___y_2023_ = v_options_2251_;
v___y_2024_ = v___x_2297_;
v___y_2025_ = v___x_2239_;
v___y_2026_ = v___x_2338_;
v___y_2027_ = v___f_2296_;
goto v___jp_2021_;
}
}
else
{
uint8_t v___x_2339_; 
v___x_2339_ = lean_unbox(v_a_2292_);
lean_dec(v_a_2292_);
v___y_2022_ = v___x_2290_;
v___y_2023_ = v_options_2251_;
v___y_2024_ = v___x_2297_;
v___y_2025_ = v___x_2239_;
v___y_2026_ = v___x_2339_;
v___y_2027_ = v___f_2296_;
goto v___jp_2021_;
}
}
}
}
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_dec_ref(v_binderType_1515_);
lean_dec_ref(v_expr_1286_);
v_a_2341_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2240_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2240_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
else
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
lean_dec_ref(v_binderType_1516_);
lean_dec_ref(v_binderType_1515_);
v___x_2349_ = lean_box(0);
v___x_2350_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2350_, 0, v_expr_1286_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
lean_ctor_set_uint8(v___x_2350_, sizeof(void*)*2, v___x_2239_);
v___x_2351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2350_);
return v___x_2351_;
}
}
}
else
{
lean_dec_ref(v_body_1514_);
lean_dec_ref(v_a_1503_);
goto v___jp_1507_;
}
}
else
{
lean_dec(v_a_1503_);
goto v___jp_1507_;
}
v___jp_1507_:
{
lean_object* v___x_1508_; uint8_t v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1508_ = lean_box(0);
v___x_1509_ = 1;
v___x_1510_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1510_, 0, v_expr_1286_);
lean_ctor_set(v___x_1510_, 1, v___x_1508_);
lean_ctor_set_uint8(v___x_1510_, sizeof(void*)*2, v___x_1509_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 0, v___x_1510_);
v___x_1512_ = v___x_1505_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1513_; 
v_reuseFailAlloc_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1513_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
return v___x_1512_;
}
}
}
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_dec_ref(v_expr_1286_);
v_a_2355_ = lean_ctor_get(v___x_1502_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_1502_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_1502_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_1502_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
else
{
goto v___jp_1493_;
}
}
else
{
goto v___jp_1493_;
}
v___jp_1292_:
{
if (v___y_1295_ == 0)
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
lean_dec_ref(v___y_1293_);
v___x_1296_ = lean_box(0);
v___x_1297_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1297_, 0, v_expr_1286_);
lean_ctor_set(v___x_1297_, 1, v___x_1296_);
lean_ctor_set_uint8(v___x_1297_, sizeof(void*)*2, v___y_1294_);
v___x_1298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1297_);
return v___x_1298_;
}
else
{
lean_object* v___x_1299_; 
lean_dec_ref(v_expr_1286_);
v___x_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1299_, 0, v___y_1293_);
return v___x_1299_;
}
}
v___jp_1300_:
{
uint8_t v___x_1303_; 
v___x_1303_ = l_Lean_Exception_isInterrupt(v_a_1302_);
if (v___x_1303_ == 0)
{
uint8_t v___x_1304_; 
lean_inc_ref(v_a_1302_);
v___x_1304_ = l_Lean_Exception_isRuntime(v_a_1302_);
v___y_1293_ = v_a_1302_;
v___y_1294_ = v___y_1301_;
v___y_1295_ = v___x_1304_;
goto v___jp_1292_;
}
else
{
v___y_1293_ = v_a_1302_;
v___y_1294_ = v___y_1301_;
v___y_1295_ = v___x_1303_;
goto v___jp_1292_;
}
}
v___jp_1305_:
{
if (v___y_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
lean_dec_ref(v___y_1307_);
v___x_1309_ = lean_box(0);
v___x_1310_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1310_, 0, v_expr_1286_);
lean_ctor_set(v___x_1310_, 1, v___x_1309_);
lean_ctor_set_uint8(v___x_1310_, sizeof(void*)*2, v___y_1306_);
v___x_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
return v___x_1311_;
}
else
{
lean_object* v___x_1312_; 
lean_dec_ref(v_expr_1286_);
v___x_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1312_, 0, v___y_1307_);
return v___x_1312_;
}
}
v___jp_1313_:
{
uint8_t v___x_1316_; 
v___x_1316_ = l_Lean_Exception_isInterrupt(v_a_1315_);
if (v___x_1316_ == 0)
{
uint8_t v___x_1317_; 
lean_inc_ref(v_a_1315_);
v___x_1317_ = l_Lean_Exception_isRuntime(v_a_1315_);
v___y_1306_ = v___y_1314_;
v___y_1307_ = v_a_1315_;
v___y_1308_ = v___x_1317_;
goto v___jp_1305_;
}
else
{
v___y_1306_ = v___y_1314_;
v___y_1307_ = v_a_1315_;
v___y_1308_ = v___x_1316_;
goto v___jp_1305_;
}
}
v___jp_1318_:
{
lean_object* v___x_1328_; double v___x_1329_; double v___x_1330_; double v___x_1331_; double v___x_1332_; double v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1328_ = lean_io_mono_nanos_now();
v___x_1329_ = lean_float_of_nat(v___y_1326_);
v___x_1330_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1);
v___x_1331_ = lean_float_div(v___x_1329_, v___x_1330_);
v___x_1332_ = lean_float_of_nat(v___x_1328_);
v___x_1333_ = lean_float_div(v___x_1332_, v___x_1330_);
v___x_1334_ = lean_box_float(v___x_1331_);
v___x_1335_ = lean_box_float(v___x_1333_);
v___x_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1334_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
v___x_1337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1337_, 0, v_a_1327_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
v___x_1338_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___y_1320_, v___y_1324_, v___y_1322_, v___y_1321_, v___y_1323_, v___y_1319_, v___y_1325_, v___x_1337_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
return v___x_1338_;
}
v___jp_1339_:
{
lean_object* v___x_1349_; 
v___x_1349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1349_, 0, v_a_1348_);
v___y_1319_ = v___y_1340_;
v___y_1320_ = v___y_1341_;
v___y_1321_ = v___y_1342_;
v___y_1322_ = v___y_1343_;
v___y_1323_ = v___y_1345_;
v___y_1324_ = v___y_1344_;
v___y_1325_ = v___y_1346_;
v___y_1326_ = v___y_1347_;
v_a_1327_ = v___x_1349_;
goto v___jp_1318_;
}
v___jp_1350_:
{
lean_object* v___x_1360_; 
v___x_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1360_, 0, v_a_1359_);
v___y_1319_ = v___y_1351_;
v___y_1320_ = v___y_1352_;
v___y_1321_ = v___y_1353_;
v___y_1322_ = v___y_1354_;
v___y_1323_ = v___y_1356_;
v___y_1324_ = v___y_1355_;
v___y_1325_ = v___y_1357_;
v___y_1326_ = v___y_1358_;
v_a_1327_ = v___x_1360_;
goto v___jp_1318_;
}
v___jp_1361_:
{
if (v___y_1371_ == 0)
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
lean_dec_ref(v___y_1362_);
v___x_1372_ = lean_box(0);
v___x_1373_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1373_, 0, v_expr_1286_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*2, v___y_1368_);
v___y_1351_ = v___y_1363_;
v___y_1352_ = v___y_1364_;
v___y_1353_ = v___y_1365_;
v___y_1354_ = v___y_1366_;
v___y_1355_ = v___y_1368_;
v___y_1356_ = v___y_1367_;
v___y_1357_ = v___y_1369_;
v___y_1358_ = v___y_1370_;
v_a_1359_ = v___x_1373_;
goto v___jp_1350_;
}
else
{
lean_dec_ref(v_expr_1286_);
v___y_1340_ = v___y_1363_;
v___y_1341_ = v___y_1364_;
v___y_1342_ = v___y_1365_;
v___y_1343_ = v___y_1366_;
v___y_1344_ = v___y_1368_;
v___y_1345_ = v___y_1367_;
v___y_1346_ = v___y_1369_;
v___y_1347_ = v___y_1370_;
v_a_1348_ = v___y_1362_;
goto v___jp_1339_;
}
}
v___jp_1374_:
{
uint8_t v___x_1384_; 
v___x_1384_ = l_Lean_Exception_isInterrupt(v_a_1383_);
if (v___x_1384_ == 0)
{
uint8_t v___x_1385_; 
lean_inc_ref(v_a_1383_);
v___x_1385_ = l_Lean_Exception_isRuntime(v_a_1383_);
v___y_1362_ = v_a_1383_;
v___y_1363_ = v___y_1375_;
v___y_1364_ = v___y_1376_;
v___y_1365_ = v___y_1377_;
v___y_1366_ = v___y_1378_;
v___y_1367_ = v___y_1380_;
v___y_1368_ = v___y_1379_;
v___y_1369_ = v___y_1381_;
v___y_1370_ = v___y_1382_;
v___y_1371_ = v___x_1385_;
goto v___jp_1361_;
}
else
{
v___y_1362_ = v_a_1383_;
v___y_1363_ = v___y_1375_;
v___y_1364_ = v___y_1376_;
v___y_1365_ = v___y_1377_;
v___y_1366_ = v___y_1378_;
v___y_1367_ = v___y_1380_;
v___y_1368_ = v___y_1379_;
v___y_1369_ = v___y_1381_;
v___y_1370_ = v___y_1382_;
v___y_1371_ = v___x_1384_;
goto v___jp_1361_;
}
}
v___jp_1386_:
{
lean_object* v_a_1396_; 
v_a_1396_ = lean_ctor_get(v_a_1395_, 0);
lean_inc(v_a_1396_);
lean_dec_ref(v_a_1395_);
v___y_1351_ = v___y_1387_;
v___y_1352_ = v___y_1388_;
v___y_1353_ = v___y_1389_;
v___y_1354_ = v___y_1390_;
v___y_1355_ = v___y_1392_;
v___y_1356_ = v___y_1391_;
v___y_1357_ = v___y_1393_;
v___y_1358_ = v___y_1394_;
v_a_1359_ = v_a_1396_;
goto v___jp_1350_;
}
v___jp_1397_:
{
lean_object* v___x_1407_; double v___x_1408_; double v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1407_ = lean_io_get_num_heartbeats();
v___x_1408_ = lean_float_of_nat(v___y_1398_);
v___x_1409_ = lean_float_of_nat(v___x_1407_);
v___x_1410_ = lean_box_float(v___x_1408_);
v___x_1411_ = lean_box_float(v___x_1409_);
v___x_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1410_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
v___x_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1413_, 0, v_a_1406_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
v___x_1414_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___y_1400_, v___y_1404_, v___y_1402_, v___y_1401_, v___y_1403_, v___y_1399_, v___y_1405_, v___x_1413_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_);
return v___x_1414_;
}
v___jp_1415_:
{
lean_object* v___x_1425_; 
v___x_1425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1425_, 0, v_a_1424_);
v___y_1398_ = v___y_1416_;
v___y_1399_ = v___y_1417_;
v___y_1400_ = v___y_1418_;
v___y_1401_ = v___y_1419_;
v___y_1402_ = v___y_1420_;
v___y_1403_ = v___y_1422_;
v___y_1404_ = v___y_1421_;
v___y_1405_ = v___y_1423_;
v_a_1406_ = v___x_1425_;
goto v___jp_1397_;
}
v___jp_1426_:
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1436_, 0, v_a_1435_);
v___y_1398_ = v___y_1427_;
v___y_1399_ = v___y_1428_;
v___y_1400_ = v___y_1429_;
v___y_1401_ = v___y_1430_;
v___y_1402_ = v___y_1431_;
v___y_1403_ = v___y_1433_;
v___y_1404_ = v___y_1432_;
v___y_1405_ = v___y_1434_;
v_a_1406_ = v___x_1436_;
goto v___jp_1397_;
}
v___jp_1437_:
{
if (v___y_1447_ == 0)
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
lean_dec_ref(v___y_1443_);
v___x_1448_ = lean_box(0);
v___x_1449_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1449_, 0, v_expr_1286_);
lean_ctor_set(v___x_1449_, 1, v___x_1448_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*2, v___y_1445_);
v___y_1427_ = v___y_1438_;
v___y_1428_ = v___y_1439_;
v___y_1429_ = v___y_1440_;
v___y_1430_ = v___y_1441_;
v___y_1431_ = v___y_1442_;
v___y_1432_ = v___y_1445_;
v___y_1433_ = v___y_1444_;
v___y_1434_ = v___y_1446_;
v_a_1435_ = v___x_1449_;
goto v___jp_1426_;
}
else
{
lean_dec_ref(v_expr_1286_);
v___y_1416_ = v___y_1438_;
v___y_1417_ = v___y_1439_;
v___y_1418_ = v___y_1440_;
v___y_1419_ = v___y_1441_;
v___y_1420_ = v___y_1442_;
v___y_1421_ = v___y_1445_;
v___y_1422_ = v___y_1444_;
v___y_1423_ = v___y_1446_;
v_a_1424_ = v___y_1443_;
goto v___jp_1415_;
}
}
v___jp_1450_:
{
uint8_t v___x_1460_; 
v___x_1460_ = l_Lean_Exception_isInterrupt(v_a_1459_);
if (v___x_1460_ == 0)
{
uint8_t v___x_1461_; 
lean_inc_ref(v_a_1459_);
v___x_1461_ = l_Lean_Exception_isRuntime(v_a_1459_);
v___y_1438_ = v___y_1451_;
v___y_1439_ = v___y_1452_;
v___y_1440_ = v___y_1453_;
v___y_1441_ = v___y_1454_;
v___y_1442_ = v___y_1455_;
v___y_1443_ = v_a_1459_;
v___y_1444_ = v___y_1457_;
v___y_1445_ = v___y_1456_;
v___y_1446_ = v___y_1458_;
v___y_1447_ = v___x_1461_;
goto v___jp_1437_;
}
else
{
v___y_1438_ = v___y_1451_;
v___y_1439_ = v___y_1452_;
v___y_1440_ = v___y_1453_;
v___y_1441_ = v___y_1454_;
v___y_1442_ = v___y_1455_;
v___y_1443_ = v_a_1459_;
v___y_1444_ = v___y_1457_;
v___y_1445_ = v___y_1456_;
v___y_1446_ = v___y_1458_;
v___y_1447_ = v___x_1460_;
goto v___jp_1437_;
}
}
v___jp_1462_:
{
lean_object* v_a_1472_; 
v_a_1472_ = lean_ctor_get(v_a_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref(v_a_1471_);
v___y_1427_ = v___y_1463_;
v___y_1428_ = v___y_1464_;
v___y_1429_ = v___y_1465_;
v___y_1430_ = v___y_1466_;
v___y_1431_ = v___y_1467_;
v___y_1432_ = v___y_1469_;
v___y_1433_ = v___y_1468_;
v___y_1434_ = v___y_1470_;
v_a_1435_ = v_a_1472_;
goto v___jp_1426_;
}
v___jp_1473_:
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
v_a_1475_ = lean_ctor_get(v_a_1474_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v_a_1474_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v_a_1474_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v_a_1474_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
lean_ctor_set_tag(v___x_1477_, 0);
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
v___jp_1483_:
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
v_a_1485_ = lean_ctor_get(v_a_1484_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_a_1484_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v_a_1484_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v_a_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
lean_ctor_set_tag(v___x_1487_, 0);
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
v___jp_1493_:
{
lean_object* v___x_1494_; uint8_t v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1494_ = lean_box(0);
v___x_1495_ = 1;
v___x_1496_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1496_, 0, v_expr_1286_);
lean_ctor_set(v___x_1496_, 1, v___x_1494_);
lean_ctor_set_uint8(v___x_1496_, sizeof(void*)*2, v___x_1495_);
v___x_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1496_);
return v___x_1497_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___boxed(lean_object* v_expr_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure(v_expr_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
lean_dec(v_a_2367_);
lean_dec_ref(v_a_2366_);
lean_dec(v_a_2365_);
lean_dec_ref(v_a_2364_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___redArg(lean_object* v_cls_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v_options_2373_; uint8_t v_hasTrace_2374_; 
v_options_2373_ = lean_ctor_get(v___y_2371_, 2);
v_hasTrace_2374_ = lean_ctor_get_uint8(v_options_2373_, sizeof(void*)*1);
if (v_hasTrace_2374_ == 0)
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
lean_dec(v_cls_2370_);
v___x_2375_ = lean_box(v_hasTrace_2374_);
v___x_2376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
return v___x_2376_;
}
else
{
lean_object* v_inheritedTraceOptions_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v_inheritedTraceOptions_2377_ = lean_ctor_get(v___y_2371_, 13);
v___x_2378_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__1));
v___x_2379_ = l_Lean_Name_append(v___x_2378_, v_cls_2370_);
v___x_2380_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2377_, v_options_2373_, v___x_2379_);
lean_dec(v___x_2379_);
v___x_2381_ = lean_box(v___x_2380_);
v___x_2382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2382_, 0, v___x_2381_);
return v___x_2382_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___redArg___boxed(lean_object* v_cls_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___redArg(v_cls_2383_, v___y_2384_);
lean_dec_ref(v___y_2384_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_prove_spec__0(lean_object* v_cls_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v___x_2396_; 
v___x_2396_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___redArg(v_cls_2387_, v___y_2393_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___boxed(lean_object* v_cls_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_prove_spec__0(v_cls_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__1___redArg(lean_object* v___y_2407_){
_start:
{
lean_object* v___x_2409_; lean_object* v_traceState_2410_; lean_object* v_traces_2411_; lean_object* v___x_2412_; lean_object* v_traceState_2413_; lean_object* v_env_2414_; lean_object* v_nextMacroScope_2415_; lean_object* v_ngen_2416_; lean_object* v_auxDeclNGen_2417_; lean_object* v_cache_2418_; lean_object* v_messages_2419_; lean_object* v_infoState_2420_; lean_object* v_snapshotTasks_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2442_; 
v___x_2409_ = lean_st_ref_get(v___y_2407_);
v_traceState_2410_ = lean_ctor_get(v___x_2409_, 4);
lean_inc_ref(v_traceState_2410_);
lean_dec(v___x_2409_);
v_traces_2411_ = lean_ctor_get(v_traceState_2410_, 0);
lean_inc_ref(v_traces_2411_);
lean_dec_ref(v_traceState_2410_);
v___x_2412_ = lean_st_ref_take(v___y_2407_);
v_traceState_2413_ = lean_ctor_get(v___x_2412_, 4);
v_env_2414_ = lean_ctor_get(v___x_2412_, 0);
v_nextMacroScope_2415_ = lean_ctor_get(v___x_2412_, 1);
v_ngen_2416_ = lean_ctor_get(v___x_2412_, 2);
v_auxDeclNGen_2417_ = lean_ctor_get(v___x_2412_, 3);
v_cache_2418_ = lean_ctor_get(v___x_2412_, 5);
v_messages_2419_ = lean_ctor_get(v___x_2412_, 6);
v_infoState_2420_ = lean_ctor_get(v___x_2412_, 7);
v_snapshotTasks_2421_ = lean_ctor_get(v___x_2412_, 8);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2423_ = v___x_2412_;
v_isShared_2424_ = v_isSharedCheck_2442_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_snapshotTasks_2421_);
lean_inc(v_infoState_2420_);
lean_inc(v_messages_2419_);
lean_inc(v_cache_2418_);
lean_inc(v_traceState_2413_);
lean_inc(v_auxDeclNGen_2417_);
lean_inc(v_ngen_2416_);
lean_inc(v_nextMacroScope_2415_);
lean_inc(v_env_2414_);
lean_dec(v___x_2412_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2442_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
uint64_t v_tid_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2440_; 
v_tid_2425_ = lean_ctor_get_uint64(v_traceState_2413_, sizeof(void*)*1);
v_isSharedCheck_2440_ = !lean_is_exclusive(v_traceState_2413_);
if (v_isSharedCheck_2440_ == 0)
{
lean_object* v_unused_2441_; 
v_unused_2441_ = lean_ctor_get(v_traceState_2413_, 0);
lean_dec(v_unused_2441_);
v___x_2427_ = v_traceState_2413_;
v_isShared_2428_ = v_isSharedCheck_2440_;
goto v_resetjp_2426_;
}
else
{
lean_dec(v_traceState_2413_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2440_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2433_; 
v___x_2429_ = lean_unsigned_to_nat(32u);
v___x_2430_ = lean_mk_empty_array_with_capacity(v___x_2429_);
lean_dec_ref(v___x_2430_);
v___x_2431_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__1);
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v___x_2431_);
v___x_2433_ = v___x_2427_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2431_);
lean_ctor_set_uint64(v_reuseFailAlloc_2439_, sizeof(void*)*1, v_tid_2425_);
v___x_2433_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
lean_object* v___x_2435_; 
if (v_isShared_2424_ == 0)
{
lean_ctor_set(v___x_2423_, 4, v___x_2433_);
v___x_2435_ = v___x_2423_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_env_2414_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v_nextMacroScope_2415_);
lean_ctor_set(v_reuseFailAlloc_2438_, 2, v_ngen_2416_);
lean_ctor_set(v_reuseFailAlloc_2438_, 3, v_auxDeclNGen_2417_);
lean_ctor_set(v_reuseFailAlloc_2438_, 4, v___x_2433_);
lean_ctor_set(v_reuseFailAlloc_2438_, 5, v_cache_2418_);
lean_ctor_set(v_reuseFailAlloc_2438_, 6, v_messages_2419_);
lean_ctor_set(v_reuseFailAlloc_2438_, 7, v_infoState_2420_);
lean_ctor_set(v_reuseFailAlloc_2438_, 8, v_snapshotTasks_2421_);
v___x_2435_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = lean_st_ref_set(v___y_2407_, v___x_2435_);
v___x_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2437_, 0, v_traces_2411_);
return v___x_2437_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__1___redArg___boxed(lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__1___redArg(v___y_2443_);
lean_dec(v___y_2443_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__1(lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__1___redArg(v___y_2452_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__1___boxed(lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__1(v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v___y_2457_);
lean_dec_ref(v___y_2456_);
lean_dec(v___y_2455_);
return v_res_2463_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; 
v___x_2465_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__0));
v___x_2466_ = l_Lean_stringToMessageData(v___x_2465_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lam__0(lean_object* v_e_2467_, lean_object* v_x_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2477_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__1, &l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__1);
v___x_2478_ = l_Lean_MessageData_ofExpr(v_e_2467_);
v___x_2479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2477_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
v___x_2480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2479_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lam__0___boxed(lean_object* v_e_2481_, lean_object* v_x_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Lean_Elab_Tactic_NormCast_prove___lam__0(v_e_2481_, v_x_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v_x_2482_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__3___redArg(lean_object* v_oldTraces_2492_, lean_object* v_data_2493_, lean_object* v_ref_2494_, lean_object* v_msg_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v_fileName_2501_; lean_object* v_fileMap_2502_; lean_object* v_options_2503_; lean_object* v_currRecDepth_2504_; lean_object* v_maxRecDepth_2505_; lean_object* v_ref_2506_; lean_object* v_currNamespace_2507_; lean_object* v_openDecls_2508_; lean_object* v_initHeartbeats_2509_; lean_object* v_maxHeartbeats_2510_; lean_object* v_quotContext_2511_; lean_object* v_currMacroScope_2512_; uint8_t v_diag_2513_; lean_object* v_cancelTk_x3f_2514_; uint8_t v_suppressElabErrors_2515_; lean_object* v_inheritedTraceOptions_2516_; lean_object* v___x_2517_; lean_object* v_traceState_2518_; lean_object* v_traces_2519_; lean_object* v_ref_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; size_t v_sz_2523_; size_t v___x_2524_; lean_object* v___x_2525_; lean_object* v_msg_2526_; lean_object* v___x_2527_; lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2565_; 
v_fileName_2501_ = lean_ctor_get(v___y_2498_, 0);
v_fileMap_2502_ = lean_ctor_get(v___y_2498_, 1);
v_options_2503_ = lean_ctor_get(v___y_2498_, 2);
v_currRecDepth_2504_ = lean_ctor_get(v___y_2498_, 3);
v_maxRecDepth_2505_ = lean_ctor_get(v___y_2498_, 4);
v_ref_2506_ = lean_ctor_get(v___y_2498_, 5);
v_currNamespace_2507_ = lean_ctor_get(v___y_2498_, 6);
v_openDecls_2508_ = lean_ctor_get(v___y_2498_, 7);
v_initHeartbeats_2509_ = lean_ctor_get(v___y_2498_, 8);
v_maxHeartbeats_2510_ = lean_ctor_get(v___y_2498_, 9);
v_quotContext_2511_ = lean_ctor_get(v___y_2498_, 10);
v_currMacroScope_2512_ = lean_ctor_get(v___y_2498_, 11);
v_diag_2513_ = lean_ctor_get_uint8(v___y_2498_, sizeof(void*)*14);
v_cancelTk_x3f_2514_ = lean_ctor_get(v___y_2498_, 12);
v_suppressElabErrors_2515_ = lean_ctor_get_uint8(v___y_2498_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2516_ = lean_ctor_get(v___y_2498_, 13);
v___x_2517_ = lean_st_ref_get(v___y_2499_);
v_traceState_2518_ = lean_ctor_get(v___x_2517_, 4);
lean_inc_ref(v_traceState_2518_);
lean_dec(v___x_2517_);
v_traces_2519_ = lean_ctor_get(v_traceState_2518_, 0);
lean_inc_ref(v_traces_2519_);
lean_dec_ref(v_traceState_2518_);
v_ref_2520_ = l_Lean_replaceRef(v_ref_2494_, v_ref_2506_);
lean_inc_ref(v_inheritedTraceOptions_2516_);
lean_inc(v_cancelTk_x3f_2514_);
lean_inc(v_currMacroScope_2512_);
lean_inc(v_quotContext_2511_);
lean_inc(v_maxHeartbeats_2510_);
lean_inc(v_initHeartbeats_2509_);
lean_inc(v_openDecls_2508_);
lean_inc(v_currNamespace_2507_);
lean_inc(v_maxRecDepth_2505_);
lean_inc(v_currRecDepth_2504_);
lean_inc_ref(v_options_2503_);
lean_inc_ref(v_fileMap_2502_);
lean_inc_ref(v_fileName_2501_);
v___x_2521_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2521_, 0, v_fileName_2501_);
lean_ctor_set(v___x_2521_, 1, v_fileMap_2502_);
lean_ctor_set(v___x_2521_, 2, v_options_2503_);
lean_ctor_set(v___x_2521_, 3, v_currRecDepth_2504_);
lean_ctor_set(v___x_2521_, 4, v_maxRecDepth_2505_);
lean_ctor_set(v___x_2521_, 5, v_ref_2520_);
lean_ctor_set(v___x_2521_, 6, v_currNamespace_2507_);
lean_ctor_set(v___x_2521_, 7, v_openDecls_2508_);
lean_ctor_set(v___x_2521_, 8, v_initHeartbeats_2509_);
lean_ctor_set(v___x_2521_, 9, v_maxHeartbeats_2510_);
lean_ctor_set(v___x_2521_, 10, v_quotContext_2511_);
lean_ctor_set(v___x_2521_, 11, v_currMacroScope_2512_);
lean_ctor_set(v___x_2521_, 12, v_cancelTk_x3f_2514_);
lean_ctor_set(v___x_2521_, 13, v_inheritedTraceOptions_2516_);
lean_ctor_set_uint8(v___x_2521_, sizeof(void*)*14, v_diag_2513_);
lean_ctor_set_uint8(v___x_2521_, sizeof(void*)*14 + 1, v_suppressElabErrors_2515_);
v___x_2522_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2519_);
lean_dec_ref(v_traces_2519_);
v_sz_2523_ = lean_array_size(v___x_2522_);
v___x_2524_ = ((size_t)0ULL);
v___x_2525_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__5(v_sz_2523_, v___x_2524_, v___x_2522_);
v_msg_2526_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2526_, 0, v_data_2493_);
lean_ctor_set(v_msg_2526_, 1, v_msg_2495_);
lean_ctor_set(v_msg_2526_, 2, v___x_2525_);
v___x_2527_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__6(v_msg_2526_, v___y_2496_, v___y_2497_, v___x_2521_, v___y_2499_);
lean_dec_ref(v___x_2521_);
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2530_ = v___x_2527_;
v_isShared_2531_ = v_isSharedCheck_2565_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2527_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2565_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2532_; lean_object* v_traceState_2533_; lean_object* v_env_2534_; lean_object* v_nextMacroScope_2535_; lean_object* v_ngen_2536_; lean_object* v_auxDeclNGen_2537_; lean_object* v_cache_2538_; lean_object* v_messages_2539_; lean_object* v_infoState_2540_; lean_object* v_snapshotTasks_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2564_; 
v___x_2532_ = lean_st_ref_take(v___y_2499_);
v_traceState_2533_ = lean_ctor_get(v___x_2532_, 4);
v_env_2534_ = lean_ctor_get(v___x_2532_, 0);
v_nextMacroScope_2535_ = lean_ctor_get(v___x_2532_, 1);
v_ngen_2536_ = lean_ctor_get(v___x_2532_, 2);
v_auxDeclNGen_2537_ = lean_ctor_get(v___x_2532_, 3);
v_cache_2538_ = lean_ctor_get(v___x_2532_, 5);
v_messages_2539_ = lean_ctor_get(v___x_2532_, 6);
v_infoState_2540_ = lean_ctor_get(v___x_2532_, 7);
v_snapshotTasks_2541_ = lean_ctor_get(v___x_2532_, 8);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2543_ = v___x_2532_;
v_isShared_2544_ = v_isSharedCheck_2564_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_snapshotTasks_2541_);
lean_inc(v_infoState_2540_);
lean_inc(v_messages_2539_);
lean_inc(v_cache_2538_);
lean_inc(v_traceState_2533_);
lean_inc(v_auxDeclNGen_2537_);
lean_inc(v_ngen_2536_);
lean_inc(v_nextMacroScope_2535_);
lean_inc(v_env_2534_);
lean_dec(v___x_2532_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2564_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
uint64_t v_tid_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2562_; 
v_tid_2545_ = lean_ctor_get_uint64(v_traceState_2533_, sizeof(void*)*1);
v_isSharedCheck_2562_ = !lean_is_exclusive(v_traceState_2533_);
if (v_isSharedCheck_2562_ == 0)
{
lean_object* v_unused_2563_; 
v_unused_2563_ = lean_ctor_get(v_traceState_2533_, 0);
lean_dec(v_unused_2563_);
v___x_2547_ = v_traceState_2533_;
v_isShared_2548_ = v_isSharedCheck_2562_;
goto v_resetjp_2546_;
}
else
{
lean_dec(v_traceState_2533_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2562_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2552_; 
v___x_2549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2549_, 0, v_ref_2494_);
lean_ctor_set(v___x_2549_, 1, v_a_2528_);
v___x_2550_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2492_, v___x_2549_);
if (v_isShared_2548_ == 0)
{
lean_ctor_set(v___x_2547_, 0, v___x_2550_);
v___x_2552_ = v___x_2547_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2550_);
lean_ctor_set_uint64(v_reuseFailAlloc_2561_, sizeof(void*)*1, v_tid_2545_);
v___x_2552_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
lean_object* v___x_2554_; 
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 4, v___x_2552_);
v___x_2554_ = v___x_2543_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_env_2534_);
lean_ctor_set(v_reuseFailAlloc_2560_, 1, v_nextMacroScope_2535_);
lean_ctor_set(v_reuseFailAlloc_2560_, 2, v_ngen_2536_);
lean_ctor_set(v_reuseFailAlloc_2560_, 3, v_auxDeclNGen_2537_);
lean_ctor_set(v_reuseFailAlloc_2560_, 4, v___x_2552_);
lean_ctor_set(v_reuseFailAlloc_2560_, 5, v_cache_2538_);
lean_ctor_set(v_reuseFailAlloc_2560_, 6, v_messages_2539_);
lean_ctor_set(v_reuseFailAlloc_2560_, 7, v_infoState_2540_);
lean_ctor_set(v_reuseFailAlloc_2560_, 8, v_snapshotTasks_2541_);
v___x_2554_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2558_; 
v___x_2555_ = lean_st_ref_set(v___y_2499_, v___x_2554_);
v___x_2556_ = lean_box(0);
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 0, v___x_2556_);
v___x_2558_ = v___x_2530_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v___x_2556_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__3___redArg___boxed(lean_object* v_oldTraces_2566_, lean_object* v_data_2567_, lean_object* v_ref_2568_, lean_object* v_msg_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__3___redArg(v_oldTraces_2566_, v_data_2567_, v_ref_2568_, v_msg_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__4___redArg(lean_object* v_x_2576_){
_start:
{
if (lean_obj_tag(v_x_2576_) == 0)
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
v_a_2578_ = lean_ctor_get(v_x_2576_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v_x_2576_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v_x_2576_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v_x_2576_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
lean_ctor_set_tag(v___x_2580_, 1);
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
v_a_2586_ = lean_ctor_get(v_x_2576_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v_x_2576_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v_x_2576_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v_x_2576_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___x_2591_; 
if (v_isShared_2589_ == 0)
{
lean_ctor_set_tag(v___x_2588_, 0);
v___x_2591_ = v___x_2588_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__4___redArg___boxed(lean_object* v_x_2594_, lean_object* v___y_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__4___redArg(v_x_2594_);
return v_res_2596_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__2(lean_object* v_e_2597_){
_start:
{
if (lean_obj_tag(v_e_2597_) == 0)
{
uint8_t v___x_2598_; 
v___x_2598_ = 2;
return v___x_2598_;
}
else
{
lean_object* v_a_2599_; 
v_a_2599_ = lean_ctor_get(v_e_2597_, 0);
if (lean_obj_tag(v_a_2599_) == 0)
{
uint8_t v___x_2600_; 
v___x_2600_ = 1;
return v___x_2600_;
}
else
{
uint8_t v___x_2601_; 
v___x_2601_ = 0;
return v___x_2601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__2___boxed(lean_object* v_e_2602_){
_start:
{
uint8_t v_res_2603_; lean_object* v_r_2604_; 
v_res_2603_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__2(v_e_2602_);
lean_dec_ref(v_e_2602_);
v_r_2604_ = lean_box(v_res_2603_);
return v_r_2604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2(lean_object* v_cls_2605_, uint8_t v_collapsed_2606_, lean_object* v_tag_2607_, lean_object* v_opts_2608_, uint8_t v_clsEnabled_2609_, lean_object* v_oldTraces_2610_, lean_object* v_msg_2611_, lean_object* v_resStartStop_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v_fst_2621_; lean_object* v_snd_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2720_; 
v_fst_2621_ = lean_ctor_get(v_resStartStop_2612_, 0);
v_snd_2622_ = lean_ctor_get(v_resStartStop_2612_, 1);
v_isSharedCheck_2720_ = !lean_is_exclusive(v_resStartStop_2612_);
if (v_isSharedCheck_2720_ == 0)
{
v___x_2624_ = v_resStartStop_2612_;
v_isShared_2625_ = v_isSharedCheck_2720_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_snd_2622_);
lean_inc(v_fst_2621_);
lean_dec(v_resStartStop_2612_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2720_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v_data_2629_; lean_object* v_fst_2640_; lean_object* v_snd_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2719_; 
v_fst_2640_ = lean_ctor_get(v_snd_2622_, 0);
v_snd_2641_ = lean_ctor_get(v_snd_2622_, 1);
v_isSharedCheck_2719_ = !lean_is_exclusive(v_snd_2622_);
if (v_isSharedCheck_2719_ == 0)
{
v___x_2643_ = v_snd_2622_;
v_isShared_2644_ = v_isSharedCheck_2719_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_snd_2641_);
lean_inc(v_fst_2640_);
lean_dec(v_snd_2622_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2719_;
goto v_resetjp_2642_;
}
v___jp_2626_:
{
lean_object* v___x_2630_; 
lean_inc(v___y_2628_);
v___x_2630_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__3___redArg(v_oldTraces_2610_, v_data_2629_, v___y_2628_, v___y_2627_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v___x_2631_; 
lean_dec_ref(v___x_2630_);
v___x_2631_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__4___redArg(v_fst_2621_);
return v___x_2631_;
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_dec(v_fst_2621_);
v_a_2632_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2630_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2630_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
v_resetjp_2642_:
{
lean_object* v___x_2645_; uint8_t v___x_2646_; lean_object* v___y_2648_; lean_object* v_a_2649_; uint8_t v___y_2673_; double v___y_2704_; 
v___x_2645_ = l_Lean_trace_profiler;
v___x_2646_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_opts_2608_, v___x_2645_);
if (v___x_2646_ == 0)
{
v___y_2673_ = v___x_2646_;
goto v___jp_2672_;
}
else
{
lean_object* v___x_2709_; uint8_t v___x_2710_; 
v___x_2709_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2710_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_opts_2608_, v___x_2709_);
if (v___x_2710_ == 0)
{
lean_object* v___x_2711_; lean_object* v___x_2712_; double v___x_2713_; double v___x_2714_; double v___x_2715_; 
v___x_2711_ = l_Lean_trace_profiler_threshold;
v___x_2712_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__6(v_opts_2608_, v___x_2711_);
v___x_2713_ = lean_float_of_nat(v___x_2712_);
v___x_2714_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__5);
v___x_2715_ = lean_float_div(v___x_2713_, v___x_2714_);
v___y_2704_ = v___x_2715_;
goto v___jp_2703_;
}
else
{
lean_object* v___x_2716_; lean_object* v___x_2717_; double v___x_2718_; 
v___x_2716_ = l_Lean_trace_profiler_threshold;
v___x_2717_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__6(v_opts_2608_, v___x_2716_);
v___x_2718_ = lean_float_of_nat(v___x_2717_);
v___y_2704_ = v___x_2718_;
goto v___jp_2703_;
}
}
v___jp_2647_:
{
uint8_t v_result_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2655_; 
v_result_2650_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__2(v_fst_2621_);
v___x_2651_ = l_Lean_TraceResult_toEmoji(v_result_2650_);
v___x_2652_ = l_Lean_stringToMessageData(v___x_2651_);
v___x_2653_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1);
if (v_isShared_2644_ == 0)
{
lean_ctor_set_tag(v___x_2643_, 7);
lean_ctor_set(v___x_2643_, 1, v___x_2653_);
lean_ctor_set(v___x_2643_, 0, v___x_2652_);
v___x_2655_ = v___x_2643_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2652_);
lean_ctor_set(v_reuseFailAlloc_2666_, 1, v___x_2653_);
v___x_2655_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
lean_object* v_m_2657_; 
if (v_isShared_2625_ == 0)
{
lean_ctor_set_tag(v___x_2624_, 7);
lean_ctor_set(v___x_2624_, 1, v_a_2649_);
lean_ctor_set(v___x_2624_, 0, v___x_2655_);
v_m_2657_ = v___x_2624_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___x_2655_);
lean_ctor_set(v_reuseFailAlloc_2665_, 1, v_a_2649_);
v_m_2657_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; double v___x_2660_; lean_object* v_data_2661_; 
v___x_2658_ = lean_box(v_result_2650_);
v___x_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2658_);
v___x_2660_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2);
lean_inc_ref(v_tag_2607_);
lean_inc_ref(v___x_2659_);
lean_inc(v_cls_2605_);
v_data_2661_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2661_, 0, v_cls_2605_);
lean_ctor_set(v_data_2661_, 1, v___x_2659_);
lean_ctor_set(v_data_2661_, 2, v_tag_2607_);
lean_ctor_set_float(v_data_2661_, sizeof(void*)*3, v___x_2660_);
lean_ctor_set_float(v_data_2661_, sizeof(void*)*3 + 8, v___x_2660_);
lean_ctor_set_uint8(v_data_2661_, sizeof(void*)*3 + 16, v_collapsed_2606_);
if (v___x_2646_ == 0)
{
lean_dec_ref(v___x_2659_);
lean_dec(v_snd_2641_);
lean_dec(v_fst_2640_);
lean_dec_ref(v_tag_2607_);
lean_dec(v_cls_2605_);
v___y_2627_ = v_m_2657_;
v___y_2628_ = v___y_2648_;
v_data_2629_ = v_data_2661_;
goto v___jp_2626_;
}
else
{
lean_object* v_data_2662_; double v___x_2663_; double v___x_2664_; 
lean_dec_ref(v_data_2661_);
v_data_2662_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2662_, 0, v_cls_2605_);
lean_ctor_set(v_data_2662_, 1, v___x_2659_);
lean_ctor_set(v_data_2662_, 2, v_tag_2607_);
v___x_2663_ = lean_unbox_float(v_fst_2640_);
lean_dec(v_fst_2640_);
lean_ctor_set_float(v_data_2662_, sizeof(void*)*3, v___x_2663_);
v___x_2664_ = lean_unbox_float(v_snd_2641_);
lean_dec(v_snd_2641_);
lean_ctor_set_float(v_data_2662_, sizeof(void*)*3 + 8, v___x_2664_);
lean_ctor_set_uint8(v_data_2662_, sizeof(void*)*3 + 16, v_collapsed_2606_);
v___y_2627_ = v_m_2657_;
v___y_2628_ = v___y_2648_;
v_data_2629_ = v_data_2662_;
goto v___jp_2626_;
}
}
}
}
v___jp_2667_:
{
lean_object* v_ref_2668_; lean_object* v___x_2669_; 
v_ref_2668_ = lean_ctor_get(v___y_2618_, 5);
lean_inc(v___y_2619_);
lean_inc_ref(v___y_2618_);
lean_inc(v___y_2617_);
lean_inc_ref(v___y_2616_);
lean_inc(v___y_2615_);
lean_inc_ref(v___y_2614_);
lean_inc(v___y_2613_);
lean_inc(v_fst_2621_);
v___x_2669_ = lean_apply_9(v_msg_2611_, v_fst_2621_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, lean_box(0));
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; 
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2670_);
lean_dec_ref(v___x_2669_);
v___y_2648_ = v_ref_2668_;
v_a_2649_ = v_a_2670_;
goto v___jp_2647_;
}
else
{
lean_object* v___x_2671_; 
lean_dec_ref(v___x_2669_);
v___x_2671_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__4);
v___y_2648_ = v_ref_2668_;
v_a_2649_ = v___x_2671_;
goto v___jp_2647_;
}
}
v___jp_2672_:
{
if (v_clsEnabled_2609_ == 0)
{
if (v___y_2673_ == 0)
{
lean_object* v___x_2674_; lean_object* v_traceState_2675_; lean_object* v_env_2676_; lean_object* v_nextMacroScope_2677_; lean_object* v_ngen_2678_; lean_object* v_auxDeclNGen_2679_; lean_object* v_cache_2680_; lean_object* v_messages_2681_; lean_object* v_infoState_2682_; lean_object* v_snapshotTasks_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2702_; 
lean_del_object(v___x_2643_);
lean_dec(v_snd_2641_);
lean_dec(v_fst_2640_);
lean_del_object(v___x_2624_);
lean_dec_ref(v_msg_2611_);
lean_dec_ref(v_tag_2607_);
lean_dec(v_cls_2605_);
v___x_2674_ = lean_st_ref_take(v___y_2619_);
v_traceState_2675_ = lean_ctor_get(v___x_2674_, 4);
v_env_2676_ = lean_ctor_get(v___x_2674_, 0);
v_nextMacroScope_2677_ = lean_ctor_get(v___x_2674_, 1);
v_ngen_2678_ = lean_ctor_get(v___x_2674_, 2);
v_auxDeclNGen_2679_ = lean_ctor_get(v___x_2674_, 3);
v_cache_2680_ = lean_ctor_get(v___x_2674_, 5);
v_messages_2681_ = lean_ctor_get(v___x_2674_, 6);
v_infoState_2682_ = lean_ctor_get(v___x_2674_, 7);
v_snapshotTasks_2683_ = lean_ctor_get(v___x_2674_, 8);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2685_ = v___x_2674_;
v_isShared_2686_ = v_isSharedCheck_2702_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_snapshotTasks_2683_);
lean_inc(v_infoState_2682_);
lean_inc(v_messages_2681_);
lean_inc(v_cache_2680_);
lean_inc(v_traceState_2675_);
lean_inc(v_auxDeclNGen_2679_);
lean_inc(v_ngen_2678_);
lean_inc(v_nextMacroScope_2677_);
lean_inc(v_env_2676_);
lean_dec(v___x_2674_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2702_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
uint64_t v_tid_2687_; lean_object* v_traces_2688_; lean_object* v___x_2690_; uint8_t v_isShared_2691_; uint8_t v_isSharedCheck_2701_; 
v_tid_2687_ = lean_ctor_get_uint64(v_traceState_2675_, sizeof(void*)*1);
v_traces_2688_ = lean_ctor_get(v_traceState_2675_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v_traceState_2675_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2690_ = v_traceState_2675_;
v_isShared_2691_ = v_isSharedCheck_2701_;
goto v_resetjp_2689_;
}
else
{
lean_inc(v_traces_2688_);
lean_dec(v_traceState_2675_);
v___x_2690_ = lean_box(0);
v_isShared_2691_ = v_isSharedCheck_2701_;
goto v_resetjp_2689_;
}
v_resetjp_2689_:
{
lean_object* v___x_2692_; lean_object* v___x_2694_; 
v___x_2692_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2610_, v_traces_2688_);
lean_dec_ref(v_traces_2688_);
if (v_isShared_2691_ == 0)
{
lean_ctor_set(v___x_2690_, 0, v___x_2692_);
v___x_2694_ = v___x_2690_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2692_);
lean_ctor_set_uint64(v_reuseFailAlloc_2700_, sizeof(void*)*1, v_tid_2687_);
v___x_2694_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
lean_object* v___x_2696_; 
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 4, v___x_2694_);
v___x_2696_ = v___x_2685_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_env_2676_);
lean_ctor_set(v_reuseFailAlloc_2699_, 1, v_nextMacroScope_2677_);
lean_ctor_set(v_reuseFailAlloc_2699_, 2, v_ngen_2678_);
lean_ctor_set(v_reuseFailAlloc_2699_, 3, v_auxDeclNGen_2679_);
lean_ctor_set(v_reuseFailAlloc_2699_, 4, v___x_2694_);
lean_ctor_set(v_reuseFailAlloc_2699_, 5, v_cache_2680_);
lean_ctor_set(v_reuseFailAlloc_2699_, 6, v_messages_2681_);
lean_ctor_set(v_reuseFailAlloc_2699_, 7, v_infoState_2682_);
lean_ctor_set(v_reuseFailAlloc_2699_, 8, v_snapshotTasks_2683_);
v___x_2696_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2697_ = lean_st_ref_set(v___y_2619_, v___x_2696_);
v___x_2698_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__4___redArg(v_fst_2621_);
return v___x_2698_;
}
}
}
}
}
else
{
goto v___jp_2667_;
}
}
else
{
goto v___jp_2667_;
}
}
v___jp_2703_:
{
double v___x_2705_; double v___x_2706_; double v___x_2707_; uint8_t v___x_2708_; 
v___x_2705_ = lean_unbox_float(v_snd_2641_);
v___x_2706_ = lean_unbox_float(v_fst_2640_);
v___x_2707_ = lean_float_sub(v___x_2705_, v___x_2706_);
v___x_2708_ = lean_float_decLt(v___y_2704_, v___x_2707_);
v___y_2673_ = v___x_2708_;
goto v___jp_2672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2___boxed(lean_object* v_cls_2721_, lean_object* v_collapsed_2722_, lean_object* v_tag_2723_, lean_object* v_opts_2724_, lean_object* v_clsEnabled_2725_, lean_object* v_oldTraces_2726_, lean_object* v_msg_2727_, lean_object* v_resStartStop_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
uint8_t v_collapsed_boxed_2737_; uint8_t v_clsEnabled_boxed_2738_; lean_object* v_res_2739_; 
v_collapsed_boxed_2737_ = lean_unbox(v_collapsed_2722_);
v_clsEnabled_boxed_2738_ = lean_unbox(v_clsEnabled_2725_);
v_res_2739_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2(v_cls_2721_, v_collapsed_boxed_2737_, v_tag_2723_, v_opts_2724_, v_clsEnabled_boxed_2738_, v_oldTraces_2726_, v_msg_2727_, v_resStartStop_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v_opts_2724_);
return v_res_2739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove(lean_object* v_e_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_){
_start:
{
lean_object* v_____do__lift_2750_; lean_object* v_options_2763_; uint8_t v_hasTrace_2764_; 
v_options_2763_ = lean_ctor_get(v_a_2746_, 2);
v_hasTrace_2764_ = lean_ctor_get_uint8(v_options_2763_, sizeof(void*)*1);
if (v_hasTrace_2764_ == 0)
{
lean_object* v___x_2765_; 
v___x_2765_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_e_2740_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; 
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_a_2766_);
lean_dec_ref(v___x_2765_);
v_____do__lift_2750_ = v_a_2766_;
goto v___jp_2749_;
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
v_a_2767_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2765_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2765_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
else
{
lean_object* v___x_2775_; lean_object* v___x_2776_; lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2884_; 
v___x_2775_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__2_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_));
v___x_2776_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___redArg(v___x_2775_, v_a_2746_);
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2779_ = v___x_2776_;
v_isShared_2780_ = v_isSharedCheck_2884_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2776_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2884_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___f_2781_; lean_object* v___x_2782_; lean_object* v___y_2784_; lean_object* v___y_2785_; lean_object* v_a_2786_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v_a_2802_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v_a_2809_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v_a_2822_; uint8_t v___x_2871_; 
lean_inc_ref(v_e_2740_);
v___f_2781_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_prove___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2781_, 0, v_e_2740_);
v___x_2782_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_2871_ = lean_unbox(v_a_2777_);
if (v___x_2871_ == 0)
{
lean_object* v___x_2872_; uint8_t v___x_2873_; 
v___x_2872_ = l_Lean_trace_profiler;
v___x_2873_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_2763_, v___x_2872_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2874_; 
lean_dec_ref(v___f_2781_);
lean_del_object(v___x_2779_);
lean_dec(v_a_2777_);
v___x_2874_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_e_2740_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref(v___x_2874_);
v_____do__lift_2750_ = v_a_2875_;
goto v___jp_2749_;
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
v_a_2876_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2874_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2874_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
else
{
goto v___jp_2824_;
}
}
else
{
goto v___jp_2824_;
}
v___jp_2783_:
{
lean_object* v___x_2787_; double v___x_2788_; double v___x_2789_; double v___x_2790_; double v___x_2791_; double v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; uint8_t v___x_2797_; lean_object* v___x_2798_; 
v___x_2787_ = lean_io_mono_nanos_now();
v___x_2788_ = lean_float_of_nat(v___y_2785_);
v___x_2789_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1);
v___x_2790_ = lean_float_div(v___x_2788_, v___x_2789_);
v___x_2791_ = lean_float_of_nat(v___x_2787_);
v___x_2792_ = lean_float_div(v___x_2791_, v___x_2789_);
v___x_2793_ = lean_box_float(v___x_2790_);
v___x_2794_ = lean_box_float(v___x_2792_);
v___x_2795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2793_);
lean_ctor_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2796_, 0, v_a_2786_);
lean_ctor_set(v___x_2796_, 1, v___x_2795_);
v___x_2797_ = lean_unbox(v_a_2777_);
lean_dec(v_a_2777_);
v___x_2798_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2(v___x_2775_, v_hasTrace_2764_, v___x_2782_, v_options_2763_, v___x_2797_, v___y_2784_, v___f_2781_, v___x_2796_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
return v___x_2798_;
}
v___jp_2799_:
{
lean_object* v___x_2804_; 
if (v_isShared_2780_ == 0)
{
lean_ctor_set_tag(v___x_2779_, 1);
lean_ctor_set(v___x_2779_, 0, v_a_2802_);
v___x_2804_ = v___x_2779_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2802_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
v___y_2784_ = v___y_2800_;
v___y_2785_ = v___y_2801_;
v_a_2786_ = v___x_2804_;
goto v___jp_2783_;
}
}
v___jp_2806_:
{
lean_object* v___x_2810_; double v___x_2811_; double v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; lean_object* v___x_2818_; 
v___x_2810_ = lean_io_get_num_heartbeats();
v___x_2811_ = lean_float_of_nat(v___y_2808_);
v___x_2812_ = lean_float_of_nat(v___x_2810_);
v___x_2813_ = lean_box_float(v___x_2811_);
v___x_2814_ = lean_box_float(v___x_2812_);
v___x_2815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2813_);
lean_ctor_set(v___x_2815_, 1, v___x_2814_);
v___x_2816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2816_, 0, v_a_2809_);
lean_ctor_set(v___x_2816_, 1, v___x_2815_);
v___x_2817_ = lean_unbox(v_a_2777_);
lean_dec(v_a_2777_);
v___x_2818_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2(v___x_2775_, v_hasTrace_2764_, v___x_2782_, v_options_2763_, v___x_2817_, v___y_2807_, v___f_2781_, v___x_2816_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
return v___x_2818_;
}
v___jp_2819_:
{
lean_object* v___x_2823_; 
v___x_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2823_, 0, v_a_2822_);
v___y_2807_ = v___y_2821_;
v___y_2808_ = v___y_2820_;
v_a_2809_ = v___x_2823_;
goto v___jp_2806_;
}
v___jp_2824_:
{
lean_object* v___x_2825_; lean_object* v_a_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; 
v___x_2825_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__1___redArg(v_a_2747_);
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc(v_a_2826_);
lean_dec_ref(v___x_2825_);
v___x_2827_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2828_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_2763_, v___x_2827_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = lean_io_mono_nanos_now();
v___x_2830_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_e_2740_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref(v___x_2830_);
if (lean_obj_tag(v_a_2831_) == 0)
{
lean_object* v___x_2832_; 
v___x_2832_ = lean_box(0);
v___y_2800_ = v_a_2826_;
v___y_2801_ = v___x_2829_;
v_a_2802_ = v___x_2832_;
goto v___jp_2799_;
}
else
{
lean_object* v_val_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2841_; 
v_val_2833_ = lean_ctor_get(v_a_2831_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v_a_2831_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2835_ = v_a_2831_;
v_isShared_2836_ = v_isSharedCheck_2841_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_val_2833_);
lean_dec(v_a_2831_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2841_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2837_; lean_object* v___x_2839_; 
v___x_2837_ = l_Lean_mkFVar(v_val_2833_);
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 0, v___x_2837_);
v___x_2839_ = v___x_2835_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v___x_2837_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
v___y_2800_ = v_a_2826_;
v___y_2801_ = v___x_2829_;
v_a_2802_ = v___x_2839_;
goto v___jp_2799_;
}
}
}
}
else
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
lean_del_object(v___x_2779_);
v_a_2842_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2830_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2830_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
lean_ctor_set_tag(v___x_2844_, 0);
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
v___y_2784_ = v_a_2826_;
v___y_2785_ = v___x_2829_;
v_a_2786_ = v___x_2847_;
goto v___jp_2783_;
}
}
}
}
else
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
lean_del_object(v___x_2779_);
v___x_2850_ = lean_io_get_num_heartbeats();
v___x_2851_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_e_2740_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
if (lean_obj_tag(v___x_2851_) == 0)
{
lean_object* v_a_2852_; 
v_a_2852_ = lean_ctor_get(v___x_2851_, 0);
lean_inc(v_a_2852_);
lean_dec_ref(v___x_2851_);
if (lean_obj_tag(v_a_2852_) == 0)
{
lean_object* v___x_2853_; 
v___x_2853_ = lean_box(0);
v___y_2820_ = v___x_2850_;
v___y_2821_ = v_a_2826_;
v_a_2822_ = v___x_2853_;
goto v___jp_2819_;
}
else
{
lean_object* v_val_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2862_; 
v_val_2854_ = lean_ctor_get(v_a_2852_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v_a_2852_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2856_ = v_a_2852_;
v_isShared_2857_ = v_isSharedCheck_2862_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_val_2854_);
lean_dec(v_a_2852_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2862_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2858_; lean_object* v___x_2860_; 
v___x_2858_ = l_Lean_mkFVar(v_val_2854_);
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 0, v___x_2858_);
v___x_2860_ = v___x_2856_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2858_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
v___y_2820_ = v___x_2850_;
v___y_2821_ = v_a_2826_;
v_a_2822_ = v___x_2860_;
goto v___jp_2819_;
}
}
}
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
v_a_2863_ = lean_ctor_get(v___x_2851_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2851_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2851_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2851_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
lean_ctor_set_tag(v___x_2865_, 0);
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
v___y_2807_ = v_a_2826_;
v___y_2808_ = v___x_2850_;
v_a_2809_ = v___x_2868_;
goto v___jp_2806_;
}
}
}
}
}
}
}
v___jp_2749_:
{
if (lean_obj_tag(v_____do__lift_2750_) == 0)
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2751_ = lean_box(0);
v___x_2752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2751_);
return v___x_2752_;
}
else
{
lean_object* v_val_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2762_; 
v_val_2753_ = lean_ctor_get(v_____do__lift_2750_, 0);
v_isSharedCheck_2762_ = !lean_is_exclusive(v_____do__lift_2750_);
if (v_isSharedCheck_2762_ == 0)
{
v___x_2755_ = v_____do__lift_2750_;
v_isShared_2756_ = v_isSharedCheck_2762_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_val_2753_);
lean_dec(v_____do__lift_2750_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2762_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2757_; lean_object* v___x_2759_; 
v___x_2757_ = l_Lean_mkFVar(v_val_2753_);
if (v_isShared_2756_ == 0)
{
lean_ctor_set(v___x_2755_, 0, v___x_2757_);
v___x_2759_ = v___x_2755_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2761_; 
v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2761_, 0, v___x_2757_);
v___x_2759_ = v_reuseFailAlloc_2761_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
lean_object* v___x_2760_; 
v___x_2760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2759_);
return v___x_2760_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___boxed(lean_object* v_e_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_){
_start:
{
lean_object* v_res_2894_; 
v_res_2894_ = l_Lean_Elab_Tactic_NormCast_prove(v_e_2885_, v_a_2886_, v_a_2887_, v_a_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_);
lean_dec(v_a_2892_);
lean_dec_ref(v_a_2891_);
lean_dec(v_a_2890_);
lean_dec_ref(v_a_2889_);
lean_dec(v_a_2888_);
lean_dec_ref(v_a_2887_);
lean_dec(v_a_2886_);
return v_res_2894_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__4(lean_object* v_00_u03b1_2895_, lean_object* v_x_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__4___redArg(v_x_2896_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2906_, lean_object* v_x_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__4(v_00_u03b1_2906_, v_x_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v___y_2908_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__3(lean_object* v_oldTraces_2917_, lean_object* v_data_2918_, lean_object* v_ref_2919_, lean_object* v_msg_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__3___redArg(v_oldTraces_2917_, v_data_2918_, v_ref_2919_, v_msg_2920_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__3___boxed(lean_object* v_oldTraces_2930_, lean_object* v_data_2931_, lean_object* v_ref_2932_, lean_object* v_msg_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__3(v_oldTraces_2930_, v_data_2931_, v_ref_2932_, v_msg_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_);
lean_dec(v___y_2940_);
lean_dec_ref(v___y_2939_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0(lean_object* v_a_2943_, lean_object* v_cache_2944_, lean_object* v_a_x3f_2945_){
_start:
{
lean_object* v___x_2947_; lean_object* v_congrCache_2948_; lean_object* v_dsimpCache_2949_; lean_object* v_usedTheorems_2950_; lean_object* v_numSteps_2951_; lean_object* v_diag_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2962_; 
v___x_2947_ = lean_st_ref_take(v_a_2943_);
v_congrCache_2948_ = lean_ctor_get(v___x_2947_, 1);
v_dsimpCache_2949_ = lean_ctor_get(v___x_2947_, 2);
v_usedTheorems_2950_ = lean_ctor_get(v___x_2947_, 3);
v_numSteps_2951_ = lean_ctor_get(v___x_2947_, 4);
v_diag_2952_ = lean_ctor_get(v___x_2947_, 5);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2962_ == 0)
{
lean_object* v_unused_2963_; 
v_unused_2963_ = lean_ctor_get(v___x_2947_, 0);
lean_dec(v_unused_2963_);
v___x_2954_ = v___x_2947_;
v_isShared_2955_ = v_isSharedCheck_2962_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_diag_2952_);
lean_inc(v_numSteps_2951_);
lean_inc(v_usedTheorems_2950_);
lean_inc(v_dsimpCache_2949_);
lean_inc(v_congrCache_2948_);
lean_dec(v___x_2947_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2962_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 0, v_cache_2944_);
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_cache_2944_);
lean_ctor_set(v_reuseFailAlloc_2961_, 1, v_congrCache_2948_);
lean_ctor_set(v_reuseFailAlloc_2961_, 2, v_dsimpCache_2949_);
lean_ctor_set(v_reuseFailAlloc_2961_, 3, v_usedTheorems_2950_);
lean_ctor_set(v_reuseFailAlloc_2961_, 4, v_numSteps_2951_);
lean_ctor_set(v_reuseFailAlloc_2961_, 5, v_diag_2952_);
v___x_2957_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; 
v___x_2958_ = lean_st_ref_set(v_a_2943_, v___x_2957_);
v___x_2959_ = lean_box(0);
v___x_2960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2960_, 0, v___x_2959_);
return v___x_2960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0___boxed(lean_object* v_a_2964_, lean_object* v_cache_2965_, lean_object* v_a_x3f_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_res_2968_; 
v_res_2968_ = l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0(v_a_2964_, v_cache_2965_, v_a_x3f_2966_);
lean_dec(v_a_x3f_2966_);
lean_dec(v_a_2964_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim(lean_object* v_up_2971_, lean_object* v_e_2972_, lean_object* v_a_2973_, lean_object* v_a_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_){
_start:
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v_congrCache_2983_; lean_object* v_dsimpCache_2984_; lean_object* v_usedTheorems_2985_; lean_object* v_numSteps_2986_; lean_object* v_diag_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_3089_; 
v___x_2981_ = lean_st_ref_get(v_a_2975_);
v___x_2982_ = lean_st_ref_take(v_a_2975_);
v_congrCache_2983_ = lean_ctor_get(v___x_2982_, 1);
v_dsimpCache_2984_ = lean_ctor_get(v___x_2982_, 2);
v_usedTheorems_2985_ = lean_ctor_get(v___x_2982_, 3);
v_numSteps_2986_ = lean_ctor_get(v___x_2982_, 4);
v_diag_2987_ = lean_ctor_get(v___x_2982_, 5);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3089_ == 0)
{
lean_object* v_unused_3090_; 
v_unused_3090_ = lean_ctor_get(v___x_2982_, 0);
lean_dec(v_unused_3090_);
v___x_2989_ = v___x_2982_;
v_isShared_2990_ = v_isSharedCheck_3089_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_diag_2987_);
lean_inc(v_numSteps_2986_);
lean_inc(v_usedTheorems_2985_);
lean_inc(v_dsimpCache_2984_);
lean_inc(v_congrCache_2983_);
lean_dec(v___x_2982_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_3089_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
uint8_t v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2994_; 
v___x_2991_ = 1;
v___x_2992_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 0, v___x_2992_);
v___x_2994_ = v___x_2989_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_2992_);
lean_ctor_set(v_reuseFailAlloc_3088_, 1, v_congrCache_2983_);
lean_ctor_set(v_reuseFailAlloc_3088_, 2, v_dsimpCache_2984_);
lean_ctor_set(v_reuseFailAlloc_3088_, 3, v_usedTheorems_2985_);
lean_ctor_set(v_reuseFailAlloc_3088_, 4, v_numSteps_2986_);
lean_ctor_set(v_reuseFailAlloc_3088_, 5, v_diag_2987_);
v___x_2994_ = v_reuseFailAlloc_3088_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
lean_object* v___x_2995_; lean_object* v_post_2996_; lean_object* v_erased_2997_; lean_object* v_cache_2998_; lean_object* v_pre_2999_; lean_object* v_post_3000_; lean_object* v_dpre_3001_; lean_object* v_dpost_3002_; lean_object* v___x_3003_; uint8_t v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v_r_3007_; 
v___x_2995_ = lean_st_ref_set(v_a_2975_, v___x_2994_);
v_post_2996_ = lean_ctor_get(v_up_2971_, 1);
lean_inc_ref(v_post_2996_);
v_erased_2997_ = lean_ctor_get(v_up_2971_, 4);
lean_inc_ref(v_erased_2997_);
lean_dec_ref(v_up_2971_);
v_cache_2998_ = lean_ctor_get(v___x_2981_, 0);
lean_inc_ref(v_cache_2998_);
lean_dec(v___x_2981_);
v_pre_2999_ = lean_ctor_get(v_a_2973_, 0);
v_post_3000_ = lean_ctor_get(v_a_2973_, 1);
v_dpre_3001_ = lean_ctor_get(v_a_2973_, 2);
v_dpost_3002_ = lean_ctor_get(v_a_2973_, 3);
v___x_3003_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__0));
v___x_3004_ = 0;
v___x_3005_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__1));
lean_inc_ref(v_dpost_3002_);
lean_inc_ref(v_dpre_3001_);
lean_inc_ref(v_post_3000_);
lean_inc_ref(v_pre_2999_);
v___x_3006_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_3006_, 0, v_pre_2999_);
lean_ctor_set(v___x_3006_, 1, v_post_3000_);
lean_ctor_set(v___x_3006_, 2, v_dpre_3001_);
lean_ctor_set(v___x_3006_, 3, v_dpost_3002_);
lean_ctor_set(v___x_3006_, 4, v___x_3003_);
lean_ctor_set_uint8(v___x_3006_, sizeof(void*)*5, v___x_3004_);
lean_inc_ref(v_e_2972_);
v_r_3007_ = l_Lean_Meta_Simp_rewrite_x3f(v_e_2972_, v_post_2996_, v_erased_2997_, v___x_3005_, v___x_3004_, v___x_3006_, v_a_2974_, v_a_2975_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_);
lean_dec_ref(v___x_3006_);
if (lean_obj_tag(v_r_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3076_; 
v_a_3008_ = lean_ctor_get(v_r_3007_, 0);
v_isSharedCheck_3076_ = !lean_is_exclusive(v_r_3007_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3010_ = v_r_3007_;
v_isShared_3011_ = v_isSharedCheck_3076_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v_r_3007_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3076_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3013_; 
lean_inc(v_a_3008_);
if (v_isShared_3011_ == 0)
{
lean_ctor_set_tag(v___x_3010_, 1);
v___x_3013_ = v___x_3010_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_a_3008_);
v___x_3013_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
lean_object* v___x_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3073_; 
v___x_3014_ = l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0(v_a_2975_, v_cache_2998_, v___x_3013_);
lean_dec_ref(v___x_3013_);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3073_ == 0)
{
lean_object* v_unused_3074_; 
v_unused_3074_ = lean_ctor_get(v___x_3014_, 0);
lean_dec(v_unused_3074_);
v___x_3016_ = v___x_3014_;
v_isShared_3017_ = v_isSharedCheck_3073_;
goto v_resetjp_3015_;
}
else
{
lean_dec(v___x_3014_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3073_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___y_3019_; lean_object* v_expr_3020_; 
if (lean_obj_tag(v_a_3008_) == 0)
{
lean_object* v___x_3069_; lean_object* v___x_3070_; 
v___x_3069_ = lean_box(0);
lean_inc_ref(v_e_2972_);
v___x_3070_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3070_, 0, v_e_2972_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
lean_ctor_set_uint8(v___x_3070_, sizeof(void*)*2, v___x_2991_);
lean_inc_ref(v_e_2972_);
v___y_3019_ = v___x_3070_;
v_expr_3020_ = v_e_2972_;
goto v___jp_3018_;
}
else
{
lean_object* v_val_3071_; lean_object* v_expr_3072_; 
v_val_3071_ = lean_ctor_get(v_a_3008_, 0);
lean_inc(v_val_3071_);
lean_dec_ref(v_a_3008_);
v_expr_3072_ = lean_ctor_get(v_val_3071_, 0);
lean_inc_ref(v_expr_3072_);
v___y_3019_ = v_val_3071_;
v_expr_3020_ = v_expr_3072_;
goto v___jp_3018_;
}
v___jp_3018_:
{
lean_object* v___x_3021_; 
v___x_3021_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure(v_expr_3020_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3023_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3022_);
lean_dec_ref(v___x_3021_);
v___x_3023_ = l_Lean_Meta_Simp_Result_mkEqTrans(v___y_3019_, v_a_3022_, v_a_2976_, v_a_2977_, v_a_2978_, v_a_2979_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3052_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3026_ = v___x_3023_;
v_isShared_3027_ = v_isSharedCheck_3052_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3023_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3052_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v_expr_3028_; uint8_t v___x_3029_; 
v_expr_3028_ = lean_ctor_get(v_a_3024_, 0);
v___x_3029_ = lean_expr_eqv(v_expr_3028_, v_e_2972_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3031_; 
lean_dec_ref(v_e_2972_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set_tag(v___x_3016_, 1);
lean_ctor_set(v___x_3016_, 0, v_a_3024_);
v___x_3031_ = v___x_3016_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3024_);
v___x_3031_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
lean_object* v___x_3033_; 
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 0, v___x_3031_);
v___x_3033_ = v___x_3026_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v___x_3031_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
else
{
lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3049_; 
v_isSharedCheck_3049_ = !lean_is_exclusive(v_a_3024_);
if (v_isSharedCheck_3049_ == 0)
{
lean_object* v_unused_3050_; lean_object* v_unused_3051_; 
v_unused_3050_ = lean_ctor_get(v_a_3024_, 1);
lean_dec(v_unused_3050_);
v_unused_3051_ = lean_ctor_get(v_a_3024_, 0);
lean_dec(v_unused_3051_);
v___x_3037_ = v_a_3024_;
v_isShared_3038_ = v_isSharedCheck_3049_;
goto v_resetjp_3036_;
}
else
{
lean_dec(v_a_3024_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3049_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3039_; lean_object* v___x_3041_; 
v___x_3039_ = lean_box(0);
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 1, v___x_3039_);
lean_ctor_set(v___x_3037_, 0, v_e_2972_);
v___x_3041_ = v___x_3037_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_e_2972_);
lean_ctor_set(v_reuseFailAlloc_3048_, 1, v___x_3039_);
v___x_3041_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
lean_object* v___x_3043_; 
lean_ctor_set_uint8(v___x_3041_, sizeof(void*)*2, v___x_3029_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set(v___x_3016_, 0, v___x_3041_);
v___x_3043_ = v___x_3016_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3041_);
v___x_3043_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
lean_object* v___x_3045_; 
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 0, v___x_3043_);
v___x_3045_ = v___x_3026_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3043_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
lean_del_object(v___x_3016_);
lean_dec_ref(v_e_2972_);
v_a_3053_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___x_3023_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_3023_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
lean_dec_ref(v___y_3019_);
lean_del_object(v___x_3016_);
lean_dec_ref(v_e_2972_);
v_a_3061_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___x_3021_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___x_3021_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
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
lean_object* v_a_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_dec_ref(v_e_2972_);
v_a_3077_ = lean_ctor_get(v_r_3007_, 0);
lean_inc(v_a_3077_);
lean_dec_ref(v_r_3007_);
v___x_3078_ = lean_box(0);
v___x_3079_ = l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0(v_a_2975_, v_cache_2998_, v___x_3078_);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3086_ == 0)
{
lean_object* v_unused_3087_; 
v_unused_3087_ = lean_ctor_get(v___x_3079_, 0);
lean_dec(v_unused_3087_);
v___x_3081_ = v___x_3079_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_dec(v___x_3079_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
lean_ctor_set_tag(v___x_3081_, 1);
lean_ctor_set(v___x_3081_, 0, v_a_3077_);
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3077_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___boxed(lean_object* v_up_3091_, lean_object* v_e_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_, lean_object* v_a_3095_, lean_object* v_a_3096_, lean_object* v_a_3097_, lean_object* v_a_3098_, lean_object* v_a_3099_, lean_object* v_a_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l_Lean_Elab_Tactic_NormCast_upwardAndElim(v_up_3091_, v_e_3092_, v_a_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_, v_a_3099_);
lean_dec(v_a_3099_);
lean_dec_ref(v_a_3098_);
lean_dec(v_a_3097_);
lean_dec_ref(v_a_3096_);
lean_dec(v_a_3095_);
lean_dec_ref(v_a_3094_);
lean_dec(v_a_3093_);
return v_res_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_numeralToCoe(lean_object* v_e_3106_, lean_object* v_a_3107_, lean_object* v_a_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_){
_start:
{
lean_object* v___x_3112_; 
v___x_3112_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_e_3106_);
if (lean_obj_tag(v___x_3112_) == 1)
{
lean_object* v_val_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3188_; 
v_val_3113_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3115_ = v___x_3112_;
v_isShared_3116_ = v_isSharedCheck_3188_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_val_3113_);
lean_dec(v___x_3112_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3188_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v_fst_3117_; lean_object* v_snd_3118_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___x_3166_; 
v_fst_3117_ = lean_ctor_get(v_val_3113_, 0);
lean_inc(v_fst_3117_);
v_snd_3118_ = lean_ctor_get(v_val_3113_, 1);
lean_inc(v_snd_3118_);
lean_dec(v_val_3113_);
lean_inc(v_a_3110_);
lean_inc_ref(v_a_3109_);
lean_inc(v_a_3108_);
lean_inc_ref(v_a_3107_);
lean_inc(v_fst_3117_);
v___x_3166_ = lean_whnf(v_fst_3117_, v_a_3107_, v_a_3108_, v_a_3109_, v_a_3110_);
if (lean_obj_tag(v___x_3166_) == 0)
{
lean_object* v_a_3167_; lean_object* v___x_3168_; uint8_t v___x_3169_; 
v_a_3167_ = lean_ctor_get(v___x_3166_, 0);
lean_inc(v_a_3167_);
lean_dec_ref(v___x_3166_);
v___x_3168_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__5));
v___x_3169_ = l_Lean_Expr_isConstOf(v_a_3167_, v___x_3168_);
lean_dec(v_a_3167_);
if (v___x_3169_ == 0)
{
v___y_3120_ = v_a_3107_;
v___y_3121_ = v_a_3108_;
v___y_3122_ = v_a_3109_;
v___y_3123_ = v_a_3110_;
goto v___jp_3119_;
}
else
{
lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3179_; 
lean_dec(v_snd_3118_);
lean_dec(v_fst_3117_);
lean_del_object(v___x_3115_);
lean_dec_ref(v_e_3106_);
v___x_3170_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_3171_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_3170_, v_a_3107_, v_a_3108_, v_a_3109_, v_a_3110_);
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3174_ = v___x_3171_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3171_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3177_; 
if (v_isShared_3175_ == 0)
{
v___x_3177_ = v___x_3174_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3172_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
else
{
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3187_; 
lean_dec(v_snd_3118_);
lean_dec(v_fst_3117_);
lean_del_object(v___x_3115_);
lean_dec_ref(v_e_3106_);
v_a_3180_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3182_ = v___x_3166_;
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3166_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3185_; 
if (v_isShared_3183_ == 0)
{
v___x_3185_ = v___x_3182_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_a_3180_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
v___jp_3119_:
{
lean_object* v___x_3124_; lean_object* v___x_3126_; 
v___x_3124_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_numeralToCoe___closed__1));
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 0, v_fst_3117_);
v___x_3126_ = v___x_3115_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_fst_3117_);
v___x_3126_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; 
v___x_3127_ = lean_box(0);
v___x_3128_ = l_Lean_mkNatLit(v_snd_3118_);
v___x_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3129_, 0, v___x_3128_);
v___x_3130_ = lean_unsigned_to_nat(3u);
v___x_3131_ = lean_mk_empty_array_with_capacity(v___x_3130_);
v___x_3132_ = lean_array_push(v___x_3131_, v___x_3126_);
v___x_3133_ = lean_array_push(v___x_3132_, v___x_3127_);
v___x_3134_ = lean_array_push(v___x_3133_, v___x_3129_);
v___x_3135_ = l_Lean_Meta_mkAppOptM(v___x_3124_, v___x_3134_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
if (lean_obj_tag(v___x_3135_) == 0)
{
lean_object* v_a_3136_; lean_object* v___x_3137_; 
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_a_3136_);
lean_dec_ref(v___x_3135_);
v___x_3137_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_e_3106_, v_a_3136_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v_a_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3148_; 
v_a_3138_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3140_ = v___x_3137_;
v_isShared_3141_ = v_isSharedCheck_3148_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_a_3138_);
lean_dec(v___x_3137_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3148_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
if (lean_obj_tag(v_a_3138_) == 1)
{
lean_object* v_val_3142_; lean_object* v___x_3144_; 
v_val_3142_ = lean_ctor_get(v_a_3138_, 0);
lean_inc(v_val_3142_);
lean_dec_ref(v_a_3138_);
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 0, v_val_3142_);
v___x_3144_ = v___x_3140_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_val_3142_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
else
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
lean_del_object(v___x_3140_);
lean_dec(v_a_3138_);
v___x_3146_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_3147_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_3146_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
return v___x_3147_;
}
}
}
else
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
v_a_3149_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v___x_3137_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3137_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
else
{
lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3164_; 
lean_dec_ref(v_e_3106_);
v_a_3157_ = lean_ctor_get(v___x_3135_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v___x_3135_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3159_ = v___x_3135_;
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_dec(v___x_3135_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3164_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3162_; 
if (v_isShared_3160_ == 0)
{
v___x_3162_ = v___x_3159_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v_a_3157_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
lean_dec(v___x_3112_);
lean_dec_ref(v_e_3106_);
v___x_3189_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_3190_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_3189_, v_a_3107_, v_a_3108_, v_a_3109_, v_a_3110_);
return v___x_3190_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_numeralToCoe___boxed(lean_object* v_e_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_){
_start:
{
lean_object* v_res_3197_; 
v_res_3197_ = l_Lean_Elab_Tactic_NormCast_numeralToCoe(v_e_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_);
lean_dec(v_a_3195_);
lean_dec_ref(v_a_3194_);
lean_dec(v_a_3193_);
lean_dec_ref(v_a_3192_);
return v_res_3197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(lean_object* v_e_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_){
_start:
{
lean_object* v___x_3212_; uint8_t v___x_3213_; uint8_t v___x_3214_; lean_object* v___x_3215_; 
v___x_3212_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_));
v___x_3213_ = 0;
v___x_3214_ = 1;
v___x_3215_ = l_Lean_Meta_evalExpr_x27___redArg(v___x_3212_, v_e_3206_, v___x_3213_, v___x_3214_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_);
return v___x_3215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3____boxed(lean_object* v_e_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(v_e_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_);
lean_dec(v_a_3220_);
lean_dec_ref(v_a_3219_);
lean_dec(v_a_3218_);
lean_dec_ref(v_a_3217_);
return v_res_3222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(lean_object* v_e_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_){
_start:
{
lean_object* v___x_3231_; 
v___x_3231_ = l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(v_e_3223_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3____boxed(lean_object* v_e_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_){
_start:
{
lean_object* v_res_3240_; 
v_res_3240_ = l_Lean_Elab_Tactic_NormCast_evalUnsafe_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(v_e_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_);
lean_dec(v_a_3238_);
lean_dec_ref(v_a_3237_);
lean_dec(v_a_3236_);
lean_dec_ref(v_a_3235_);
lean_dec(v_a_3234_);
lean_dec_ref(v_a_3233_);
return v_res_3240_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__0(void){
_start:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3241_ = lean_box(1);
v___x_3242_ = l_Lean_MessageData_ofFormat(v___x_3241_);
return v___x_3242_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__3(void){
_start:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3246_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__2));
v___x_3247_ = l_Lean_MessageData_ofFormat(v___x_3246_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9(lean_object* v_x_3248_, lean_object* v_x_3249_){
_start:
{
if (lean_obj_tag(v_x_3249_) == 0)
{
return v_x_3248_;
}
else
{
lean_object* v_head_3250_; lean_object* v_tail_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3273_; 
v_head_3250_ = lean_ctor_get(v_x_3249_, 0);
v_tail_3251_ = lean_ctor_get(v_x_3249_, 1);
v_isSharedCheck_3273_ = !lean_is_exclusive(v_x_3249_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3253_ = v_x_3249_;
v_isShared_3254_ = v_isSharedCheck_3273_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_tail_3251_);
lean_inc(v_head_3250_);
lean_dec(v_x_3249_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3273_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v_before_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3271_; 
v_before_3255_ = lean_ctor_get(v_head_3250_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v_head_3250_);
if (v_isSharedCheck_3271_ == 0)
{
lean_object* v_unused_3272_; 
v_unused_3272_ = lean_ctor_get(v_head_3250_, 1);
lean_dec(v_unused_3272_);
v___x_3257_ = v_head_3250_;
v_isShared_3258_ = v_isSharedCheck_3271_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_before_3255_);
lean_dec(v_head_3250_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3271_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3259_; lean_object* v___x_3261_; 
v___x_3259_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__0);
if (v_isShared_3258_ == 0)
{
lean_ctor_set_tag(v___x_3257_, 7);
lean_ctor_set(v___x_3257_, 1, v___x_3259_);
lean_ctor_set(v___x_3257_, 0, v_x_3248_);
v___x_3261_ = v___x_3257_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_x_3248_);
lean_ctor_set(v_reuseFailAlloc_3270_, 1, v___x_3259_);
v___x_3261_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
lean_object* v___x_3262_; lean_object* v___x_3264_; 
v___x_3262_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__3);
if (v_isShared_3254_ == 0)
{
lean_ctor_set_tag(v___x_3253_, 7);
lean_ctor_set(v___x_3253_, 1, v___x_3262_);
lean_ctor_set(v___x_3253_, 0, v___x_3261_);
v___x_3264_ = v___x_3253_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v___x_3261_);
lean_ctor_set(v_reuseFailAlloc_3269_, 1, v___x_3262_);
v___x_3264_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
v___x_3265_ = l_Lean_MessageData_ofSyntax(v_before_3255_);
v___x_3266_ = l_Lean_indentD(v___x_3265_);
v___x_3267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3264_);
lean_ctor_set(v___x_3267_, 1, v___x_3266_);
v_x_3248_ = v___x_3267_;
v_x_3249_ = v_tail_3251_;
goto _start;
}
}
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3277_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__1));
v___x_3278_ = l_Lean_MessageData_ofFormat(v___x_3277_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg(lean_object* v_msgData_3279_, lean_object* v_macroStack_3280_, lean_object* v___y_3281_){
_start:
{
lean_object* v_options_3283_; lean_object* v___x_3284_; uint8_t v___x_3285_; 
v_options_3283_ = lean_ctor_get(v___y_3281_, 2);
v___x_3284_ = l_Lean_Elab_pp_macroStack;
v___x_3285_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_3283_, v___x_3284_);
if (v___x_3285_ == 0)
{
lean_object* v___x_3286_; 
lean_dec(v_macroStack_3280_);
v___x_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3286_, 0, v_msgData_3279_);
return v___x_3286_;
}
else
{
if (lean_obj_tag(v_macroStack_3280_) == 0)
{
lean_object* v___x_3287_; 
v___x_3287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3287_, 0, v_msgData_3279_);
return v___x_3287_;
}
else
{
lean_object* v_head_3288_; lean_object* v_after_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3304_; 
v_head_3288_ = lean_ctor_get(v_macroStack_3280_, 0);
lean_inc(v_head_3288_);
v_after_3289_ = lean_ctor_get(v_head_3288_, 1);
v_isSharedCheck_3304_ = !lean_is_exclusive(v_head_3288_);
if (v_isSharedCheck_3304_ == 0)
{
lean_object* v_unused_3305_; 
v_unused_3305_ = lean_ctor_get(v_head_3288_, 0);
lean_dec(v_unused_3305_);
v___x_3291_ = v_head_3288_;
v_isShared_3292_ = v_isSharedCheck_3304_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_after_3289_);
lean_dec(v_head_3288_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3304_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; lean_object* v___x_3295_; 
v___x_3293_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__0);
if (v_isShared_3292_ == 0)
{
lean_ctor_set_tag(v___x_3291_, 7);
lean_ctor_set(v___x_3291_, 1, v___x_3293_);
lean_ctor_set(v___x_3291_, 0, v_msgData_3279_);
v___x_3295_ = v___x_3291_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_msgData_3279_);
lean_ctor_set(v_reuseFailAlloc_3303_, 1, v___x_3293_);
v___x_3295_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v_msgData_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3296_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__2);
v___x_3297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3295_);
lean_ctor_set(v___x_3297_, 1, v___x_3296_);
v___x_3298_ = l_Lean_MessageData_ofSyntax(v_after_3289_);
v___x_3299_ = l_Lean_indentD(v___x_3298_);
v_msgData_3300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_3300_, 0, v___x_3297_);
lean_ctor_set(v_msgData_3300_, 1, v___x_3299_);
v___x_3301_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9(v_msgData_3300_, v_macroStack_3280_);
v___x_3302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3301_);
return v___x_3302_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___boxed(lean_object* v_msgData_3306_, lean_object* v_macroStack_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg(v_msgData_3306_, v_macroStack_3307_, v___y_3308_);
lean_dec_ref(v___y_3308_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg(lean_object* v_msg_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_){
_start:
{
lean_object* v_ref_3319_; lean_object* v___x_3320_; lean_object* v_a_3321_; lean_object* v_macroStack_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3333_; 
v_ref_3319_ = lean_ctor_get(v___y_3316_, 5);
v___x_3320_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__6(v_msg_3311_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
v_a_3321_ = lean_ctor_get(v___x_3320_, 0);
lean_inc(v_a_3321_);
lean_dec_ref(v___x_3320_);
v_macroStack_3322_ = lean_ctor_get(v___y_3312_, 1);
lean_inc(v_macroStack_3322_);
lean_dec_ref(v___y_3312_);
lean_inc(v_macroStack_3322_);
v___x_3323_ = l_Lean_Elab_getBetterRef(v_ref_3319_, v_macroStack_3322_);
v___x_3324_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg(v_a_3321_, v_macroStack_3322_, v___y_3316_);
v_a_3325_ = lean_ctor_get(v___x_3324_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3324_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3327_ = v___x_3324_;
v_isShared_3328_ = v_isSharedCheck_3333_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3324_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3333_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3329_; lean_object* v___x_3331_; 
v___x_3329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3323_);
lean_ctor_set(v___x_3329_, 1, v_a_3325_);
if (v_isShared_3328_ == 0)
{
lean_ctor_set_tag(v___x_3327_, 1);
lean_ctor_set(v___x_3327_, 0, v___x_3329_);
v___x_3331_ = v___x_3327_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v___x_3329_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg___boxed(lean_object* v_msg_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg(v_msg_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
lean_dec(v___y_3340_);
lean_dec_ref(v___y_3339_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
lean_dec(v___y_3336_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__3___redArg(lean_object* v_cls_3345_, lean_object* v_msg_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
lean_object* v_ref_3352_; lean_object* v___x_3353_; lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3398_; 
v_ref_3352_ = lean_ctor_get(v___y_3349_, 5);
v___x_3353_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__6(v_msg_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_);
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3356_ = v___x_3353_;
v_isShared_3357_ = v_isSharedCheck_3398_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3353_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3398_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3358_; lean_object* v_traceState_3359_; lean_object* v_env_3360_; lean_object* v_nextMacroScope_3361_; lean_object* v_ngen_3362_; lean_object* v_auxDeclNGen_3363_; lean_object* v_cache_3364_; lean_object* v_messages_3365_; lean_object* v_infoState_3366_; lean_object* v_snapshotTasks_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3397_; 
v___x_3358_ = lean_st_ref_take(v___y_3350_);
v_traceState_3359_ = lean_ctor_get(v___x_3358_, 4);
v_env_3360_ = lean_ctor_get(v___x_3358_, 0);
v_nextMacroScope_3361_ = lean_ctor_get(v___x_3358_, 1);
v_ngen_3362_ = lean_ctor_get(v___x_3358_, 2);
v_auxDeclNGen_3363_ = lean_ctor_get(v___x_3358_, 3);
v_cache_3364_ = lean_ctor_get(v___x_3358_, 5);
v_messages_3365_ = lean_ctor_get(v___x_3358_, 6);
v_infoState_3366_ = lean_ctor_get(v___x_3358_, 7);
v_snapshotTasks_3367_ = lean_ctor_get(v___x_3358_, 8);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3397_ == 0)
{
v___x_3369_ = v___x_3358_;
v_isShared_3370_ = v_isSharedCheck_3397_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_snapshotTasks_3367_);
lean_inc(v_infoState_3366_);
lean_inc(v_messages_3365_);
lean_inc(v_cache_3364_);
lean_inc(v_traceState_3359_);
lean_inc(v_auxDeclNGen_3363_);
lean_inc(v_ngen_3362_);
lean_inc(v_nextMacroScope_3361_);
lean_inc(v_env_3360_);
lean_dec(v___x_3358_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3397_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
uint64_t v_tid_3371_; lean_object* v_traces_3372_; lean_object* v___x_3374_; uint8_t v_isShared_3375_; uint8_t v_isSharedCheck_3396_; 
v_tid_3371_ = lean_ctor_get_uint64(v_traceState_3359_, sizeof(void*)*1);
v_traces_3372_ = lean_ctor_get(v_traceState_3359_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v_traceState_3359_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3374_ = v_traceState_3359_;
v_isShared_3375_ = v_isSharedCheck_3396_;
goto v_resetjp_3373_;
}
else
{
lean_inc(v_traces_3372_);
lean_dec(v_traceState_3359_);
v___x_3374_ = lean_box(0);
v_isShared_3375_ = v_isSharedCheck_3396_;
goto v_resetjp_3373_;
}
v_resetjp_3373_:
{
lean_object* v___x_3376_; double v___x_3377_; uint8_t v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3386_; 
v___x_3376_ = lean_box(0);
v___x_3377_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2);
v___x_3378_ = 0;
v___x_3379_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_3380_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3380_, 0, v_cls_3345_);
lean_ctor_set(v___x_3380_, 1, v___x_3376_);
lean_ctor_set(v___x_3380_, 2, v___x_3379_);
lean_ctor_set_float(v___x_3380_, sizeof(void*)*3, v___x_3377_);
lean_ctor_set_float(v___x_3380_, sizeof(void*)*3 + 8, v___x_3377_);
lean_ctor_set_uint8(v___x_3380_, sizeof(void*)*3 + 16, v___x_3378_);
v___x_3381_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_3382_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3380_);
lean_ctor_set(v___x_3382_, 1, v_a_3354_);
lean_ctor_set(v___x_3382_, 2, v___x_3381_);
lean_inc(v_ref_3352_);
v___x_3383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3383_, 0, v_ref_3352_);
lean_ctor_set(v___x_3383_, 1, v___x_3382_);
v___x_3384_ = l_Lean_PersistentArray_push___redArg(v_traces_3372_, v___x_3383_);
if (v_isShared_3375_ == 0)
{
lean_ctor_set(v___x_3374_, 0, v___x_3384_);
v___x_3386_ = v___x_3374_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3384_);
lean_ctor_set_uint64(v_reuseFailAlloc_3395_, sizeof(void*)*1, v_tid_3371_);
v___x_3386_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
lean_object* v___x_3388_; 
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 4, v___x_3386_);
v___x_3388_ = v___x_3369_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_env_3360_);
lean_ctor_set(v_reuseFailAlloc_3394_, 1, v_nextMacroScope_3361_);
lean_ctor_set(v_reuseFailAlloc_3394_, 2, v_ngen_3362_);
lean_ctor_set(v_reuseFailAlloc_3394_, 3, v_auxDeclNGen_3363_);
lean_ctor_set(v_reuseFailAlloc_3394_, 4, v___x_3386_);
lean_ctor_set(v_reuseFailAlloc_3394_, 5, v_cache_3364_);
lean_ctor_set(v_reuseFailAlloc_3394_, 6, v_messages_3365_);
lean_ctor_set(v_reuseFailAlloc_3394_, 7, v_infoState_3366_);
lean_ctor_set(v_reuseFailAlloc_3394_, 8, v_snapshotTasks_3367_);
v___x_3388_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3392_; 
v___x_3389_ = lean_st_ref_set(v___y_3350_, v___x_3388_);
v___x_3390_ = lean_box(0);
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 0, v___x_3390_);
v___x_3392_ = v___x_3356_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3390_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_cls_3399_, lean_object* v_msg_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
lean_object* v_res_3406_; 
v_res_3406_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__3___redArg(v_cls_3399_, v_msg_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
return v_res_3406_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(lean_object* v_keys_3407_, lean_object* v_i_3408_, lean_object* v_k_3409_){
_start:
{
lean_object* v___x_3410_; uint8_t v___x_3411_; 
v___x_3410_ = lean_array_get_size(v_keys_3407_);
v___x_3411_ = lean_nat_dec_lt(v_i_3408_, v___x_3410_);
if (v___x_3411_ == 0)
{
lean_dec(v_i_3408_);
return v___x_3411_;
}
else
{
lean_object* v_k_x27_3412_; uint8_t v___x_3413_; 
v_k_x27_3412_ = lean_array_fget_borrowed(v_keys_3407_, v_i_3408_);
v___x_3413_ = l_Lean_instBEqExtraModUse_beq(v_k_3409_, v_k_x27_3412_);
if (v___x_3413_ == 0)
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3414_ = lean_unsigned_to_nat(1u);
v___x_3415_ = lean_nat_add(v_i_3408_, v___x_3414_);
lean_dec(v_i_3408_);
v_i_3408_ = v___x_3415_;
goto _start;
}
else
{
lean_dec(v_i_3408_);
return v___x_3413_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_keys_3417_, lean_object* v_i_3418_, lean_object* v_k_3419_){
_start:
{
uint8_t v_res_3420_; lean_object* v_r_3421_; 
v_res_3420_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_keys_3417_, v_i_3418_, v_k_3419_);
lean_dec_ref(v_k_3419_);
lean_dec_ref(v_keys_3417_);
v_r_3421_ = lean_box(v_res_3420_);
return v_r_3421_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_3422_; size_t v___x_3423_; size_t v___x_3424_; 
v___x_3422_ = ((size_t)5ULL);
v___x_3423_ = ((size_t)1ULL);
v___x_3424_ = lean_usize_shift_left(v___x_3423_, v___x_3422_);
return v___x_3424_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_3425_; size_t v___x_3426_; size_t v___x_3427_; 
v___x_3425_ = ((size_t)1ULL);
v___x_3426_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_3427_ = lean_usize_sub(v___x_3426_, v___x_3425_);
return v___x_3427_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_3428_, size_t v_x_3429_, lean_object* v_x_3430_){
_start:
{
if (lean_obj_tag(v_x_3428_) == 0)
{
lean_object* v_es_3431_; lean_object* v___x_3432_; size_t v___x_3433_; size_t v___x_3434_; size_t v___x_3435_; lean_object* v_j_3436_; lean_object* v___x_3437_; 
v_es_3431_ = lean_ctor_get(v_x_3428_, 0);
lean_inc_ref(v_es_3431_);
lean_dec_ref(v_x_3428_);
v___x_3432_ = lean_box(2);
v___x_3433_ = ((size_t)5ULL);
v___x_3434_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_3435_ = lean_usize_land(v_x_3429_, v___x_3434_);
v_j_3436_ = lean_usize_to_nat(v___x_3435_);
v___x_3437_ = lean_array_get(v___x_3432_, v_es_3431_, v_j_3436_);
lean_dec(v_j_3436_);
lean_dec_ref(v_es_3431_);
switch(lean_obj_tag(v___x_3437_))
{
case 0:
{
lean_object* v_key_3438_; uint8_t v___x_3439_; 
v_key_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_key_3438_);
lean_dec_ref(v___x_3437_);
v___x_3439_ = l_Lean_instBEqExtraModUse_beq(v_x_3430_, v_key_3438_);
lean_dec(v_key_3438_);
return v___x_3439_;
}
case 1:
{
lean_object* v_node_3440_; size_t v___x_3441_; 
v_node_3440_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_node_3440_);
lean_dec_ref(v___x_3437_);
v___x_3441_ = lean_usize_shift_right(v_x_3429_, v___x_3433_);
v_x_3428_ = v_node_3440_;
v_x_3429_ = v___x_3441_;
goto _start;
}
default: 
{
uint8_t v___x_3443_; 
v___x_3443_ = 0;
return v___x_3443_;
}
}
}
else
{
lean_object* v_ks_3444_; lean_object* v___x_3445_; uint8_t v___x_3446_; 
v_ks_3444_ = lean_ctor_get(v_x_3428_, 0);
lean_inc_ref(v_ks_3444_);
lean_dec_ref(v_x_3428_);
v___x_3445_ = lean_unsigned_to_nat(0u);
v___x_3446_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_ks_3444_, v___x_3445_, v_x_3430_);
lean_dec_ref(v_ks_3444_);
return v___x_3446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_3447_, lean_object* v_x_3448_, lean_object* v_x_3449_){
_start:
{
size_t v_x_11946__boxed_3450_; uint8_t v_res_3451_; lean_object* v_r_3452_; 
v_x_11946__boxed_3450_ = lean_unbox_usize(v_x_3448_);
lean_dec(v_x_3448_);
v_res_3451_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg(v_x_3447_, v_x_11946__boxed_3450_, v_x_3449_);
lean_dec_ref(v_x_3449_);
v_r_3452_ = lean_box(v_res_3451_);
return v_r_3452_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3453_, lean_object* v_x_3454_){
_start:
{
uint64_t v___x_3455_; size_t v___x_3456_; uint8_t v___x_3457_; 
v___x_3455_ = l_Lean_instHashableExtraModUse_hash(v_x_3454_);
v___x_3456_ = lean_uint64_to_usize(v___x_3455_);
v___x_3457_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg(v_x_3453_, v___x_3456_, v_x_3454_);
return v___x_3457_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3458_, lean_object* v_x_3459_){
_start:
{
uint8_t v_res_3460_; lean_object* v_r_3461_; 
v_res_3460_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___redArg(v_x_3458_, v_x_3459_);
lean_dec_ref(v_x_3459_);
v_r_3461_ = lean_box(v_res_3460_);
return v_r_3461_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg(lean_object* v_cls_3462_, lean_object* v___y_3463_){
_start:
{
lean_object* v_options_3465_; uint8_t v_hasTrace_3466_; 
v_options_3465_ = lean_ctor_get(v___y_3463_, 2);
v_hasTrace_3466_ = lean_ctor_get_uint8(v_options_3465_, sizeof(void*)*1);
if (v_hasTrace_3466_ == 0)
{
lean_object* v___x_3467_; lean_object* v___x_3468_; 
lean_dec(v_cls_3462_);
v___x_3467_ = lean_box(v_hasTrace_3466_);
v___x_3468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3467_);
return v___x_3468_;
}
else
{
lean_object* v_inheritedTraceOptions_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; uint8_t v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v_inheritedTraceOptions_3469_ = lean_ctor_get(v___y_3463_, 13);
v___x_3470_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__1));
v___x_3471_ = l_Lean_Name_append(v___x_3470_, v_cls_3462_);
v___x_3472_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3469_, v_options_3465_, v___x_3471_);
lean_dec(v___x_3471_);
v___x_3473_ = lean_box(v___x_3472_);
v___x_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3474_, 0, v___x_3473_);
return v___x_3474_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_cls_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_){
_start:
{
lean_object* v_res_3478_; 
v_res_3478_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg(v_cls_3475_, v___y_3476_);
lean_dec_ref(v___y_3476_);
return v_res_3478_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; 
v___x_3481_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__1));
v___x_3482_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__0));
v___x_3483_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_3482_, v___x_3481_);
return v___x_3483_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3484_; 
v___x_3484_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3484_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3485_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__3);
v___x_3486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3485_);
return v___x_3486_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3487_; lean_object* v___x_3488_; 
v___x_3487_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4);
v___x_3488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3488_, 0, v___x_3487_);
lean_ctor_set(v___x_3488_, 1, v___x_3487_);
return v___x_3488_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
v___x_3489_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4);
v___x_3490_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3489_);
lean_ctor_set(v___x_3490_, 1, v___x_3489_);
lean_ctor_set(v___x_3490_, 2, v___x_3489_);
lean_ctor_set(v___x_3490_, 3, v___x_3489_);
lean_ctor_set(v___x_3490_, 4, v___x_3489_);
lean_ctor_set(v___x_3490_, 5, v___x_3489_);
return v___x_3490_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; 
v___x_3495_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__9));
v___x_3496_ = l_Lean_stringToMessageData(v___x_3495_);
return v___x_3496_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3498_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__11));
v___x_3499_ = l_Lean_stringToMessageData(v___x_3498_);
return v___x_3499_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__13(void){
_start:
{
lean_object* v___x_3500_; lean_object* v___x_3501_; 
v___x_3500_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_3501_ = l_Lean_stringToMessageData(v___x_3500_);
return v___x_3501_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__15(void){
_start:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; 
v___x_3503_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__14));
v___x_3504_ = l_Lean_stringToMessageData(v___x_3503_);
return v___x_3504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0(lean_object* v_mod_3509_, uint8_t v_isMeta_3510_, lean_object* v_hint_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_, lean_object* v___y_3517_){
_start:
{
lean_object* v___x_3519_; lean_object* v_env_3520_; uint8_t v_isExporting_3521_; lean_object* v___x_3522_; lean_object* v_env_3523_; lean_object* v___x_3524_; lean_object* v_entry_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___x_3571_; uint8_t v___x_3572_; 
v___x_3519_ = lean_st_ref_get(v___y_3517_);
v_env_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc_ref(v_env_3520_);
lean_dec(v___x_3519_);
v_isExporting_3521_ = lean_ctor_get_uint8(v_env_3520_, sizeof(void*)*8);
lean_dec_ref(v_env_3520_);
v___x_3522_ = lean_st_ref_get(v___y_3517_);
v_env_3523_ = lean_ctor_get(v___x_3522_, 0);
lean_inc_ref(v_env_3523_);
lean_dec(v___x_3522_);
v___x_3524_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__2);
lean_inc(v_mod_3509_);
v_entry_3525_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3525_, 0, v_mod_3509_);
lean_ctor_set_uint8(v_entry_3525_, sizeof(void*)*1, v_isExporting_3521_);
lean_ctor_set_uint8(v_entry_3525_, sizeof(void*)*1 + 1, v_isMeta_3510_);
v___x_3526_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3527_ = lean_box(1);
v___x_3528_ = lean_box(0);
v___x_3571_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3524_, v___x_3526_, v_env_3523_, v___x_3527_, v___x_3528_);
v___x_3572_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___redArg(v___x_3571_, v_entry_3525_);
if (v___x_3572_ == 0)
{
lean_object* v_cls_3573_; lean_object* v___x_3574_; lean_object* v_a_3575_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3582_; lean_object* v___y_3583_; uint8_t v___x_3595_; 
v_cls_3573_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__8));
v___x_3574_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg(v_cls_3573_, v___y_3516_);
v_a_3575_ = lean_ctor_get(v___x_3574_, 0);
lean_inc(v_a_3575_);
lean_dec_ref(v___x_3574_);
v___x_3595_ = lean_unbox(v_a_3575_);
lean_dec(v_a_3575_);
if (v___x_3595_ == 0)
{
lean_dec(v_hint_3511_);
lean_dec(v_mod_3509_);
v___y_3530_ = v___y_3515_;
v___y_3531_ = v___y_3517_;
goto v___jp_3529_;
}
else
{
lean_object* v___x_3596_; lean_object* v___y_3598_; 
v___x_3596_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__15);
if (v_isExporting_3521_ == 0)
{
lean_object* v___x_3605_; 
v___x_3605_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__18));
v___y_3598_ = v___x_3605_;
goto v___jp_3597_;
}
else
{
lean_object* v___x_3606_; 
v___x_3606_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__19));
v___y_3598_ = v___x_3606_;
goto v___jp_3597_;
}
v___jp_3597_:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3599_ = l_Lean_stringToMessageData(v___y_3598_);
v___x_3600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3596_);
lean_ctor_set(v___x_3600_, 1, v___x_3599_);
v___x_3601_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1);
v___x_3602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3600_);
lean_ctor_set(v___x_3602_, 1, v___x_3601_);
if (v_isMeta_3510_ == 0)
{
lean_object* v___x_3603_; 
v___x_3603_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__16));
v___y_3582_ = v___x_3602_;
v___y_3583_ = v___x_3603_;
goto v___jp_3581_;
}
else
{
lean_object* v___x_3604_; 
v___x_3604_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__17));
v___y_3582_ = v___x_3602_;
v___y_3583_ = v___x_3604_;
goto v___jp_3581_;
}
}
}
v___jp_3576_:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3579_, 0, v___y_3577_);
lean_ctor_set(v___x_3579_, 1, v___y_3578_);
v___x_3580_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__3___redArg(v_cls_3573_, v___x_3579_, v___y_3514_, v___y_3515_, v___y_3516_, v___y_3517_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_dec_ref(v___x_3580_);
v___y_3530_ = v___y_3515_;
v___y_3531_ = v___y_3517_;
goto v___jp_3529_;
}
else
{
lean_dec_ref(v_entry_3525_);
return v___x_3580_;
}
}
v___jp_3581_:
{
lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; uint8_t v___x_3590_; 
v___x_3584_ = l_Lean_stringToMessageData(v___y_3583_);
v___x_3585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3585_, 0, v___y_3582_);
lean_ctor_set(v___x_3585_, 1, v___x_3584_);
v___x_3586_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__10);
v___x_3587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3585_);
lean_ctor_set(v___x_3587_, 1, v___x_3586_);
v___x_3588_ = l_Lean_MessageData_ofName(v_mod_3509_);
v___x_3589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3587_);
lean_ctor_set(v___x_3589_, 1, v___x_3588_);
v___x_3590_ = l_Lean_Name_isAnonymous(v_hint_3511_);
if (v___x_3590_ == 0)
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3591_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__12);
v___x_3592_ = l_Lean_MessageData_ofName(v_hint_3511_);
v___x_3593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3591_);
lean_ctor_set(v___x_3593_, 1, v___x_3592_);
v___y_3577_ = v___x_3589_;
v___y_3578_ = v___x_3593_;
goto v___jp_3576_;
}
else
{
lean_object* v___x_3594_; 
lean_dec(v_hint_3511_);
v___x_3594_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__13);
v___y_3577_ = v___x_3589_;
v___y_3578_ = v___x_3594_;
goto v___jp_3576_;
}
}
}
else
{
lean_object* v___x_3607_; lean_object* v___x_3608_; 
lean_dec_ref(v_entry_3525_);
lean_dec(v_hint_3511_);
lean_dec(v_mod_3509_);
v___x_3607_ = lean_box(0);
v___x_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3607_);
return v___x_3608_;
}
v___jp_3529_:
{
lean_object* v___x_3532_; lean_object* v_toEnvExtension_3533_; lean_object* v_env_3534_; lean_object* v_nextMacroScope_3535_; lean_object* v_ngen_3536_; lean_object* v_auxDeclNGen_3537_; lean_object* v_traceState_3538_; lean_object* v_messages_3539_; lean_object* v_infoState_3540_; lean_object* v_snapshotTasks_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3569_; 
v___x_3532_ = lean_st_ref_take(v___y_3531_);
v_toEnvExtension_3533_ = lean_ctor_get(v___x_3526_, 0);
lean_inc_ref(v_toEnvExtension_3533_);
v_env_3534_ = lean_ctor_get(v___x_3532_, 0);
v_nextMacroScope_3535_ = lean_ctor_get(v___x_3532_, 1);
v_ngen_3536_ = lean_ctor_get(v___x_3532_, 2);
v_auxDeclNGen_3537_ = lean_ctor_get(v___x_3532_, 3);
v_traceState_3538_ = lean_ctor_get(v___x_3532_, 4);
v_messages_3539_ = lean_ctor_get(v___x_3532_, 6);
v_infoState_3540_ = lean_ctor_get(v___x_3532_, 7);
v_snapshotTasks_3541_ = lean_ctor_get(v___x_3532_, 8);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3569_ == 0)
{
lean_object* v_unused_3570_; 
v_unused_3570_ = lean_ctor_get(v___x_3532_, 5);
lean_dec(v_unused_3570_);
v___x_3543_ = v___x_3532_;
v_isShared_3544_ = v_isSharedCheck_3569_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_snapshotTasks_3541_);
lean_inc(v_infoState_3540_);
lean_inc(v_messages_3539_);
lean_inc(v_traceState_3538_);
lean_inc(v_auxDeclNGen_3537_);
lean_inc(v_ngen_3536_);
lean_inc(v_nextMacroScope_3535_);
lean_inc(v_env_3534_);
lean_dec(v___x_3532_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3569_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v_asyncMode_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3549_; 
v_asyncMode_3545_ = lean_ctor_get(v_toEnvExtension_3533_, 2);
lean_inc(v_asyncMode_3545_);
lean_dec_ref(v_toEnvExtension_3533_);
v___x_3546_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3526_, v_env_3534_, v_entry_3525_, v_asyncMode_3545_, v___x_3528_);
lean_dec(v_asyncMode_3545_);
v___x_3547_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__5);
if (v_isShared_3544_ == 0)
{
lean_ctor_set(v___x_3543_, 5, v___x_3547_);
lean_ctor_set(v___x_3543_, 0, v___x_3546_);
v___x_3549_ = v___x_3543_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3546_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v_nextMacroScope_3535_);
lean_ctor_set(v_reuseFailAlloc_3568_, 2, v_ngen_3536_);
lean_ctor_set(v_reuseFailAlloc_3568_, 3, v_auxDeclNGen_3537_);
lean_ctor_set(v_reuseFailAlloc_3568_, 4, v_traceState_3538_);
lean_ctor_set(v_reuseFailAlloc_3568_, 5, v___x_3547_);
lean_ctor_set(v_reuseFailAlloc_3568_, 6, v_messages_3539_);
lean_ctor_set(v_reuseFailAlloc_3568_, 7, v_infoState_3540_);
lean_ctor_set(v_reuseFailAlloc_3568_, 8, v_snapshotTasks_3541_);
v___x_3549_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v_mctx_3552_; lean_object* v_zetaDeltaFVarIds_3553_; lean_object* v_postponed_3554_; lean_object* v_diag_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3566_; 
v___x_3550_ = lean_st_ref_set(v___y_3531_, v___x_3549_);
v___x_3551_ = lean_st_ref_take(v___y_3530_);
v_mctx_3552_ = lean_ctor_get(v___x_3551_, 0);
v_zetaDeltaFVarIds_3553_ = lean_ctor_get(v___x_3551_, 2);
v_postponed_3554_ = lean_ctor_get(v___x_3551_, 3);
v_diag_3555_ = lean_ctor_get(v___x_3551_, 4);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3566_ == 0)
{
lean_object* v_unused_3567_; 
v_unused_3567_ = lean_ctor_get(v___x_3551_, 1);
lean_dec(v_unused_3567_);
v___x_3557_ = v___x_3551_;
v_isShared_3558_ = v_isSharedCheck_3566_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_diag_3555_);
lean_inc(v_postponed_3554_);
lean_inc(v_zetaDeltaFVarIds_3553_);
lean_inc(v_mctx_3552_);
lean_dec(v___x_3551_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3566_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3559_; lean_object* v___x_3561_; 
v___x_3559_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__6);
if (v_isShared_3558_ == 0)
{
lean_ctor_set(v___x_3557_, 1, v___x_3559_);
v___x_3561_ = v___x_3557_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_mctx_3552_);
lean_ctor_set(v_reuseFailAlloc_3565_, 1, v___x_3559_);
lean_ctor_set(v_reuseFailAlloc_3565_, 2, v_zetaDeltaFVarIds_3553_);
lean_ctor_set(v_reuseFailAlloc_3565_, 3, v_postponed_3554_);
lean_ctor_set(v_reuseFailAlloc_3565_, 4, v_diag_3555_);
v___x_3561_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3562_ = lean_st_ref_set(v___y_3530_, v___x_3561_);
v___x_3563_ = lean_box(0);
v___x_3564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3564_, 0, v___x_3563_);
return v___x_3564_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___boxed(lean_object* v_mod_3609_, lean_object* v_isMeta_3610_, lean_object* v_hint_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
uint8_t v_isMeta_boxed_3619_; lean_object* v_res_3620_; 
v_isMeta_boxed_3619_ = lean_unbox(v_isMeta_3610_);
v_res_3620_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0(v_mod_3609_, v_isMeta_boxed_3619_, v_hint_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec_ref(v___y_3612_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__1(lean_object* v___x_3621_, lean_object* v_declName_3622_, lean_object* v_as_3623_, size_t v_sz_3624_, size_t v_i_3625_, lean_object* v_b_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
uint8_t v___x_3634_; 
v___x_3634_ = lean_usize_dec_lt(v_i_3625_, v_sz_3624_);
if (v___x_3634_ == 0)
{
lean_object* v___x_3635_; 
lean_dec(v_declName_3622_);
v___x_3635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3635_, 0, v_b_3626_);
return v___x_3635_;
}
else
{
lean_object* v___x_3636_; lean_object* v_modules_3637_; lean_object* v___x_3638_; lean_object* v_a_3639_; lean_object* v___x_3640_; lean_object* v_toImport_3641_; lean_object* v_module_3642_; uint8_t v___x_3643_; lean_object* v___x_3644_; 
v___x_3636_ = l_Lean_Environment_header(v___x_3621_);
v_modules_3637_ = lean_ctor_get(v___x_3636_, 3);
lean_inc_ref(v_modules_3637_);
lean_dec_ref(v___x_3636_);
v___x_3638_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3639_ = lean_array_uget_borrowed(v_as_3623_, v_i_3625_);
v___x_3640_ = lean_array_get(v___x_3638_, v_modules_3637_, v_a_3639_);
lean_dec_ref(v_modules_3637_);
v_toImport_3641_ = lean_ctor_get(v___x_3640_, 0);
lean_inc_ref(v_toImport_3641_);
lean_dec(v___x_3640_);
v_module_3642_ = lean_ctor_get(v_toImport_3641_, 0);
lean_inc(v_module_3642_);
lean_dec_ref(v_toImport_3641_);
v___x_3643_ = 0;
lean_inc(v_declName_3622_);
v___x_3644_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0(v_module_3642_, v___x_3643_, v_declName_3622_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v___x_3645_; size_t v___x_3646_; size_t v___x_3647_; 
lean_dec_ref(v___x_3644_);
v___x_3645_ = lean_box(0);
v___x_3646_ = ((size_t)1ULL);
v___x_3647_ = lean_usize_add(v_i_3625_, v___x_3646_);
v_i_3625_ = v___x_3647_;
v_b_3626_ = v___x_3645_;
goto _start;
}
else
{
lean_dec(v_declName_3622_);
return v___x_3644_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__1___boxed(lean_object* v___x_3649_, lean_object* v_declName_3650_, lean_object* v_as_3651_, lean_object* v_sz_3652_, lean_object* v_i_3653_, lean_object* v_b_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_){
_start:
{
size_t v_sz_boxed_3662_; size_t v_i_boxed_3663_; lean_object* v_res_3664_; 
v_sz_boxed_3662_ = lean_unbox_usize(v_sz_3652_);
lean_dec(v_sz_3652_);
v_i_boxed_3663_ = lean_unbox_usize(v_i_3653_);
lean_dec(v_i_3653_);
v_res_3664_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__1(v___x_3649_, v_declName_3650_, v_as_3651_, v_sz_boxed_3662_, v_i_boxed_3663_, v_b_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
lean_dec(v___y_3660_);
lean_dec_ref(v___y_3659_);
lean_dec(v___y_3658_);
lean_dec_ref(v___y_3657_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
lean_dec_ref(v_as_3651_);
lean_dec_ref(v___x_3649_);
return v_res_3664_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__6___redArg(lean_object* v_a_3665_, lean_object* v_x_3666_){
_start:
{
if (lean_obj_tag(v_x_3666_) == 0)
{
lean_object* v___x_3667_; 
v___x_3667_ = lean_box(0);
return v___x_3667_;
}
else
{
lean_object* v_key_3668_; lean_object* v_value_3669_; lean_object* v_tail_3670_; uint8_t v___x_3671_; 
v_key_3668_ = lean_ctor_get(v_x_3666_, 0);
v_value_3669_ = lean_ctor_get(v_x_3666_, 1);
v_tail_3670_ = lean_ctor_get(v_x_3666_, 2);
v___x_3671_ = lean_name_eq(v_key_3668_, v_a_3665_);
if (v___x_3671_ == 0)
{
v_x_3666_ = v_tail_3670_;
goto _start;
}
else
{
lean_object* v___x_3673_; 
lean_inc(v_value_3669_);
v___x_3673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3673_, 0, v_value_3669_);
return v___x_3673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_a_3674_, lean_object* v_x_3675_){
_start:
{
lean_object* v_res_3676_; 
v_res_3676_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__6___redArg(v_a_3674_, v_x_3675_);
lean_dec(v_x_3675_);
lean_dec(v_a_3674_);
return v_res_3676_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3677_; uint64_t v___x_3678_; 
v___x_3677_ = lean_unsigned_to_nat(1723u);
v___x_3678_ = lean_uint64_of_nat(v___x_3677_);
return v___x_3678_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg(lean_object* v_m_3679_, lean_object* v_a_3680_){
_start:
{
lean_object* v_buckets_3681_; lean_object* v___x_3682_; uint64_t v___y_3684_; 
v_buckets_3681_ = lean_ctor_get(v_m_3679_, 1);
v___x_3682_ = lean_array_get_size(v_buckets_3681_);
if (lean_obj_tag(v_a_3680_) == 0)
{
uint64_t v___x_3698_; 
v___x_3698_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg___closed__0);
v___y_3684_ = v___x_3698_;
goto v___jp_3683_;
}
else
{
uint64_t v_hash_3699_; 
v_hash_3699_ = lean_ctor_get_uint64(v_a_3680_, sizeof(void*)*2);
v___y_3684_ = v_hash_3699_;
goto v___jp_3683_;
}
v___jp_3683_:
{
uint64_t v___x_3685_; uint64_t v___x_3686_; uint64_t v_fold_3687_; uint64_t v___x_3688_; uint64_t v___x_3689_; uint64_t v___x_3690_; size_t v___x_3691_; size_t v___x_3692_; size_t v___x_3693_; size_t v___x_3694_; size_t v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; 
v___x_3685_ = 32ULL;
v___x_3686_ = lean_uint64_shift_right(v___y_3684_, v___x_3685_);
v_fold_3687_ = lean_uint64_xor(v___y_3684_, v___x_3686_);
v___x_3688_ = 16ULL;
v___x_3689_ = lean_uint64_shift_right(v_fold_3687_, v___x_3688_);
v___x_3690_ = lean_uint64_xor(v_fold_3687_, v___x_3689_);
v___x_3691_ = lean_uint64_to_usize(v___x_3690_);
v___x_3692_ = lean_usize_of_nat(v___x_3682_);
v___x_3693_ = ((size_t)1ULL);
v___x_3694_ = lean_usize_sub(v___x_3692_, v___x_3693_);
v___x_3695_ = lean_usize_land(v___x_3691_, v___x_3694_);
v___x_3696_ = lean_array_uget_borrowed(v_buckets_3681_, v___x_3695_);
v___x_3697_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__6___redArg(v_a_3680_, v___x_3696_);
return v___x_3697_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg___boxed(lean_object* v_m_3700_, lean_object* v_a_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg(v_m_3700_, v_a_3701_);
lean_dec(v_a_3701_);
lean_dec_ref(v_m_3700_);
return v_res_3702_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3705_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__1));
v___x_3706_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__0));
v___x_3707_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_3706_, v___x_3705_);
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0(lean_object* v_declName_3710_, uint8_t v_isMeta_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_){
_start:
{
lean_object* v___x_3719_; lean_object* v_env_3723_; lean_object* v___y_3725_; lean_object* v___x_3738_; 
v___x_3719_ = lean_st_ref_get(v___y_3717_);
v_env_3723_ = lean_ctor_get(v___x_3719_, 0);
lean_inc_ref(v_env_3723_);
lean_dec(v___x_3719_);
v___x_3738_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3723_, v_declName_3710_);
if (lean_obj_tag(v___x_3738_) == 0)
{
lean_dec_ref(v_env_3723_);
lean_dec(v_declName_3710_);
goto v___jp_3720_;
}
else
{
lean_object* v_val_3739_; lean_object* v___x_3740_; lean_object* v_modules_3741_; lean_object* v___x_3742_; uint8_t v___x_3743_; 
v_val_3739_ = lean_ctor_get(v___x_3738_, 0);
lean_inc(v_val_3739_);
lean_dec_ref(v___x_3738_);
v___x_3740_ = l_Lean_Environment_header(v_env_3723_);
v_modules_3741_ = lean_ctor_get(v___x_3740_, 3);
lean_inc_ref(v_modules_3741_);
lean_dec_ref(v___x_3740_);
v___x_3742_ = lean_array_get_size(v_modules_3741_);
v___x_3743_ = lean_nat_dec_lt(v_val_3739_, v___x_3742_);
if (v___x_3743_ == 0)
{
lean_dec_ref(v_modules_3741_);
lean_dec(v_val_3739_);
lean_dec_ref(v_env_3723_);
lean_dec(v_declName_3710_);
goto v___jp_3720_;
}
else
{
lean_object* v___x_3744_; lean_object* v_env_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; uint8_t v___y_3749_; 
v___x_3744_ = lean_st_ref_get(v___y_3717_);
v_env_3745_ = lean_ctor_get(v___x_3744_, 0);
lean_inc_ref(v_env_3745_);
lean_dec(v___x_3744_);
v___x_3746_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__2);
v___x_3747_ = lean_array_fget(v_modules_3741_, v_val_3739_);
lean_dec(v_val_3739_);
lean_dec_ref(v_modules_3741_);
if (v_isMeta_3711_ == 0)
{
lean_dec_ref(v_env_3745_);
v___y_3749_ = v_isMeta_3711_;
goto v___jp_3748_;
}
else
{
uint8_t v___x_3760_; 
lean_inc(v_declName_3710_);
v___x_3760_ = l_Lean_isMarkedMeta(v_env_3745_, v_declName_3710_);
if (v___x_3760_ == 0)
{
v___y_3749_ = v_isMeta_3711_;
goto v___jp_3748_;
}
else
{
uint8_t v___x_3761_; 
v___x_3761_ = 0;
v___y_3749_ = v___x_3761_;
goto v___jp_3748_;
}
}
v___jp_3748_:
{
lean_object* v_toImport_3750_; lean_object* v_module_3751_; lean_object* v___x_3752_; 
v_toImport_3750_ = lean_ctor_get(v___x_3747_, 0);
lean_inc_ref(v_toImport_3750_);
lean_dec(v___x_3747_);
v_module_3751_ = lean_ctor_get(v_toImport_3750_, 0);
lean_inc(v_module_3751_);
lean_dec_ref(v_toImport_3750_);
lean_inc(v_declName_3710_);
v___x_3752_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0(v_module_3751_, v___y_3749_, v_declName_3710_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
if (lean_obj_tag(v___x_3752_) == 0)
{
lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; 
lean_dec_ref(v___x_3752_);
v___x_3753_ = l_Lean_indirectModUseExt;
v___x_3754_ = lean_box(1);
v___x_3755_ = lean_box(0);
lean_inc_ref(v_env_3723_);
v___x_3756_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3746_, v___x_3753_, v_env_3723_, v___x_3754_, v___x_3755_);
v___x_3757_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg(v___x_3756_, v_declName_3710_);
lean_dec(v___x_3756_);
if (lean_obj_tag(v___x_3757_) == 0)
{
lean_object* v___x_3758_; 
v___x_3758_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__3));
v___y_3725_ = v___x_3758_;
goto v___jp_3724_;
}
else
{
lean_object* v_val_3759_; 
v_val_3759_ = lean_ctor_get(v___x_3757_, 0);
lean_inc(v_val_3759_);
lean_dec_ref(v___x_3757_);
v___y_3725_ = v_val_3759_;
goto v___jp_3724_;
}
}
else
{
lean_dec_ref(v_env_3723_);
lean_dec(v_declName_3710_);
return v___x_3752_;
}
}
}
}
v___jp_3720_:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3721_ = lean_box(0);
v___x_3722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3721_);
return v___x_3722_;
}
v___jp_3724_:
{
lean_object* v___x_3726_; size_t v_sz_3727_; size_t v___x_3728_; lean_object* v___x_3729_; 
v___x_3726_ = lean_box(0);
v_sz_3727_ = lean_array_size(v___y_3725_);
v___x_3728_ = ((size_t)0ULL);
v___x_3729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__1(v_env_3723_, v_declName_3710_, v___y_3725_, v_sz_3727_, v___x_3728_, v___x_3726_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
lean_dec_ref(v___y_3725_);
lean_dec_ref(v_env_3723_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3736_; 
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3729_);
if (v_isSharedCheck_3736_ == 0)
{
lean_object* v_unused_3737_; 
v_unused_3737_ = lean_ctor_get(v___x_3729_, 0);
lean_dec(v_unused_3737_);
v___x_3731_ = v___x_3729_;
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
else
{
lean_dec(v___x_3729_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3734_; 
if (v_isShared_3732_ == 0)
{
lean_ctor_set(v___x_3731_, 0, v___x_3726_);
v___x_3734_ = v___x_3731_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v___x_3726_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
return v___x_3734_;
}
}
}
else
{
return v___x_3729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___boxed(lean_object* v_declName_3762_, lean_object* v_isMeta_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
uint8_t v_isMeta_boxed_3771_; lean_object* v_res_3772_; 
v_isMeta_boxed_3771_ = lean_unbox(v_isMeta_3763_);
v_res_3772_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0(v_declName_3762_, v_isMeta_boxed_3771_, v___y_3764_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_, v___y_3769_);
lean_dec(v___y_3769_);
lean_dec_ref(v___y_3768_);
lean_dec(v___y_3767_);
lean_dec_ref(v___y_3766_);
lean_dec(v___y_3765_);
lean_dec_ref(v___y_3764_);
return v_res_3772_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__1(void){
_start:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3774_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__0));
v___x_3775_ = l_Lean_stringToMessageData(v___x_3774_);
return v___x_3775_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__3(void){
_start:
{
lean_object* v___x_3777_; lean_object* v___x_3778_; 
v___x_3777_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__2));
v___x_3778_ = l_Lean_stringToMessageData(v___x_3777_);
return v___x_3778_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__5(void){
_start:
{
lean_object* v___x_3780_; lean_object* v___x_3781_; 
v___x_3780_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__4));
v___x_3781_ = l_Lean_stringToMessageData(v___x_3780_);
return v___x_3781_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__7(void){
_start:
{
lean_object* v___x_3783_; lean_object* v___x_3784_; 
v___x_3783_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__6));
v___x_3784_ = l_Lean_stringToMessageData(v___x_3783_);
return v___x_3784_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__8(void){
_start:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3785_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_));
v___x_3786_ = l_Lean_MessageData_ofName(v___x_3785_);
return v___x_3786_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__9(void){
_start:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3787_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__8, &l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__8);
v___x_3788_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__7, &l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__7);
v___x_3789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3788_);
lean_ctor_set(v___x_3789_, 1, v___x_3787_);
return v___x_3789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg(lean_object* v_optConfig_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_){
_start:
{
lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; uint8_t v___y_3816_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; uint8_t v_recover_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; uint8_t v___x_3843_; uint8_t v___x_3844_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; 
v_recover_3838_ = lean_ctor_get_uint8(v_a_3798_, sizeof(void*)*1);
lean_inc(v_optConfig_3797_);
v___x_3839_ = l_Lean_Parser_Tactic_getConfigItems(v_optConfig_3797_);
v___x_3840_ = l_Lean_Elab_Tactic_mkConfigItemViews(v___x_3839_);
v___x_3841_ = lean_array_get_size(v___x_3840_);
v___x_3842_ = lean_unsigned_to_nat(0u);
v___x_3843_ = lean_nat_dec_eq(v___x_3841_, v___x_3842_);
v___x_3844_ = 1;
if (v___x_3843_ == 0)
{
lean_object* v___x_3896_; lean_object* v_fileName_3897_; lean_object* v_fileMap_3898_; lean_object* v_options_3899_; lean_object* v_currRecDepth_3900_; lean_object* v_maxRecDepth_3901_; lean_object* v_ref_3902_; lean_object* v_currNamespace_3903_; lean_object* v_openDecls_3904_; lean_object* v_initHeartbeats_3905_; lean_object* v_maxHeartbeats_3906_; lean_object* v_quotContext_3907_; lean_object* v_currMacroScope_3908_; uint8_t v_diag_3909_; lean_object* v_cancelTk_x3f_3910_; uint8_t v_suppressElabErrors_3911_; lean_object* v_inheritedTraceOptions_3912_; lean_object* v_env_3913_; lean_object* v_ref_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; uint8_t v___x_3917_; 
v___x_3896_ = lean_st_ref_get(v_a_3804_);
v_fileName_3897_ = lean_ctor_get(v_a_3803_, 0);
v_fileMap_3898_ = lean_ctor_get(v_a_3803_, 1);
v_options_3899_ = lean_ctor_get(v_a_3803_, 2);
v_currRecDepth_3900_ = lean_ctor_get(v_a_3803_, 3);
v_maxRecDepth_3901_ = lean_ctor_get(v_a_3803_, 4);
v_ref_3902_ = lean_ctor_get(v_a_3803_, 5);
v_currNamespace_3903_ = lean_ctor_get(v_a_3803_, 6);
v_openDecls_3904_ = lean_ctor_get(v_a_3803_, 7);
v_initHeartbeats_3905_ = lean_ctor_get(v_a_3803_, 8);
v_maxHeartbeats_3906_ = lean_ctor_get(v_a_3803_, 9);
v_quotContext_3907_ = lean_ctor_get(v_a_3803_, 10);
v_currMacroScope_3908_ = lean_ctor_get(v_a_3803_, 11);
v_diag_3909_ = lean_ctor_get_uint8(v_a_3803_, sizeof(void*)*14);
v_cancelTk_x3f_3910_ = lean_ctor_get(v_a_3803_, 12);
v_suppressElabErrors_3911_ = lean_ctor_get_uint8(v_a_3803_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3912_ = lean_ctor_get(v_a_3803_, 13);
v_env_3913_ = lean_ctor_get(v___x_3896_, 0);
lean_inc_ref(v_env_3913_);
lean_dec(v___x_3896_);
v_ref_3914_ = l_Lean_replaceRef(v_optConfig_3797_, v_ref_3902_);
lean_dec(v_optConfig_3797_);
lean_inc_ref(v_inheritedTraceOptions_3912_);
lean_inc(v_cancelTk_x3f_3910_);
lean_inc(v_currMacroScope_3908_);
lean_inc(v_quotContext_3907_);
lean_inc(v_maxHeartbeats_3906_);
lean_inc(v_initHeartbeats_3905_);
lean_inc(v_openDecls_3904_);
lean_inc(v_currNamespace_3903_);
lean_inc(v_maxRecDepth_3901_);
lean_inc(v_currRecDepth_3900_);
lean_inc_ref(v_options_3899_);
lean_inc_ref(v_fileMap_3898_);
lean_inc_ref(v_fileName_3897_);
v___x_3915_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3915_, 0, v_fileName_3897_);
lean_ctor_set(v___x_3915_, 1, v_fileMap_3898_);
lean_ctor_set(v___x_3915_, 2, v_options_3899_);
lean_ctor_set(v___x_3915_, 3, v_currRecDepth_3900_);
lean_ctor_set(v___x_3915_, 4, v_maxRecDepth_3901_);
lean_ctor_set(v___x_3915_, 5, v_ref_3914_);
lean_ctor_set(v___x_3915_, 6, v_currNamespace_3903_);
lean_ctor_set(v___x_3915_, 7, v_openDecls_3904_);
lean_ctor_set(v___x_3915_, 8, v_initHeartbeats_3905_);
lean_ctor_set(v___x_3915_, 9, v_maxHeartbeats_3906_);
lean_ctor_set(v___x_3915_, 10, v_quotContext_3907_);
lean_ctor_set(v___x_3915_, 11, v_currMacroScope_3908_);
lean_ctor_set(v___x_3915_, 12, v_cancelTk_x3f_3910_);
lean_ctor_set(v___x_3915_, 13, v_inheritedTraceOptions_3912_);
lean_ctor_set_uint8(v___x_3915_, sizeof(void*)*14, v_diag_3909_);
lean_ctor_set_uint8(v___x_3915_, sizeof(void*)*14 + 1, v_suppressElabErrors_3911_);
v___x_3916_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_));
v___x_3917_ = l_Lean_Environment_contains(v_env_3913_, v___x_3916_, v___x_3844_);
if (v___x_3917_ == 0)
{
lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v_a_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3927_; 
lean_dec_ref(v___x_3840_);
v___x_3918_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__9, &l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__9);
lean_inc_ref(v_a_3799_);
v___x_3919_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg(v___x_3918_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_, v___x_3915_, v_a_3804_);
lean_dec_ref(v___x_3915_);
v_a_3920_ = lean_ctor_get(v___x_3919_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3919_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3922_ = v___x_3919_;
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_a_3920_);
lean_dec(v___x_3919_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3925_; 
if (v_isShared_3923_ == 0)
{
v___x_3925_ = v___x_3922_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3920_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
else
{
v___y_3846_ = v_a_3799_;
v___y_3847_ = v_a_3800_;
v___y_3848_ = v_a_3801_;
v___y_3849_ = v_a_3802_;
v___y_3850_ = v___x_3915_;
v___y_3851_ = v_a_3804_;
goto v___jp_3845_;
}
}
else
{
lean_object* v___x_3928_; lean_object* v___x_3929_; 
lean_dec_ref(v___x_3840_);
lean_dec(v_optConfig_3797_);
v___x_3928_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__10));
v___x_3929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3929_, 0, v___x_3928_);
return v___x_3929_;
}
v___jp_3806_:
{
if (v___y_3816_ == 0)
{
lean_object* v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; 
lean_dec_ref(v___y_3807_);
v___x_3817_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__1, &l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__1);
v___x_3818_ = l_Lean_MessageData_ofExpr(v___y_3812_);
v___x_3819_ = l_Lean_indentD(v___x_3818_);
v___x_3820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3820_, 0, v___x_3817_);
lean_ctor_set(v___x_3820_, 1, v___x_3819_);
v___x_3821_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__3, &l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__3);
v___x_3822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3820_);
lean_ctor_set(v___x_3822_, 1, v___x_3821_);
v___x_3823_ = l_Lean_Exception_toMessageData(v___y_3808_);
v___x_3824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3822_);
lean_ctor_set(v___x_3824_, 1, v___x_3823_);
lean_inc_ref(v___y_3811_);
v___x_3825_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg(v___x_3824_, v___y_3811_, v___y_3810_, v___y_3814_, v___y_3809_, v___y_3813_, v___y_3815_);
lean_dec_ref(v___y_3813_);
return v___x_3825_;
}
else
{
lean_dec_ref(v___y_3813_);
lean_dec_ref(v___y_3812_);
lean_dec_ref(v___y_3808_);
return v___y_3807_;
}
}
v___jp_3826_:
{
lean_object* v___x_3834_; 
lean_inc_ref(v___y_3827_);
v___x_3834_ = l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(v___y_3827_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_dec_ref(v___y_3832_);
lean_dec_ref(v___y_3827_);
return v___x_3834_;
}
else
{
lean_object* v_a_3835_; uint8_t v___x_3836_; 
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
lean_inc(v_a_3835_);
v___x_3836_ = l_Lean_Exception_isInterrupt(v_a_3835_);
if (v___x_3836_ == 0)
{
uint8_t v___x_3837_; 
lean_inc(v_a_3835_);
v___x_3837_ = l_Lean_Exception_isRuntime(v_a_3835_);
v___y_3807_ = v___x_3834_;
v___y_3808_ = v_a_3835_;
v___y_3809_ = v___y_3831_;
v___y_3810_ = v___y_3829_;
v___y_3811_ = v___y_3828_;
v___y_3812_ = v___y_3827_;
v___y_3813_ = v___y_3832_;
v___y_3814_ = v___y_3830_;
v___y_3815_ = v___y_3833_;
v___y_3816_ = v___x_3837_;
goto v___jp_3806_;
}
else
{
v___y_3807_ = v___x_3834_;
v___y_3808_ = v_a_3835_;
v___y_3809_ = v___y_3831_;
v___y_3810_ = v___y_3829_;
v___y_3811_ = v___y_3828_;
v___y_3812_ = v___y_3827_;
v___y_3813_ = v___y_3832_;
v___y_3814_ = v___y_3830_;
v___y_3815_ = v___y_3833_;
v___y_3816_ = v___x_3836_;
goto v___jp_3806_;
}
}
}
v___jp_3845_:
{
lean_object* v___x_3852_; lean_object* v___x_3853_; 
v___x_3852_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_));
v___x_3853_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0(v___x_3852_, v___x_3844_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v___x_3854_; 
lean_dec_ref(v___x_3853_);
v___x_3854_ = l_Lean_Elab_Tactic_elabConfig(v_recover_3838_, v___x_3852_, v___x_3840_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v_a_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3879_; 
v_a_3855_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3857_ = v___x_3854_;
v_isShared_3858_ = v_isSharedCheck_3879_;
goto v_resetjp_3856_;
}
else
{
lean_inc(v_a_3855_);
lean_dec(v___x_3854_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3879_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
uint8_t v___x_3859_; 
v___x_3859_ = l_Lean_Expr_hasSyntheticSorry(v_a_3855_);
if (v___x_3859_ == 0)
{
uint8_t v___x_3860_; 
lean_del_object(v___x_3857_);
v___x_3860_ = l_Lean_Expr_hasSorry(v_a_3855_);
if (v___x_3860_ == 0)
{
v___y_3827_ = v_a_3855_;
v___y_3828_ = v___y_3846_;
v___y_3829_ = v___y_3847_;
v___y_3830_ = v___y_3848_;
v___y_3831_ = v___y_3849_;
v___y_3832_ = v___y_3850_;
v___y_3833_ = v___y_3851_;
goto v___jp_3826_;
}
else
{
lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v_a_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3870_; 
lean_dec(v_a_3855_);
v___x_3861_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__5, &l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__5);
lean_inc_ref(v___y_3846_);
v___x_3862_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg(v___x_3861_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_);
lean_dec_ref(v___y_3850_);
v_a_3863_ = lean_ctor_get(v___x_3862_, 0);
v_isSharedCheck_3870_ = !lean_is_exclusive(v___x_3862_);
if (v_isSharedCheck_3870_ == 0)
{
v___x_3865_ = v___x_3862_;
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_a_3863_);
lean_dec(v___x_3862_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3870_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3868_; 
if (v_isShared_3866_ == 0)
{
v___x_3868_ = v___x_3865_;
goto v_reusejp_3867_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_a_3863_);
v___x_3868_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3867_;
}
v_reusejp_3867_:
{
return v___x_3868_;
}
}
}
}
else
{
lean_object* v___x_3871_; lean_object* v___x_3872_; uint8_t v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3877_; 
lean_dec(v_a_3855_);
lean_dec_ref(v___y_3850_);
v___x_3871_ = lean_unsigned_to_nat(100000u);
v___x_3872_ = lean_unsigned_to_nat(2u);
v___x_3873_ = 0;
v___x_3874_ = lean_box(0);
v___x_3875_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_3875_, 0, v___x_3871_);
lean_ctor_set(v___x_3875_, 1, v___x_3872_);
lean_ctor_set(v___x_3875_, 2, v___x_3874_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3, v___x_3843_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 1, v___x_3844_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 2, v___x_3843_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 3, v___x_3843_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 4, v___x_3843_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 5, v___x_3843_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 6, v___x_3873_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 7, v___x_3843_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 8, v___x_3843_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 9, v___x_3843_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 10, v___x_3843_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 11, v___x_3843_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 12, v___x_3844_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 13, v___x_3844_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 14, v___x_3843_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 15, v___x_3843_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 16, v___x_3843_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 17, v___x_3844_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 18, v___x_3844_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 19, v___x_3844_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 20, v___x_3844_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 21, v___x_3844_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 22, v___x_3844_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 23, v___x_3844_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 24, v___x_3844_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 25, v___x_3844_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 26, v___x_3843_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 27, v___x_3843_);
lean_ctor_set_uint8(v___x_3875_, sizeof(void*)*3 + 28, v___x_3843_);
if (v_isShared_3858_ == 0)
{
lean_ctor_set(v___x_3857_, 0, v___x_3875_);
v___x_3877_ = v___x_3857_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v___x_3875_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
lean_dec_ref(v___y_3850_);
v_a_3880_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3882_ = v___x_3854_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3854_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
else
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
lean_dec_ref(v___y_3850_);
lean_dec_ref(v___x_3840_);
v_a_3888_ = lean_ctor_get(v___x_3853_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3853_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3853_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3853_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___boxed(lean_object* v_optConfig_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg(v_optConfig_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_);
lean_dec(v_a_3937_);
lean_dec_ref(v_a_3936_);
lean_dec(v_a_3935_);
lean_dec_ref(v_a_3934_);
lean_dec(v_a_3933_);
lean_dec_ref(v_a_3932_);
lean_dec_ref(v_a_3931_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig(lean_object* v_optConfig_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_){
_start:
{
lean_object* v___x_3950_; 
v___x_3950_ = l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg(v_optConfig_3940_, v_a_3941_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___boxed(lean_object* v_optConfig_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_Lean_Elab_Tactic_NormCast_elabNormCastConfig(v_optConfig_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_);
lean_dec(v_a_3959_);
lean_dec_ref(v_a_3958_);
lean_dec(v_a_3957_);
lean_dec_ref(v_a_3956_);
lean_dec(v_a_3955_);
lean_dec_ref(v_a_3954_);
lean_dec(v_a_3953_);
lean_dec_ref(v_a_3952_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1(lean_object* v_00_u03b1_3962_, lean_object* v_msg_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_){
_start:
{
lean_object* v___x_3971_; 
lean_inc_ref(v___y_3964_);
v___x_3971_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg(v_msg_3963_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___boxed(lean_object* v_00_u03b1_3972_, lean_object* v_msg_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1(v_00_u03b1_3972_, v_msg_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2(lean_object* v_cls_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_){
_start:
{
lean_object* v___x_3990_; 
v___x_3990_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg(v_cls_3982_, v___y_3987_);
return v___x_3990_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_){
_start:
{
lean_object* v_res_3999_; 
v_res_3999_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2(v_cls_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_);
lean_dec(v___y_3997_);
lean_dec_ref(v___y_3996_);
lean_dec(v___y_3995_);
lean_dec_ref(v___y_3994_);
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3992_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2(lean_object* v_00_u03b2_4000_, lean_object* v_m_4001_, lean_object* v_a_4002_){
_start:
{
lean_object* v___x_4003_; 
v___x_4003_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg(v_m_4001_, v_a_4002_);
return v___x_4003_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___boxed(lean_object* v_00_u03b2_4004_, lean_object* v_m_4005_, lean_object* v_a_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2(v_00_u03b2_4004_, v_m_4005_, v_a_4006_);
lean_dec(v_a_4006_);
lean_dec_ref(v_m_4005_);
return v_res_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4(lean_object* v_msgData_4008_, lean_object* v_macroStack_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_){
_start:
{
lean_object* v___x_4017_; 
v___x_4017_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg(v_msgData_4008_, v_macroStack_4009_, v___y_4014_);
return v___x_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___boxed(lean_object* v_msgData_4018_, lean_object* v_macroStack_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4(v_msgData_4018_, v_macroStack_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
return v_res_4027_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4028_, lean_object* v_x_4029_, lean_object* v_x_4030_){
_start:
{
uint8_t v___x_4031_; 
v___x_4031_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___redArg(v_x_4029_, v_x_4030_);
return v___x_4031_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4032_, lean_object* v_x_4033_, lean_object* v_x_4034_){
_start:
{
uint8_t v_res_4035_; lean_object* v_r_4036_; 
v_res_4035_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1(v_00_u03b2_4032_, v_x_4033_, v_x_4034_);
lean_dec_ref(v_x_4034_);
v_r_4036_ = lean_box(v_res_4035_);
return v_r_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__3(lean_object* v_cls_4037_, lean_object* v_msg_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__3___redArg(v_cls_4037_, v_msg_4038_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__3___boxed(lean_object* v_cls_4047_, lean_object* v_msg_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_){
_start:
{
lean_object* v_res_4056_; 
v_res_4056_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__3(v_cls_4047_, v_msg_4048_, v___y_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_, v___y_4054_);
lean_dec(v___y_4054_);
lean_dec_ref(v___y_4053_);
lean_dec(v___y_4052_);
lean_dec_ref(v___y_4051_);
lean_dec(v___y_4050_);
lean_dec_ref(v___y_4049_);
return v_res_4056_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_4057_, lean_object* v_a_4058_, lean_object* v_x_4059_){
_start:
{
lean_object* v___x_4060_; 
v___x_4060_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__6___redArg(v_a_4058_, v_x_4059_);
return v___x_4060_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_4061_, lean_object* v_a_4062_, lean_object* v_x_4063_){
_start:
{
lean_object* v_res_4064_; 
v_res_4064_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__6(v_00_u03b2_4061_, v_a_4062_, v_x_4063_);
lean_dec(v_x_4063_);
lean_dec(v_a_4062_);
return v_res_4064_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_4065_, lean_object* v_x_4066_, size_t v_x_4067_, lean_object* v_x_4068_){
_start:
{
uint8_t v___x_4069_; 
v___x_4069_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg(v_x_4066_, v_x_4067_, v_x_4068_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_4070_, lean_object* v_x_4071_, lean_object* v_x_4072_, lean_object* v_x_4073_){
_start:
{
size_t v_x_13006__boxed_4074_; uint8_t v_res_4075_; lean_object* v_r_4076_; 
v_x_13006__boxed_4074_ = lean_unbox_usize(v_x_4072_);
lean_dec(v_x_4072_);
v_res_4075_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_4070_, v_x_4071_, v_x_13006__boxed_4074_, v_x_4073_);
lean_dec_ref(v_x_4073_);
v_r_4076_ = lean_box(v_res_4075_);
return v_r_4076_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_4077_, lean_object* v_keys_4078_, lean_object* v_vals_4079_, lean_object* v_heq_4080_, lean_object* v_i_4081_, lean_object* v_k_4082_){
_start:
{
uint8_t v___x_4083_; 
v___x_4083_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_keys_4078_, v_i_4081_, v_k_4082_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_4084_, lean_object* v_keys_4085_, lean_object* v_vals_4086_, lean_object* v_heq_4087_, lean_object* v_i_4088_, lean_object* v_k_4089_){
_start:
{
uint8_t v_res_4090_; lean_object* v_r_4091_; 
v_res_4090_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__8(v_00_u03b2_4084_, v_keys_4085_, v_vals_4086_, v_heq_4087_, v_i_4088_, v_k_4089_);
lean_dec_ref(v_k_4089_);
lean_dec_ref(v_vals_4086_);
lean_dec_ref(v_keys_4085_);
v_r_4091_ = lean_box(v_res_4090_);
return v_r_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(lean_object* v_e_4092_, lean_object* v___y_4093_){
_start:
{
uint8_t v___x_4095_; 
v___x_4095_ = l_Lean_Expr_hasMVar(v_e_4092_);
if (v___x_4095_ == 0)
{
lean_object* v___x_4096_; 
v___x_4096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4096_, 0, v_e_4092_);
return v___x_4096_;
}
else
{
lean_object* v___x_4097_; lean_object* v_mctx_4098_; lean_object* v___x_4099_; lean_object* v_fst_4100_; lean_object* v_snd_4101_; lean_object* v___x_4102_; lean_object* v_cache_4103_; lean_object* v_zetaDeltaFVarIds_4104_; lean_object* v_postponed_4105_; lean_object* v_diag_4106_; lean_object* v___x_4108_; uint8_t v_isShared_4109_; uint8_t v_isSharedCheck_4115_; 
v___x_4097_ = lean_st_ref_get(v___y_4093_);
v_mctx_4098_ = lean_ctor_get(v___x_4097_, 0);
lean_inc_ref(v_mctx_4098_);
lean_dec(v___x_4097_);
v___x_4099_ = l_Lean_instantiateMVarsCore(v_mctx_4098_, v_e_4092_);
v_fst_4100_ = lean_ctor_get(v___x_4099_, 0);
lean_inc(v_fst_4100_);
v_snd_4101_ = lean_ctor_get(v___x_4099_, 1);
lean_inc(v_snd_4101_);
lean_dec_ref(v___x_4099_);
v___x_4102_ = lean_st_ref_take(v___y_4093_);
v_cache_4103_ = lean_ctor_get(v___x_4102_, 1);
v_zetaDeltaFVarIds_4104_ = lean_ctor_get(v___x_4102_, 2);
v_postponed_4105_ = lean_ctor_get(v___x_4102_, 3);
v_diag_4106_ = lean_ctor_get(v___x_4102_, 4);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4115_ == 0)
{
lean_object* v_unused_4116_; 
v_unused_4116_ = lean_ctor_get(v___x_4102_, 0);
lean_dec(v_unused_4116_);
v___x_4108_ = v___x_4102_;
v_isShared_4109_ = v_isSharedCheck_4115_;
goto v_resetjp_4107_;
}
else
{
lean_inc(v_diag_4106_);
lean_inc(v_postponed_4105_);
lean_inc(v_zetaDeltaFVarIds_4104_);
lean_inc(v_cache_4103_);
lean_dec(v___x_4102_);
v___x_4108_ = lean_box(0);
v_isShared_4109_ = v_isSharedCheck_4115_;
goto v_resetjp_4107_;
}
v_resetjp_4107_:
{
lean_object* v___x_4111_; 
if (v_isShared_4109_ == 0)
{
lean_ctor_set(v___x_4108_, 0, v_snd_4101_);
v___x_4111_ = v___x_4108_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_snd_4101_);
lean_ctor_set(v_reuseFailAlloc_4114_, 1, v_cache_4103_);
lean_ctor_set(v_reuseFailAlloc_4114_, 2, v_zetaDeltaFVarIds_4104_);
lean_ctor_set(v_reuseFailAlloc_4114_, 3, v_postponed_4105_);
lean_ctor_set(v_reuseFailAlloc_4114_, 4, v_diag_4106_);
v___x_4111_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; 
v___x_4112_ = lean_st_ref_set(v___y_4093_, v___x_4111_);
v___x_4113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4113_, 0, v_fst_4100_);
return v___x_4113_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg___boxed(lean_object* v_e_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_){
_start:
{
lean_object* v_res_4120_; 
v_res_4120_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_e_4117_, v___y_4118_);
lean_dec(v___y_4118_);
return v_res_4120_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0(lean_object* v_e_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
lean_object* v___x_4127_; 
v___x_4127_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_e_4121_, v___y_4123_);
return v___x_4127_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___boxed(lean_object* v_e_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_){
_start:
{
lean_object* v_res_4134_; 
v_res_4134_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0(v_e_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
lean_dec(v___y_4132_);
lean_dec_ref(v___y_4131_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
return v_res_4134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__0(lean_object* v_x_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4146_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___lam__0___closed__0));
v___x_4147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4147_, 0, v___x_4146_);
return v___x_4147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__0___boxed(lean_object* v_x_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
lean_object* v_res_4157_; 
v_res_4157_ = l_Lean_Elab_Tactic_NormCast_derive___lam__0(v_x_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_, v___y_4155_);
lean_dec(v___y_4155_);
lean_dec_ref(v___y_4154_);
lean_dec(v___y_4153_);
lean_dec_ref(v___y_4152_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
lean_dec(v___y_4149_);
lean_dec_ref(v_x_4148_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__1(lean_object* v_e_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_){
_start:
{
lean_object* v___x_4167_; lean_object* v___x_4168_; 
v___x_4167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4167_, 0, v_e_4158_);
v___x_4168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4167_);
return v___x_4168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__1___boxed(lean_object* v_e_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l_Lean_Elab_Tactic_NormCast_derive___lam__1(v_e_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
lean_dec(v___y_4170_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__2(lean_object* v___x_4179_, lean_object* v_x_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4189_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4189_, 0, v___x_4179_);
v___x_4190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4189_);
return v___x_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__2___boxed(lean_object* v___x_4191_, lean_object* v_x_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_){
_start:
{
lean_object* v_res_4201_; 
v_res_4201_ = l_Lean_Elab_Tactic_NormCast_derive___lam__2(v___x_4191_, v_x_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
lean_dec(v___y_4197_);
lean_dec_ref(v___y_4196_);
lean_dec(v___y_4195_);
lean_dec_ref(v___y_4194_);
lean_dec(v___y_4193_);
lean_dec_ref(v_x_4192_);
return v_res_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__3(lean_object* v___x_4202_, lean_object* v_x_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
lean_object* v___x_4212_; 
v___x_4212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4212_, 0, v___x_4202_);
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__3___boxed(lean_object* v___x_4213_, lean_object* v_x_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v_res_4223_; 
v_res_4223_ = l_Lean_Elab_Tactic_NormCast_derive___lam__3(v___x_4213_, v_x_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec_ref(v_x_4214_);
return v_res_4223_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__0(void){
_start:
{
lean_object* v___x_4224_; lean_object* v___x_4225_; 
v___x_4224_ = l_Lean_bombEmoji;
v___x_4225_ = l_Lean_stringToMessageData(v___x_4224_);
return v___x_4225_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__1(void){
_start:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; 
v___x_4226_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1);
v___x_4227_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__0, &l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__0_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__0);
v___x_4228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4228_, 0, v___x_4227_);
lean_ctor_set(v___x_4228_, 1, v___x_4226_);
return v___x_4228_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__3(void){
_start:
{
lean_object* v___x_4230_; lean_object* v___x_4231_; 
v___x_4230_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__2));
v___x_4231_ = l_Lean_stringToMessageData(v___x_4230_);
return v___x_4231_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__5(void){
_start:
{
lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4233_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__4));
v___x_4234_ = l_Lean_stringToMessageData(v___x_4233_);
return v___x_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__4(lean_object* v_phase_4235_, lean_object* v_x_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_){
_start:
{
if (lean_obj_tag(v_x_4236_) == 0)
{
lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4251_; 
v_isSharedCheck_4251_ = !lean_is_exclusive(v_x_4236_);
if (v_isSharedCheck_4251_ == 0)
{
lean_object* v_unused_4252_; 
v_unused_4252_ = lean_ctor_get(v_x_4236_, 0);
lean_dec(v_unused_4252_);
v___x_4243_ = v_x_4236_;
v_isShared_4244_ = v_isSharedCheck_4251_;
goto v_resetjp_4242_;
}
else
{
lean_dec(v_x_4236_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4251_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4249_; 
v___x_4245_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__1, &l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__1);
v___x_4246_ = l_Lean_stringToMessageData(v_phase_4235_);
v___x_4247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4247_, 0, v___x_4245_);
lean_ctor_set(v___x_4247_, 1, v___x_4246_);
if (v_isShared_4244_ == 0)
{
lean_ctor_set(v___x_4243_, 0, v___x_4247_);
v___x_4249_ = v___x_4243_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v___x_4247_);
v___x_4249_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
return v___x_4249_;
}
}
}
else
{
lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4268_; 
v_a_4253_ = lean_ctor_get(v_x_4236_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v_x_4236_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4255_ = v_x_4236_;
v_isShared_4256_ = v_isSharedCheck_4268_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v_x_4236_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4268_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v_expr_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4266_; 
v_expr_4257_ = lean_ctor_get(v_a_4253_, 0);
lean_inc_ref(v_expr_4257_);
lean_dec(v_a_4253_);
v___x_4258_ = l_Lean_MessageData_ofExpr(v_expr_4257_);
v___x_4259_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__3, &l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__3_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__3);
v___x_4260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4260_, 0, v___x_4258_);
lean_ctor_set(v___x_4260_, 1, v___x_4259_);
v___x_4261_ = l_Lean_stringToMessageData(v_phase_4235_);
v___x_4262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4262_, 0, v___x_4260_);
lean_ctor_set(v___x_4262_, 1, v___x_4261_);
v___x_4263_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__5, &l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__5);
v___x_4264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4264_, 0, v___x_4262_);
lean_ctor_set(v___x_4264_, 1, v___x_4263_);
if (v_isShared_4256_ == 0)
{
lean_ctor_set_tag(v___x_4255_, 0);
lean_ctor_set(v___x_4255_, 0, v___x_4264_);
v___x_4266_ = v___x_4255_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v___x_4264_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__4___boxed(lean_object* v_phase_4269_, lean_object* v_x_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_){
_start:
{
lean_object* v_res_4276_; 
v_res_4276_ = l_Lean_Elab_Tactic_NormCast_derive___lam__4(v_phase_4269_, v_x_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_);
lean_dec(v___y_4274_);
lean_dec_ref(v___y_4273_);
lean_dec(v___y_4272_);
lean_dec_ref(v___y_4271_);
return v_res_4276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__5(lean_object* v___x_4277_, uint8_t v___x_4278_, lean_object* v_phase_4279_, lean_object* v_k_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_){
_start:
{
lean_object* v_options_4286_; uint8_t v_hasTrace_4287_; 
v_options_4286_ = lean_ctor_get(v___y_4283_, 2);
v_hasTrace_4287_ = lean_ctor_get_uint8(v_options_4286_, sizeof(void*)*1);
if (v_hasTrace_4287_ == 0)
{
lean_object* v___x_4288_; 
lean_dec_ref(v_phase_4279_);
lean_dec(v___x_4277_);
lean_inc(v___y_4284_);
lean_inc_ref(v___y_4283_);
lean_inc(v___y_4282_);
lean_inc_ref(v___y_4281_);
v___x_4288_ = lean_apply_5(v_k_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, lean_box(0));
return v___x_4288_;
}
else
{
lean_object* v___x_4289_; lean_object* v_a_4290_; lean_object* v___f_4291_; lean_object* v___x_4292_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v_a_4296_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v_a_4312_; uint8_t v___x_4363_; 
lean_inc(v___x_4277_);
v___x_4289_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___x_4277_, v___y_4283_);
v_a_4290_ = lean_ctor_get(v___x_4289_, 0);
lean_inc(v_a_4290_);
lean_dec_ref(v___x_4289_);
v___f_4291_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4291_, 0, v_phase_4279_);
v___x_4292_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_4363_ = lean_unbox(v_a_4290_);
if (v___x_4363_ == 0)
{
lean_object* v___x_4364_; uint8_t v___x_4365_; 
v___x_4364_ = l_Lean_trace_profiler;
v___x_4365_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_4286_, v___x_4364_);
if (v___x_4365_ == 0)
{
lean_object* v___x_4366_; 
lean_dec_ref(v___f_4291_);
lean_dec(v_a_4290_);
lean_dec(v___x_4277_);
lean_inc(v___y_4284_);
lean_inc_ref(v___y_4283_);
lean_inc(v___y_4282_);
lean_inc_ref(v___y_4281_);
v___x_4366_ = lean_apply_5(v_k_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, lean_box(0));
return v___x_4366_;
}
else
{
goto v___jp_4322_;
}
}
else
{
goto v___jp_4322_;
}
v___jp_4293_:
{
lean_object* v___x_4297_; double v___x_4298_; double v___x_4299_; double v___x_4300_; double v___x_4301_; double v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; uint8_t v___x_4307_; lean_object* v___x_4308_; 
v___x_4297_ = lean_io_mono_nanos_now();
v___x_4298_ = lean_float_of_nat(v___y_4295_);
v___x_4299_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1);
v___x_4300_ = lean_float_div(v___x_4298_, v___x_4299_);
v___x_4301_ = lean_float_of_nat(v___x_4297_);
v___x_4302_ = lean_float_div(v___x_4301_, v___x_4299_);
v___x_4303_ = lean_box_float(v___x_4300_);
v___x_4304_ = lean_box_float(v___x_4302_);
v___x_4305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4305_, 0, v___x_4303_);
lean_ctor_set(v___x_4305_, 1, v___x_4304_);
v___x_4306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4306_, 0, v_a_4296_);
lean_ctor_set(v___x_4306_, 1, v___x_4305_);
v___x_4307_ = lean_unbox(v_a_4290_);
lean_dec(v_a_4290_);
v___x_4308_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4277_, v___x_4278_, v___x_4292_, v_options_4286_, v___x_4307_, v___y_4294_, v___f_4291_, v___x_4306_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
return v___x_4308_;
}
v___jp_4309_:
{
lean_object* v___x_4313_; double v___x_4314_; double v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; uint8_t v___x_4320_; lean_object* v___x_4321_; 
v___x_4313_ = lean_io_get_num_heartbeats();
v___x_4314_ = lean_float_of_nat(v___y_4311_);
v___x_4315_ = lean_float_of_nat(v___x_4313_);
v___x_4316_ = lean_box_float(v___x_4314_);
v___x_4317_ = lean_box_float(v___x_4315_);
v___x_4318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4318_, 0, v___x_4316_);
lean_ctor_set(v___x_4318_, 1, v___x_4317_);
v___x_4319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4319_, 0, v_a_4312_);
lean_ctor_set(v___x_4319_, 1, v___x_4318_);
v___x_4320_ = lean_unbox(v_a_4290_);
lean_dec(v_a_4290_);
v___x_4321_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4277_, v___x_4278_, v___x_4292_, v_options_4286_, v___x_4320_, v___y_4310_, v___f_4291_, v___x_4319_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
return v___x_4321_;
}
v___jp_4322_:
{
lean_object* v___x_4323_; lean_object* v_a_4324_; lean_object* v___x_4325_; uint8_t v___x_4326_; 
v___x_4323_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg(v___y_4284_);
v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
lean_inc(v_a_4324_);
lean_dec_ref(v___x_4323_);
v___x_4325_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4326_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_4286_, v___x_4325_);
if (v___x_4326_ == 0)
{
lean_object* v___x_4327_; lean_object* v___x_4328_; 
v___x_4327_ = lean_io_mono_nanos_now();
lean_inc(v___y_4284_);
lean_inc_ref(v___y_4283_);
lean_inc(v___y_4282_);
lean_inc_ref(v___y_4281_);
v___x_4328_ = lean_apply_5(v_k_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, lean_box(0));
if (lean_obj_tag(v___x_4328_) == 0)
{
lean_object* v_a_4329_; lean_object* v___x_4331_; uint8_t v_isShared_4332_; uint8_t v_isSharedCheck_4336_; 
v_a_4329_ = lean_ctor_get(v___x_4328_, 0);
v_isSharedCheck_4336_ = !lean_is_exclusive(v___x_4328_);
if (v_isSharedCheck_4336_ == 0)
{
v___x_4331_ = v___x_4328_;
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
else
{
lean_inc(v_a_4329_);
lean_dec(v___x_4328_);
v___x_4331_ = lean_box(0);
v_isShared_4332_ = v_isSharedCheck_4336_;
goto v_resetjp_4330_;
}
v_resetjp_4330_:
{
lean_object* v___x_4334_; 
if (v_isShared_4332_ == 0)
{
lean_ctor_set_tag(v___x_4331_, 1);
v___x_4334_ = v___x_4331_;
goto v_reusejp_4333_;
}
else
{
lean_object* v_reuseFailAlloc_4335_; 
v_reuseFailAlloc_4335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4335_, 0, v_a_4329_);
v___x_4334_ = v_reuseFailAlloc_4335_;
goto v_reusejp_4333_;
}
v_reusejp_4333_:
{
v___y_4294_ = v_a_4324_;
v___y_4295_ = v___x_4327_;
v_a_4296_ = v___x_4334_;
goto v___jp_4293_;
}
}
}
else
{
lean_object* v_a_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4344_; 
v_a_4337_ = lean_ctor_get(v___x_4328_, 0);
v_isSharedCheck_4344_ = !lean_is_exclusive(v___x_4328_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4339_ = v___x_4328_;
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_a_4337_);
lean_dec(v___x_4328_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4344_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v___x_4342_; 
if (v_isShared_4340_ == 0)
{
lean_ctor_set_tag(v___x_4339_, 0);
v___x_4342_ = v___x_4339_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4343_; 
v_reuseFailAlloc_4343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4343_, 0, v_a_4337_);
v___x_4342_ = v_reuseFailAlloc_4343_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
v___y_4294_ = v_a_4324_;
v___y_4295_ = v___x_4327_;
v_a_4296_ = v___x_4342_;
goto v___jp_4293_;
}
}
}
}
else
{
lean_object* v___x_4345_; lean_object* v___x_4346_; 
v___x_4345_ = lean_io_get_num_heartbeats();
lean_inc(v___y_4284_);
lean_inc_ref(v___y_4283_);
lean_inc(v___y_4282_);
lean_inc_ref(v___y_4281_);
v___x_4346_ = lean_apply_5(v_k_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_, lean_box(0));
if (lean_obj_tag(v___x_4346_) == 0)
{
lean_object* v_a_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4354_; 
v_a_4347_ = lean_ctor_get(v___x_4346_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4346_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4349_ = v___x_4346_;
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_a_4347_);
lean_dec(v___x_4346_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4354_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4352_; 
if (v_isShared_4350_ == 0)
{
lean_ctor_set_tag(v___x_4349_, 1);
v___x_4352_ = v___x_4349_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4347_);
v___x_4352_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
v___y_4310_ = v_a_4324_;
v___y_4311_ = v___x_4345_;
v_a_4312_ = v___x_4352_;
goto v___jp_4309_;
}
}
}
else
{
lean_object* v_a_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4362_; 
v_a_4355_ = lean_ctor_get(v___x_4346_, 0);
v_isSharedCheck_4362_ = !lean_is_exclusive(v___x_4346_);
if (v_isSharedCheck_4362_ == 0)
{
v___x_4357_ = v___x_4346_;
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_a_4355_);
lean_dec(v___x_4346_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4360_; 
if (v_isShared_4358_ == 0)
{
lean_ctor_set_tag(v___x_4357_, 0);
v___x_4360_ = v___x_4357_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_a_4355_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
v___y_4310_ = v_a_4324_;
v___y_4311_ = v___x_4345_;
v_a_4312_ = v___x_4360_;
goto v___jp_4309_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__5___boxed(lean_object* v___x_4367_, lean_object* v___x_4368_, lean_object* v_phase_4369_, lean_object* v_k_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_){
_start:
{
uint8_t v___x_30801__boxed_4376_; lean_object* v_res_4377_; 
v___x_30801__boxed_4376_ = lean_unbox(v___x_4368_);
v_res_4377_ = l_Lean_Elab_Tactic_NormCast_derive___lam__5(v___x_4367_, v___x_30801__boxed_4376_, v_phase_4369_, v_k_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
lean_dec(v___y_4372_);
lean_dec_ref(v___y_4371_);
return v_res_4377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__6(lean_object* v___x_4378_, uint8_t v___x_4379_, lean_object* v_e_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_){
_start:
{
lean_object* v_a_4390_; lean_object* v___y_4394_; lean_object* v___x_4404_; 
lean_inc_ref(v_e_4380_);
v___x_4404_ = l_Lean_Elab_Tactic_NormCast_numeralToCoe(v_e_4380_, v___y_4384_, v___y_4385_, v___y_4386_, v___y_4387_);
if (lean_obj_tag(v___x_4404_) == 0)
{
lean_dec_ref(v_e_4380_);
lean_dec(v___x_4378_);
v___y_4394_ = v___x_4404_;
goto v___jp_4393_;
}
else
{
lean_object* v_a_4405_; uint8_t v___y_4407_; uint8_t v___x_4409_; 
v_a_4405_ = lean_ctor_get(v___x_4404_, 0);
lean_inc(v_a_4405_);
v___x_4409_ = l_Lean_Exception_isInterrupt(v_a_4405_);
if (v___x_4409_ == 0)
{
uint8_t v___x_4410_; 
v___x_4410_ = l_Lean_Exception_isRuntime(v_a_4405_);
v___y_4407_ = v___x_4410_;
goto v___jp_4406_;
}
else
{
lean_dec(v_a_4405_);
v___y_4407_ = v___x_4409_;
goto v___jp_4406_;
}
v___jp_4406_:
{
if (v___y_4407_ == 0)
{
lean_object* v___x_4408_; 
lean_dec_ref(v___x_4404_);
v___x_4408_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4408_, 0, v_e_4380_);
lean_ctor_set(v___x_4408_, 1, v___x_4378_);
lean_ctor_set_uint8(v___x_4408_, sizeof(void*)*2, v___x_4379_);
v_a_4390_ = v___x_4408_;
goto v___jp_4389_;
}
else
{
lean_dec_ref(v_e_4380_);
lean_dec(v___x_4378_);
v___y_4394_ = v___x_4404_;
goto v___jp_4393_;
}
}
}
v___jp_4389_:
{
lean_object* v___x_4391_; lean_object* v___x_4392_; 
v___x_4391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4391_, 0, v_a_4390_);
v___x_4392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4392_, 0, v___x_4391_);
return v___x_4392_;
}
v___jp_4393_:
{
if (lean_obj_tag(v___y_4394_) == 0)
{
lean_object* v_a_4395_; 
v_a_4395_ = lean_ctor_get(v___y_4394_, 0);
lean_inc(v_a_4395_);
lean_dec_ref(v___y_4394_);
v_a_4390_ = v_a_4395_;
goto v___jp_4389_;
}
else
{
lean_object* v_a_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4403_; 
v_a_4396_ = lean_ctor_get(v___y_4394_, 0);
v_isSharedCheck_4403_ = !lean_is_exclusive(v___y_4394_);
if (v_isSharedCheck_4403_ == 0)
{
v___x_4398_ = v___y_4394_;
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_a_4396_);
lean_dec(v___y_4394_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4403_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v___x_4401_; 
if (v_isShared_4399_ == 0)
{
v___x_4401_ = v___x_4398_;
goto v_reusejp_4400_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_a_4396_);
v___x_4401_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4400_;
}
v_reusejp_4400_:
{
return v___x_4401_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__6___boxed(lean_object* v___x_4411_, lean_object* v___x_4412_, lean_object* v_e_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_){
_start:
{
uint8_t v___x_30983__boxed_4422_; lean_object* v_res_4423_; 
v___x_30983__boxed_4422_ = lean_unbox(v___x_4412_);
v_res_4423_ = l_Lean_Elab_Tactic_NormCast_derive___lam__6(v___x_4411_, v___x_30983__boxed_4422_, v_e_4413_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_, v___y_4420_);
lean_dec(v___y_4420_);
lean_dec_ref(v___y_4419_);
lean_dec(v___y_4418_);
lean_dec_ref(v___y_4417_);
lean_dec(v___y_4416_);
lean_dec_ref(v___y_4415_);
lean_dec(v___y_4414_);
return v_res_4423_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__0(void){
_start:
{
lean_object* v___x_4424_; 
v___x_4424_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4424_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1(void){
_start:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; 
v___x_4425_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__0, &l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__0_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__0);
v___x_4426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4426_, 0, v___x_4425_);
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__7(lean_object* v_config_4427_, lean_object* v___x_4428_, lean_object* v_a_4429_, lean_object* v___x_4430_, lean_object* v___f_4431_, lean_object* v___f_4432_, lean_object* v___f_4433_, lean_object* v___f_4434_, lean_object* v___f_4435_, uint8_t v___x_4436_, lean_object* v_a_4437_, lean_object* v___x_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
lean_object* v___x_4444_; 
v___x_4444_ = l_Lean_Meta_Simp_mkContext___redArg(v_config_4427_, v___x_4428_, v_a_4429_, v___y_4439_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4444_) == 0)
{
lean_object* v_a_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; size_t v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; 
v_a_4445_ = lean_ctor_get(v___x_4444_, 0);
lean_inc(v_a_4445_);
lean_dec_ref(v___x_4444_);
v___x_4446_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1, &l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1);
lean_inc(v___x_4430_);
v___x_4447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4447_, 0, v___x_4446_);
lean_ctor_set(v___x_4447_, 1, v___x_4430_);
v___x_4448_ = lean_unsigned_to_nat(32u);
v___x_4449_ = lean_mk_empty_array_with_capacity(v___x_4448_);
v___x_4450_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8);
v___x_4451_ = ((size_t)5ULL);
lean_inc(v___x_4430_);
v___x_4452_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4452_, 0, v___x_4450_);
lean_ctor_set(v___x_4452_, 1, v___x_4449_);
lean_ctor_set(v___x_4452_, 2, v___x_4430_);
lean_ctor_set(v___x_4452_, 3, v___x_4430_);
lean_ctor_set_usize(v___x_4452_, 4, v___x_4451_);
v___x_4453_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4453_, 0, v___x_4446_);
lean_ctor_set(v___x_4453_, 1, v___x_4446_);
lean_ctor_set(v___x_4453_, 2, v___x_4446_);
lean_ctor_set(v___x_4453_, 3, v___x_4452_);
v___x_4454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4454_, 0, v___x_4447_);
lean_ctor_set(v___x_4454_, 1, v___x_4453_);
v___x_4455_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4455_, 0, v___f_4431_);
lean_ctor_set(v___x_4455_, 1, v___f_4432_);
lean_ctor_set(v___x_4455_, 2, v___f_4433_);
lean_ctor_set(v___x_4455_, 3, v___f_4434_);
lean_ctor_set(v___x_4455_, 4, v___f_4435_);
lean_ctor_set_uint8(v___x_4455_, sizeof(void*)*5, v___x_4436_);
v___x_4456_ = l_Lean_Meta_Simp_main(v_a_4437_, v_a_4445_, v___x_4454_, v___x_4455_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
if (lean_obj_tag(v___x_4456_) == 0)
{
lean_object* v_a_4457_; lean_object* v_fst_4458_; lean_object* v___x_4459_; 
v_a_4457_ = lean_ctor_get(v___x_4456_, 0);
lean_inc(v_a_4457_);
lean_dec_ref(v___x_4456_);
v_fst_4458_ = lean_ctor_get(v_a_4457_, 0);
lean_inc(v_fst_4458_);
lean_dec(v_a_4457_);
v___x_4459_ = l_Lean_Meta_Simp_Result_mkEqTrans(v___x_4438_, v_fst_4458_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_);
return v___x_4459_;
}
else
{
lean_object* v_a_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4467_; 
lean_dec_ref(v___x_4438_);
v_a_4460_ = lean_ctor_get(v___x_4456_, 0);
v_isSharedCheck_4467_ = !lean_is_exclusive(v___x_4456_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4462_ = v___x_4456_;
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_a_4460_);
lean_dec(v___x_4456_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4465_; 
if (v_isShared_4463_ == 0)
{
v___x_4465_ = v___x_4462_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_a_4460_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
return v___x_4465_;
}
}
}
}
else
{
lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4475_; 
lean_dec_ref(v___x_4438_);
lean_dec_ref(v_a_4437_);
lean_dec_ref(v___f_4435_);
lean_dec_ref(v___f_4434_);
lean_dec_ref(v___f_4433_);
lean_dec_ref(v___f_4432_);
lean_dec_ref(v___f_4431_);
lean_dec(v___x_4430_);
v_a_4468_ = lean_ctor_get(v___x_4444_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4470_ = v___x_4444_;
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4444_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4473_; 
if (v_isShared_4471_ == 0)
{
v___x_4473_ = v___x_4470_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__7___boxed(lean_object** _args){
lean_object* v_config_4476_ = _args[0];
lean_object* v___x_4477_ = _args[1];
lean_object* v_a_4478_ = _args[2];
lean_object* v___x_4479_ = _args[3];
lean_object* v___f_4480_ = _args[4];
lean_object* v___f_4481_ = _args[5];
lean_object* v___f_4482_ = _args[6];
lean_object* v___f_4483_ = _args[7];
lean_object* v___f_4484_ = _args[8];
lean_object* v___x_4485_ = _args[9];
lean_object* v_a_4486_ = _args[10];
lean_object* v___x_4487_ = _args[11];
lean_object* v___y_4488_ = _args[12];
lean_object* v___y_4489_ = _args[13];
lean_object* v___y_4490_ = _args[14];
lean_object* v___y_4491_ = _args[15];
lean_object* v___y_4492_ = _args[16];
_start:
{
uint8_t v___x_31074__boxed_4493_; lean_object* v_res_4494_; 
v___x_31074__boxed_4493_ = lean_unbox(v___x_4485_);
v_res_4494_ = l_Lean_Elab_Tactic_NormCast_derive___lam__7(v_config_4476_, v___x_4477_, v_a_4478_, v___x_4479_, v___f_4480_, v___f_4481_, v___f_4482_, v___f_4483_, v___f_4484_, v___x_31074__boxed_4493_, v_a_4486_, v___x_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_);
lean_dec(v___y_4491_);
lean_dec_ref(v___y_4490_);
lean_dec(v___y_4489_);
lean_dec_ref(v___y_4488_);
return v_res_4494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__12(lean_object* v_up_4495_, lean_object* v_config_4496_, lean_object* v___x_4497_, lean_object* v_a_4498_, lean_object* v_a_4499_, lean_object* v___x_4500_, lean_object* v___f_4501_, lean_object* v___f_4502_, lean_object* v___f_4503_, lean_object* v___f_4504_, uint8_t v___x_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_){
_start:
{
lean_object* v___x_4511_; 
v___x_4511_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_up_4495_, v___y_4509_);
if (lean_obj_tag(v___x_4511_) == 0)
{
lean_object* v_a_4512_; lean_object* v___x_4513_; 
v_a_4512_ = lean_ctor_get(v___x_4511_, 0);
lean_inc(v_a_4512_);
lean_dec_ref(v___x_4511_);
v___x_4513_ = l_Lean_Meta_Simp_mkContext___redArg(v_config_4496_, v___x_4497_, v_a_4498_, v___y_4506_, v___y_4508_, v___y_4509_);
if (lean_obj_tag(v___x_4513_) == 0)
{
lean_object* v_a_4514_; lean_object* v_expr_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; size_t v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; 
v_a_4514_ = lean_ctor_get(v___x_4513_, 0);
lean_inc(v_a_4514_);
lean_dec_ref(v___x_4513_);
v_expr_4515_ = lean_ctor_get(v_a_4499_, 0);
v___x_4516_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_upwardAndElim___boxed), 10, 1);
lean_closure_set(v___x_4516_, 0, v_a_4512_);
v___x_4517_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1, &l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1);
lean_inc(v___x_4500_);
v___x_4518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4517_);
lean_ctor_set(v___x_4518_, 1, v___x_4500_);
v___x_4519_ = lean_unsigned_to_nat(32u);
v___x_4520_ = lean_mk_empty_array_with_capacity(v___x_4519_);
v___x_4521_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8);
v___x_4522_ = ((size_t)5ULL);
lean_inc(v___x_4500_);
v___x_4523_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4523_, 0, v___x_4521_);
lean_ctor_set(v___x_4523_, 1, v___x_4520_);
lean_ctor_set(v___x_4523_, 2, v___x_4500_);
lean_ctor_set(v___x_4523_, 3, v___x_4500_);
lean_ctor_set_usize(v___x_4523_, 4, v___x_4522_);
v___x_4524_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4524_, 0, v___x_4517_);
lean_ctor_set(v___x_4524_, 1, v___x_4517_);
lean_ctor_set(v___x_4524_, 2, v___x_4517_);
lean_ctor_set(v___x_4524_, 3, v___x_4523_);
v___x_4525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4525_, 0, v___x_4518_);
lean_ctor_set(v___x_4525_, 1, v___x_4524_);
v___x_4526_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4526_, 0, v___f_4501_);
lean_ctor_set(v___x_4526_, 1, v___x_4516_);
lean_ctor_set(v___x_4526_, 2, v___f_4502_);
lean_ctor_set(v___x_4526_, 3, v___f_4503_);
lean_ctor_set(v___x_4526_, 4, v___f_4504_);
lean_ctor_set_uint8(v___x_4526_, sizeof(void*)*5, v___x_4505_);
lean_inc_ref(v_expr_4515_);
v___x_4527_ = l_Lean_Meta_Simp_main(v_expr_4515_, v_a_4514_, v___x_4525_, v___x_4526_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_);
if (lean_obj_tag(v___x_4527_) == 0)
{
lean_object* v_a_4528_; lean_object* v_fst_4529_; lean_object* v___x_4530_; 
v_a_4528_ = lean_ctor_get(v___x_4527_, 0);
lean_inc(v_a_4528_);
lean_dec_ref(v___x_4527_);
v_fst_4529_ = lean_ctor_get(v_a_4528_, 0);
lean_inc(v_fst_4529_);
lean_dec(v_a_4528_);
v___x_4530_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_4499_, v_fst_4529_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_);
return v___x_4530_;
}
else
{
lean_object* v_a_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4538_; 
lean_dec_ref(v_a_4499_);
v_a_4531_ = lean_ctor_get(v___x_4527_, 0);
v_isSharedCheck_4538_ = !lean_is_exclusive(v___x_4527_);
if (v_isSharedCheck_4538_ == 0)
{
v___x_4533_ = v___x_4527_;
v_isShared_4534_ = v_isSharedCheck_4538_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_a_4531_);
lean_dec(v___x_4527_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4538_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
lean_object* v___x_4536_; 
if (v_isShared_4534_ == 0)
{
v___x_4536_ = v___x_4533_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_a_4531_);
v___x_4536_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
return v___x_4536_;
}
}
}
}
else
{
lean_object* v_a_4539_; lean_object* v___x_4541_; uint8_t v_isShared_4542_; uint8_t v_isSharedCheck_4546_; 
lean_dec(v_a_4512_);
lean_dec_ref(v___f_4504_);
lean_dec_ref(v___f_4503_);
lean_dec_ref(v___f_4502_);
lean_dec_ref(v___f_4501_);
lean_dec(v___x_4500_);
lean_dec_ref(v_a_4499_);
v_a_4539_ = lean_ctor_get(v___x_4513_, 0);
v_isSharedCheck_4546_ = !lean_is_exclusive(v___x_4513_);
if (v_isSharedCheck_4546_ == 0)
{
v___x_4541_ = v___x_4513_;
v_isShared_4542_ = v_isSharedCheck_4546_;
goto v_resetjp_4540_;
}
else
{
lean_inc(v_a_4539_);
lean_dec(v___x_4513_);
v___x_4541_ = lean_box(0);
v_isShared_4542_ = v_isSharedCheck_4546_;
goto v_resetjp_4540_;
}
v_resetjp_4540_:
{
lean_object* v___x_4544_; 
if (v_isShared_4542_ == 0)
{
v___x_4544_ = v___x_4541_;
goto v_reusejp_4543_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v_a_4539_);
v___x_4544_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4543_;
}
v_reusejp_4543_:
{
return v___x_4544_;
}
}
}
}
else
{
lean_object* v_a_4547_; lean_object* v___x_4549_; uint8_t v_isShared_4550_; uint8_t v_isSharedCheck_4554_; 
lean_dec_ref(v___f_4504_);
lean_dec_ref(v___f_4503_);
lean_dec_ref(v___f_4502_);
lean_dec_ref(v___f_4501_);
lean_dec(v___x_4500_);
lean_dec_ref(v_a_4499_);
lean_dec_ref(v_a_4498_);
lean_dec_ref(v___x_4497_);
lean_dec_ref(v_config_4496_);
v_a_4547_ = lean_ctor_get(v___x_4511_, 0);
v_isSharedCheck_4554_ = !lean_is_exclusive(v___x_4511_);
if (v_isSharedCheck_4554_ == 0)
{
v___x_4549_ = v___x_4511_;
v_isShared_4550_ = v_isSharedCheck_4554_;
goto v_resetjp_4548_;
}
else
{
lean_inc(v_a_4547_);
lean_dec(v___x_4511_);
v___x_4549_ = lean_box(0);
v_isShared_4550_ = v_isSharedCheck_4554_;
goto v_resetjp_4548_;
}
v_resetjp_4548_:
{
lean_object* v___x_4552_; 
if (v_isShared_4550_ == 0)
{
v___x_4552_ = v___x_4549_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v_a_4547_);
v___x_4552_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
return v___x_4552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__12___boxed(lean_object* v_up_4555_, lean_object* v_config_4556_, lean_object* v___x_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v___x_4560_, lean_object* v___f_4561_, lean_object* v___f_4562_, lean_object* v___f_4563_, lean_object* v___f_4564_, lean_object* v___x_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_){
_start:
{
uint8_t v___x_31193__boxed_4571_; lean_object* v_res_4572_; 
v___x_31193__boxed_4571_ = lean_unbox(v___x_4565_);
v_res_4572_ = l_Lean_Elab_Tactic_NormCast_derive___lam__12(v_up_4555_, v_config_4556_, v___x_4557_, v_a_4558_, v_a_4559_, v___x_4560_, v___f_4561_, v___f_4562_, v___f_4563_, v___f_4564_, v___x_31193__boxed_4571_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_);
lean_dec(v___y_4569_);
lean_dec_ref(v___y_4568_);
lean_dec(v___y_4567_);
lean_dec_ref(v___y_4566_);
lean_dec_ref(v_up_4555_);
return v_res_4572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__8(lean_object* v_squash_4573_, lean_object* v_config_4574_, lean_object* v_a_4575_, lean_object* v_a_4576_, lean_object* v___x_4577_, lean_object* v_a_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_){
_start:
{
lean_object* v___x_4584_; 
v___x_4584_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_squash_4573_, v___y_4582_);
if (lean_obj_tag(v___x_4584_) == 0)
{
lean_object* v_a_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; 
v_a_4585_ = lean_ctor_get(v___x_4584_, 0);
lean_inc(v_a_4585_);
lean_dec_ref(v___x_4584_);
v___x_4586_ = lean_unsigned_to_nat(1u);
v___x_4587_ = lean_mk_empty_array_with_capacity(v___x_4586_);
v___x_4588_ = lean_array_push(v___x_4587_, v_a_4585_);
v___x_4589_ = l_Lean_Meta_Simp_mkContext___redArg(v_config_4574_, v___x_4588_, v_a_4575_, v___y_4579_, v___y_4581_, v___y_4582_);
if (lean_obj_tag(v___x_4589_) == 0)
{
lean_object* v_a_4590_; lean_object* v_expr_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; size_t v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; 
v_a_4590_ = lean_ctor_get(v___x_4589_, 0);
lean_inc(v_a_4590_);
lean_dec_ref(v___x_4589_);
v_expr_4591_ = lean_ctor_get(v_a_4576_, 0);
v___x_4592_ = lean_box(0);
v___x_4593_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1, &l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1);
lean_inc(v___x_4577_);
v___x_4594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4594_, 0, v___x_4593_);
lean_ctor_set(v___x_4594_, 1, v___x_4577_);
v___x_4595_ = lean_unsigned_to_nat(32u);
v___x_4596_ = lean_mk_empty_array_with_capacity(v___x_4595_);
v___x_4597_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8);
v___x_4598_ = ((size_t)5ULL);
lean_inc(v___x_4577_);
v___x_4599_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4599_, 0, v___x_4597_);
lean_ctor_set(v___x_4599_, 1, v___x_4596_);
lean_ctor_set(v___x_4599_, 2, v___x_4577_);
lean_ctor_set(v___x_4599_, 3, v___x_4577_);
lean_ctor_set_usize(v___x_4599_, 4, v___x_4598_);
v___x_4600_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4600_, 0, v___x_4593_);
lean_ctor_set(v___x_4600_, 1, v___x_4593_);
lean_ctor_set(v___x_4600_, 2, v___x_4593_);
lean_ctor_set(v___x_4600_, 3, v___x_4599_);
v___x_4601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4594_);
lean_ctor_set(v___x_4601_, 1, v___x_4600_);
lean_inc_ref(v_expr_4591_);
v___x_4602_ = l_Lean_Meta_simp(v_expr_4591_, v_a_4590_, v_a_4578_, v___x_4592_, v___x_4601_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_);
lean_dec_ref(v___x_4601_);
if (lean_obj_tag(v___x_4602_) == 0)
{
lean_object* v_a_4603_; lean_object* v_fst_4604_; lean_object* v___x_4605_; 
v_a_4603_ = lean_ctor_get(v___x_4602_, 0);
lean_inc(v_a_4603_);
lean_dec_ref(v___x_4602_);
v_fst_4604_ = lean_ctor_get(v_a_4603_, 0);
lean_inc(v_fst_4604_);
lean_dec(v_a_4603_);
v___x_4605_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_4576_, v_fst_4604_, v___y_4579_, v___y_4580_, v___y_4581_, v___y_4582_);
return v___x_4605_;
}
else
{
lean_object* v_a_4606_; lean_object* v___x_4608_; uint8_t v_isShared_4609_; uint8_t v_isSharedCheck_4613_; 
lean_dec_ref(v_a_4576_);
v_a_4606_ = lean_ctor_get(v___x_4602_, 0);
v_isSharedCheck_4613_ = !lean_is_exclusive(v___x_4602_);
if (v_isSharedCheck_4613_ == 0)
{
v___x_4608_ = v___x_4602_;
v_isShared_4609_ = v_isSharedCheck_4613_;
goto v_resetjp_4607_;
}
else
{
lean_inc(v_a_4606_);
lean_dec(v___x_4602_);
v___x_4608_ = lean_box(0);
v_isShared_4609_ = v_isSharedCheck_4613_;
goto v_resetjp_4607_;
}
v_resetjp_4607_:
{
lean_object* v___x_4611_; 
if (v_isShared_4609_ == 0)
{
v___x_4611_ = v___x_4608_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v_a_4606_);
v___x_4611_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
return v___x_4611_;
}
}
}
}
else
{
lean_object* v_a_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4621_; 
lean_dec_ref(v_a_4578_);
lean_dec(v___x_4577_);
lean_dec_ref(v_a_4576_);
v_a_4614_ = lean_ctor_get(v___x_4589_, 0);
v_isSharedCheck_4621_ = !lean_is_exclusive(v___x_4589_);
if (v_isSharedCheck_4621_ == 0)
{
v___x_4616_ = v___x_4589_;
v_isShared_4617_ = v_isSharedCheck_4621_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_a_4614_);
lean_dec(v___x_4589_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4621_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v___x_4619_; 
if (v_isShared_4617_ == 0)
{
v___x_4619_ = v___x_4616_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v_a_4614_);
v___x_4619_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
return v___x_4619_;
}
}
}
}
else
{
lean_object* v_a_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4629_; 
lean_dec_ref(v_a_4578_);
lean_dec(v___x_4577_);
lean_dec_ref(v_a_4576_);
lean_dec_ref(v_a_4575_);
lean_dec_ref(v_config_4574_);
v_a_4622_ = lean_ctor_get(v___x_4584_, 0);
v_isSharedCheck_4629_ = !lean_is_exclusive(v___x_4584_);
if (v_isSharedCheck_4629_ == 0)
{
v___x_4624_ = v___x_4584_;
v_isShared_4625_ = v_isSharedCheck_4629_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_a_4622_);
lean_dec(v___x_4584_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4629_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v___x_4627_; 
if (v_isShared_4625_ == 0)
{
v___x_4627_ = v___x_4624_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v_a_4622_);
v___x_4627_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4626_;
}
v_reusejp_4626_:
{
return v___x_4627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__8___boxed(lean_object* v_squash_4630_, lean_object* v_config_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v___x_4634_, lean_object* v_a_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_){
_start:
{
lean_object* v_res_4641_; 
v_res_4641_ = l_Lean_Elab_Tactic_NormCast_derive___lam__8(v_squash_4630_, v_config_4631_, v_a_4632_, v_a_4633_, v___x_4634_, v_a_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_);
lean_dec(v___y_4639_);
lean_dec_ref(v___y_4638_);
lean_dec(v___y_4637_);
lean_dec_ref(v___y_4636_);
lean_dec_ref(v_squash_4630_);
return v_res_4641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__18(lean_object* v_e_4642_, lean_object* v_x_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_){
_start:
{
lean_object* v___x_4649_; lean_object* v___x_4650_; 
v___x_4649_ = l_Lean_MessageData_ofExpr(v_e_4642_);
v___x_4650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4650_, 0, v___x_4649_);
return v___x_4650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__18___boxed(lean_object* v_e_4651_, lean_object* v_x_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_){
_start:
{
lean_object* v_res_4658_; 
v_res_4658_ = l_Lean_Elab_Tactic_NormCast_derive___lam__18(v_e_4651_, v_x_4652_, v___y_4653_, v___y_4654_, v___y_4655_, v___y_4656_);
lean_dec(v___y_4656_);
lean_dec_ref(v___y_4655_);
lean_dec(v___y_4654_);
lean_dec_ref(v___y_4653_);
lean_dec_ref(v_x_4652_);
return v_res_4658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__10(lean_object* v___x_4659_, uint8_t v_hasTrace_4660_, lean_object* v_phase_4661_, lean_object* v_k_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_){
_start:
{
lean_object* v_options_4668_; uint8_t v_hasTrace_4669_; 
v_options_4668_ = lean_ctor_get(v___y_4665_, 2);
v_hasTrace_4669_ = lean_ctor_get_uint8(v_options_4668_, sizeof(void*)*1);
if (v_hasTrace_4669_ == 0)
{
lean_object* v___x_4670_; 
lean_dec_ref(v_phase_4661_);
lean_dec(v___x_4659_);
lean_inc(v___y_4666_);
lean_inc_ref(v___y_4665_);
lean_inc(v___y_4664_);
lean_inc_ref(v___y_4663_);
v___x_4670_ = lean_apply_5(v_k_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, lean_box(0));
return v___x_4670_;
}
else
{
lean_object* v___x_4671_; lean_object* v_a_4672_; lean_object* v___f_4673_; lean_object* v___x_4674_; lean_object* v___y_4676_; lean_object* v___y_4677_; lean_object* v_a_4678_; lean_object* v___y_4692_; lean_object* v___y_4693_; lean_object* v_a_4694_; uint8_t v___x_4745_; 
lean_inc(v___x_4659_);
v___x_4671_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___x_4659_, v___y_4665_);
v_a_4672_ = lean_ctor_get(v___x_4671_, 0);
lean_inc(v_a_4672_);
lean_dec_ref(v___x_4671_);
v___f_4673_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4673_, 0, v_phase_4661_);
v___x_4674_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_4745_ = lean_unbox(v_a_4672_);
if (v___x_4745_ == 0)
{
lean_object* v___x_4746_; uint8_t v___x_4747_; 
v___x_4746_ = l_Lean_trace_profiler;
v___x_4747_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_4668_, v___x_4746_);
if (v___x_4747_ == 0)
{
lean_object* v___x_4748_; 
lean_dec_ref(v___f_4673_);
lean_dec(v_a_4672_);
lean_dec(v___x_4659_);
lean_inc(v___y_4666_);
lean_inc_ref(v___y_4665_);
lean_inc(v___y_4664_);
lean_inc_ref(v___y_4663_);
v___x_4748_ = lean_apply_5(v_k_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, lean_box(0));
return v___x_4748_;
}
else
{
goto v___jp_4704_;
}
}
else
{
goto v___jp_4704_;
}
v___jp_4675_:
{
lean_object* v___x_4679_; double v___x_4680_; double v___x_4681_; double v___x_4682_; double v___x_4683_; double v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; uint8_t v___x_4689_; lean_object* v___x_4690_; 
v___x_4679_ = lean_io_mono_nanos_now();
v___x_4680_ = lean_float_of_nat(v___y_4676_);
v___x_4681_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1);
v___x_4682_ = lean_float_div(v___x_4680_, v___x_4681_);
v___x_4683_ = lean_float_of_nat(v___x_4679_);
v___x_4684_ = lean_float_div(v___x_4683_, v___x_4681_);
v___x_4685_ = lean_box_float(v___x_4682_);
v___x_4686_ = lean_box_float(v___x_4684_);
v___x_4687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4687_, 0, v___x_4685_);
lean_ctor_set(v___x_4687_, 1, v___x_4686_);
v___x_4688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4688_, 0, v_a_4678_);
lean_ctor_set(v___x_4688_, 1, v___x_4687_);
v___x_4689_ = lean_unbox(v_a_4672_);
lean_dec(v_a_4672_);
v___x_4690_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4659_, v_hasTrace_4660_, v___x_4674_, v_options_4668_, v___x_4689_, v___y_4677_, v___f_4673_, v___x_4688_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_);
return v___x_4690_;
}
v___jp_4691_:
{
lean_object* v___x_4695_; double v___x_4696_; double v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; uint8_t v___x_4702_; lean_object* v___x_4703_; 
v___x_4695_ = lean_io_get_num_heartbeats();
v___x_4696_ = lean_float_of_nat(v___y_4693_);
v___x_4697_ = lean_float_of_nat(v___x_4695_);
v___x_4698_ = lean_box_float(v___x_4696_);
v___x_4699_ = lean_box_float(v___x_4697_);
v___x_4700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4700_, 0, v___x_4698_);
lean_ctor_set(v___x_4700_, 1, v___x_4699_);
v___x_4701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4701_, 0, v_a_4694_);
lean_ctor_set(v___x_4701_, 1, v___x_4700_);
v___x_4702_ = lean_unbox(v_a_4672_);
lean_dec(v_a_4672_);
v___x_4703_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4659_, v_hasTrace_4660_, v___x_4674_, v_options_4668_, v___x_4702_, v___y_4692_, v___f_4673_, v___x_4701_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_);
return v___x_4703_;
}
v___jp_4704_:
{
lean_object* v___x_4705_; lean_object* v_a_4706_; lean_object* v___x_4707_; uint8_t v___x_4708_; 
v___x_4705_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg(v___y_4666_);
v_a_4706_ = lean_ctor_get(v___x_4705_, 0);
lean_inc(v_a_4706_);
lean_dec_ref(v___x_4705_);
v___x_4707_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4708_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_4668_, v___x_4707_);
if (v___x_4708_ == 0)
{
lean_object* v___x_4709_; lean_object* v___x_4710_; 
v___x_4709_ = lean_io_mono_nanos_now();
lean_inc(v___y_4666_);
lean_inc_ref(v___y_4665_);
lean_inc(v___y_4664_);
lean_inc_ref(v___y_4663_);
v___x_4710_ = lean_apply_5(v_k_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, lean_box(0));
if (lean_obj_tag(v___x_4710_) == 0)
{
lean_object* v_a_4711_; lean_object* v___x_4713_; uint8_t v_isShared_4714_; uint8_t v_isSharedCheck_4718_; 
v_a_4711_ = lean_ctor_get(v___x_4710_, 0);
v_isSharedCheck_4718_ = !lean_is_exclusive(v___x_4710_);
if (v_isSharedCheck_4718_ == 0)
{
v___x_4713_ = v___x_4710_;
v_isShared_4714_ = v_isSharedCheck_4718_;
goto v_resetjp_4712_;
}
else
{
lean_inc(v_a_4711_);
lean_dec(v___x_4710_);
v___x_4713_ = lean_box(0);
v_isShared_4714_ = v_isSharedCheck_4718_;
goto v_resetjp_4712_;
}
v_resetjp_4712_:
{
lean_object* v___x_4716_; 
if (v_isShared_4714_ == 0)
{
lean_ctor_set_tag(v___x_4713_, 1);
v___x_4716_ = v___x_4713_;
goto v_reusejp_4715_;
}
else
{
lean_object* v_reuseFailAlloc_4717_; 
v_reuseFailAlloc_4717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4717_, 0, v_a_4711_);
v___x_4716_ = v_reuseFailAlloc_4717_;
goto v_reusejp_4715_;
}
v_reusejp_4715_:
{
v___y_4676_ = v___x_4709_;
v___y_4677_ = v_a_4706_;
v_a_4678_ = v___x_4716_;
goto v___jp_4675_;
}
}
}
else
{
lean_object* v_a_4719_; lean_object* v___x_4721_; uint8_t v_isShared_4722_; uint8_t v_isSharedCheck_4726_; 
v_a_4719_ = lean_ctor_get(v___x_4710_, 0);
v_isSharedCheck_4726_ = !lean_is_exclusive(v___x_4710_);
if (v_isSharedCheck_4726_ == 0)
{
v___x_4721_ = v___x_4710_;
v_isShared_4722_ = v_isSharedCheck_4726_;
goto v_resetjp_4720_;
}
else
{
lean_inc(v_a_4719_);
lean_dec(v___x_4710_);
v___x_4721_ = lean_box(0);
v_isShared_4722_ = v_isSharedCheck_4726_;
goto v_resetjp_4720_;
}
v_resetjp_4720_:
{
lean_object* v___x_4724_; 
if (v_isShared_4722_ == 0)
{
lean_ctor_set_tag(v___x_4721_, 0);
v___x_4724_ = v___x_4721_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v_a_4719_);
v___x_4724_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
v___y_4676_ = v___x_4709_;
v___y_4677_ = v_a_4706_;
v_a_4678_ = v___x_4724_;
goto v___jp_4675_;
}
}
}
}
else
{
lean_object* v___x_4727_; lean_object* v___x_4728_; 
v___x_4727_ = lean_io_get_num_heartbeats();
lean_inc(v___y_4666_);
lean_inc_ref(v___y_4665_);
lean_inc(v___y_4664_);
lean_inc_ref(v___y_4663_);
v___x_4728_ = lean_apply_5(v_k_4662_, v___y_4663_, v___y_4664_, v___y_4665_, v___y_4666_, lean_box(0));
if (lean_obj_tag(v___x_4728_) == 0)
{
lean_object* v_a_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4736_; 
v_a_4729_ = lean_ctor_get(v___x_4728_, 0);
v_isSharedCheck_4736_ = !lean_is_exclusive(v___x_4728_);
if (v_isSharedCheck_4736_ == 0)
{
v___x_4731_ = v___x_4728_;
v_isShared_4732_ = v_isSharedCheck_4736_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_a_4729_);
lean_dec(v___x_4728_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4736_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v___x_4734_; 
if (v_isShared_4732_ == 0)
{
lean_ctor_set_tag(v___x_4731_, 1);
v___x_4734_ = v___x_4731_;
goto v_reusejp_4733_;
}
else
{
lean_object* v_reuseFailAlloc_4735_; 
v_reuseFailAlloc_4735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4735_, 0, v_a_4729_);
v___x_4734_ = v_reuseFailAlloc_4735_;
goto v_reusejp_4733_;
}
v_reusejp_4733_:
{
v___y_4692_ = v_a_4706_;
v___y_4693_ = v___x_4727_;
v_a_4694_ = v___x_4734_;
goto v___jp_4691_;
}
}
}
else
{
lean_object* v_a_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4744_; 
v_a_4737_ = lean_ctor_get(v___x_4728_, 0);
v_isSharedCheck_4744_ = !lean_is_exclusive(v___x_4728_);
if (v_isSharedCheck_4744_ == 0)
{
v___x_4739_ = v___x_4728_;
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_a_4737_);
lean_dec(v___x_4728_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4744_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v___x_4742_; 
if (v_isShared_4740_ == 0)
{
lean_ctor_set_tag(v___x_4739_, 0);
v___x_4742_ = v___x_4739_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v_a_4737_);
v___x_4742_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
v___y_4692_ = v_a_4706_;
v___y_4693_ = v___x_4727_;
v_a_4694_ = v___x_4742_;
goto v___jp_4691_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__10___boxed(lean_object* v___x_4749_, lean_object* v_hasTrace_4750_, lean_object* v_phase_4751_, lean_object* v_k_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_){
_start:
{
uint8_t v_hasTrace_boxed_4758_; lean_object* v_res_4759_; 
v_hasTrace_boxed_4758_ = lean_unbox(v_hasTrace_4750_);
v_res_4759_ = l_Lean_Elab_Tactic_NormCast_derive___lam__10(v___x_4749_, v_hasTrace_boxed_4758_, v_phase_4751_, v_k_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_);
lean_dec(v___y_4756_);
lean_dec_ref(v___y_4755_);
lean_dec(v___y_4754_);
lean_dec_ref(v___y_4753_);
return v_res_4759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__9(lean_object* v___x_4760_, uint8_t v_hasTrace_4761_, lean_object* v_e_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_){
_start:
{
lean_object* v_a_4772_; lean_object* v___y_4776_; lean_object* v___x_4786_; 
lean_inc_ref(v_e_4762_);
v___x_4786_ = l_Lean_Elab_Tactic_NormCast_numeralToCoe(v_e_4762_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_);
if (lean_obj_tag(v___x_4786_) == 0)
{
lean_dec_ref(v_e_4762_);
lean_dec(v___x_4760_);
v___y_4776_ = v___x_4786_;
goto v___jp_4775_;
}
else
{
lean_object* v_a_4787_; uint8_t v___y_4789_; uint8_t v___x_4791_; 
v_a_4787_ = lean_ctor_get(v___x_4786_, 0);
lean_inc(v_a_4787_);
v___x_4791_ = l_Lean_Exception_isInterrupt(v_a_4787_);
if (v___x_4791_ == 0)
{
uint8_t v___x_4792_; 
v___x_4792_ = l_Lean_Exception_isRuntime(v_a_4787_);
v___y_4789_ = v___x_4792_;
goto v___jp_4788_;
}
else
{
lean_dec(v_a_4787_);
v___y_4789_ = v___x_4791_;
goto v___jp_4788_;
}
v___jp_4788_:
{
if (v___y_4789_ == 0)
{
lean_object* v___x_4790_; 
lean_dec_ref(v___x_4786_);
v___x_4790_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4790_, 0, v_e_4762_);
lean_ctor_set(v___x_4790_, 1, v___x_4760_);
lean_ctor_set_uint8(v___x_4790_, sizeof(void*)*2, v_hasTrace_4761_);
v_a_4772_ = v___x_4790_;
goto v___jp_4771_;
}
else
{
lean_dec_ref(v_e_4762_);
lean_dec(v___x_4760_);
v___y_4776_ = v___x_4786_;
goto v___jp_4775_;
}
}
}
v___jp_4771_:
{
lean_object* v___x_4773_; lean_object* v___x_4774_; 
v___x_4773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4773_, 0, v_a_4772_);
v___x_4774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4774_, 0, v___x_4773_);
return v___x_4774_;
}
v___jp_4775_:
{
if (lean_obj_tag(v___y_4776_) == 0)
{
lean_object* v_a_4777_; 
v_a_4777_ = lean_ctor_get(v___y_4776_, 0);
lean_inc(v_a_4777_);
lean_dec_ref(v___y_4776_);
v_a_4772_ = v_a_4777_;
goto v___jp_4771_;
}
else
{
lean_object* v_a_4778_; lean_object* v___x_4780_; uint8_t v_isShared_4781_; uint8_t v_isSharedCheck_4785_; 
v_a_4778_ = lean_ctor_get(v___y_4776_, 0);
v_isSharedCheck_4785_ = !lean_is_exclusive(v___y_4776_);
if (v_isSharedCheck_4785_ == 0)
{
v___x_4780_ = v___y_4776_;
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
else
{
lean_inc(v_a_4778_);
lean_dec(v___y_4776_);
v___x_4780_ = lean_box(0);
v_isShared_4781_ = v_isSharedCheck_4785_;
goto v_resetjp_4779_;
}
v_resetjp_4779_:
{
lean_object* v___x_4783_; 
if (v_isShared_4781_ == 0)
{
v___x_4783_ = v___x_4780_;
goto v_reusejp_4782_;
}
else
{
lean_object* v_reuseFailAlloc_4784_; 
v_reuseFailAlloc_4784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4784_, 0, v_a_4778_);
v___x_4783_ = v_reuseFailAlloc_4784_;
goto v_reusejp_4782_;
}
v_reusejp_4782_:
{
return v___x_4783_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__9___boxed(lean_object* v___x_4793_, lean_object* v_hasTrace_4794_, lean_object* v_e_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_){
_start:
{
uint8_t v_hasTrace_boxed_4804_; lean_object* v_res_4805_; 
v_hasTrace_boxed_4804_ = lean_unbox(v_hasTrace_4794_);
v_res_4805_ = l_Lean_Elab_Tactic_NormCast_derive___lam__9(v___x_4793_, v_hasTrace_boxed_4804_, v_e_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_, v___y_4801_, v___y_4802_);
lean_dec(v___y_4802_);
lean_dec_ref(v___y_4801_);
lean_dec(v___y_4800_);
lean_dec_ref(v___y_4799_);
lean_dec(v___y_4798_);
lean_dec_ref(v___y_4797_);
lean_dec(v___y_4796_);
return v_res_4805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__14(lean_object* v_config_4806_, lean_object* v___x_4807_, lean_object* v_a_4808_, lean_object* v___x_4809_, lean_object* v___f_4810_, lean_object* v___f_4811_, lean_object* v___f_4812_, lean_object* v___f_4813_, lean_object* v___f_4814_, uint8_t v_hasTrace_4815_, lean_object* v_a_4816_, lean_object* v___x_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_){
_start:
{
lean_object* v___x_4823_; 
v___x_4823_ = l_Lean_Meta_Simp_mkContext___redArg(v_config_4806_, v___x_4807_, v_a_4808_, v___y_4818_, v___y_4820_, v___y_4821_);
if (lean_obj_tag(v___x_4823_) == 0)
{
lean_object* v_a_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; size_t v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; 
v_a_4824_ = lean_ctor_get(v___x_4823_, 0);
lean_inc(v_a_4824_);
lean_dec_ref(v___x_4823_);
v___x_4825_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1, &l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1);
lean_inc(v___x_4809_);
v___x_4826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4826_, 0, v___x_4825_);
lean_ctor_set(v___x_4826_, 1, v___x_4809_);
v___x_4827_ = lean_unsigned_to_nat(32u);
v___x_4828_ = lean_mk_empty_array_with_capacity(v___x_4827_);
v___x_4829_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8);
v___x_4830_ = ((size_t)5ULL);
lean_inc(v___x_4809_);
v___x_4831_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4831_, 0, v___x_4829_);
lean_ctor_set(v___x_4831_, 1, v___x_4828_);
lean_ctor_set(v___x_4831_, 2, v___x_4809_);
lean_ctor_set(v___x_4831_, 3, v___x_4809_);
lean_ctor_set_usize(v___x_4831_, 4, v___x_4830_);
v___x_4832_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4832_, 0, v___x_4825_);
lean_ctor_set(v___x_4832_, 1, v___x_4825_);
lean_ctor_set(v___x_4832_, 2, v___x_4825_);
lean_ctor_set(v___x_4832_, 3, v___x_4831_);
v___x_4833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4833_, 0, v___x_4826_);
lean_ctor_set(v___x_4833_, 1, v___x_4832_);
v___x_4834_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4834_, 0, v___f_4810_);
lean_ctor_set(v___x_4834_, 1, v___f_4811_);
lean_ctor_set(v___x_4834_, 2, v___f_4812_);
lean_ctor_set(v___x_4834_, 3, v___f_4813_);
lean_ctor_set(v___x_4834_, 4, v___f_4814_);
lean_ctor_set_uint8(v___x_4834_, sizeof(void*)*5, v_hasTrace_4815_);
v___x_4835_ = l_Lean_Meta_Simp_main(v_a_4816_, v_a_4824_, v___x_4833_, v___x_4834_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_);
if (lean_obj_tag(v___x_4835_) == 0)
{
lean_object* v_a_4836_; lean_object* v_fst_4837_; lean_object* v___x_4838_; 
v_a_4836_ = lean_ctor_get(v___x_4835_, 0);
lean_inc(v_a_4836_);
lean_dec_ref(v___x_4835_);
v_fst_4837_ = lean_ctor_get(v_a_4836_, 0);
lean_inc(v_fst_4837_);
lean_dec(v_a_4836_);
v___x_4838_ = l_Lean_Meta_Simp_Result_mkEqTrans(v___x_4817_, v_fst_4837_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_);
return v___x_4838_;
}
else
{
lean_object* v_a_4839_; lean_object* v___x_4841_; uint8_t v_isShared_4842_; uint8_t v_isSharedCheck_4846_; 
lean_dec_ref(v___x_4817_);
v_a_4839_ = lean_ctor_get(v___x_4835_, 0);
v_isSharedCheck_4846_ = !lean_is_exclusive(v___x_4835_);
if (v_isSharedCheck_4846_ == 0)
{
v___x_4841_ = v___x_4835_;
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
else
{
lean_inc(v_a_4839_);
lean_dec(v___x_4835_);
v___x_4841_ = lean_box(0);
v_isShared_4842_ = v_isSharedCheck_4846_;
goto v_resetjp_4840_;
}
v_resetjp_4840_:
{
lean_object* v___x_4844_; 
if (v_isShared_4842_ == 0)
{
v___x_4844_ = v___x_4841_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4845_; 
v_reuseFailAlloc_4845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4845_, 0, v_a_4839_);
v___x_4844_ = v_reuseFailAlloc_4845_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
return v___x_4844_;
}
}
}
}
else
{
lean_object* v_a_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4854_; 
lean_dec_ref(v___x_4817_);
lean_dec_ref(v_a_4816_);
lean_dec_ref(v___f_4814_);
lean_dec_ref(v___f_4813_);
lean_dec_ref(v___f_4812_);
lean_dec_ref(v___f_4811_);
lean_dec_ref(v___f_4810_);
lean_dec(v___x_4809_);
v_a_4847_ = lean_ctor_get(v___x_4823_, 0);
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4823_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4849_ = v___x_4823_;
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_a_4847_);
lean_dec(v___x_4823_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v___x_4852_; 
if (v_isShared_4850_ == 0)
{
v___x_4852_ = v___x_4849_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v_a_4847_);
v___x_4852_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
return v___x_4852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__14___boxed(lean_object** _args){
lean_object* v_config_4855_ = _args[0];
lean_object* v___x_4856_ = _args[1];
lean_object* v_a_4857_ = _args[2];
lean_object* v___x_4858_ = _args[3];
lean_object* v___f_4859_ = _args[4];
lean_object* v___f_4860_ = _args[5];
lean_object* v___f_4861_ = _args[6];
lean_object* v___f_4862_ = _args[7];
lean_object* v___f_4863_ = _args[8];
lean_object* v_hasTrace_4864_ = _args[9];
lean_object* v_a_4865_ = _args[10];
lean_object* v___x_4866_ = _args[11];
lean_object* v___y_4867_ = _args[12];
lean_object* v___y_4868_ = _args[13];
lean_object* v___y_4869_ = _args[14];
lean_object* v___y_4870_ = _args[15];
lean_object* v___y_4871_ = _args[16];
_start:
{
uint8_t v_hasTrace_boxed_4872_; lean_object* v_res_4873_; 
v_hasTrace_boxed_4872_ = lean_unbox(v_hasTrace_4864_);
v_res_4873_ = l_Lean_Elab_Tactic_NormCast_derive___lam__14(v_config_4855_, v___x_4856_, v_a_4857_, v___x_4858_, v___f_4859_, v___f_4860_, v___f_4861_, v___f_4862_, v___f_4863_, v_hasTrace_boxed_4872_, v_a_4865_, v___x_4866_, v___y_4867_, v___y_4868_, v___y_4869_, v___y_4870_);
lean_dec(v___y_4870_);
lean_dec_ref(v___y_4869_);
lean_dec(v___y_4868_);
lean_dec_ref(v___y_4867_);
return v_res_4873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__15(lean_object* v_up_4874_, lean_object* v_config_4875_, lean_object* v___x_4876_, lean_object* v_a_4877_, lean_object* v_a_4878_, lean_object* v___x_4879_, lean_object* v___f_4880_, lean_object* v___f_4881_, lean_object* v___f_4882_, lean_object* v___f_4883_, uint8_t v_hasTrace_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_, lean_object* v___y_4887_, lean_object* v___y_4888_){
_start:
{
lean_object* v___x_4890_; 
v___x_4890_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_up_4874_, v___y_4888_);
if (lean_obj_tag(v___x_4890_) == 0)
{
lean_object* v_a_4891_; lean_object* v___x_4892_; 
v_a_4891_ = lean_ctor_get(v___x_4890_, 0);
lean_inc(v_a_4891_);
lean_dec_ref(v___x_4890_);
v___x_4892_ = l_Lean_Meta_Simp_mkContext___redArg(v_config_4875_, v___x_4876_, v_a_4877_, v___y_4885_, v___y_4887_, v___y_4888_);
if (lean_obj_tag(v___x_4892_) == 0)
{
lean_object* v_a_4893_; lean_object* v_expr_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; size_t v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; 
v_a_4893_ = lean_ctor_get(v___x_4892_, 0);
lean_inc(v_a_4893_);
lean_dec_ref(v___x_4892_);
v_expr_4894_ = lean_ctor_get(v_a_4878_, 0);
v___x_4895_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_upwardAndElim___boxed), 10, 1);
lean_closure_set(v___x_4895_, 0, v_a_4891_);
v___x_4896_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1, &l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1);
lean_inc(v___x_4879_);
v___x_4897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4897_, 0, v___x_4896_);
lean_ctor_set(v___x_4897_, 1, v___x_4879_);
v___x_4898_ = lean_unsigned_to_nat(32u);
v___x_4899_ = lean_mk_empty_array_with_capacity(v___x_4898_);
v___x_4900_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8);
v___x_4901_ = ((size_t)5ULL);
lean_inc(v___x_4879_);
v___x_4902_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4902_, 0, v___x_4900_);
lean_ctor_set(v___x_4902_, 1, v___x_4899_);
lean_ctor_set(v___x_4902_, 2, v___x_4879_);
lean_ctor_set(v___x_4902_, 3, v___x_4879_);
lean_ctor_set_usize(v___x_4902_, 4, v___x_4901_);
v___x_4903_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4903_, 0, v___x_4896_);
lean_ctor_set(v___x_4903_, 1, v___x_4896_);
lean_ctor_set(v___x_4903_, 2, v___x_4896_);
lean_ctor_set(v___x_4903_, 3, v___x_4902_);
v___x_4904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4904_, 0, v___x_4897_);
lean_ctor_set(v___x_4904_, 1, v___x_4903_);
v___x_4905_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4905_, 0, v___f_4880_);
lean_ctor_set(v___x_4905_, 1, v___x_4895_);
lean_ctor_set(v___x_4905_, 2, v___f_4881_);
lean_ctor_set(v___x_4905_, 3, v___f_4882_);
lean_ctor_set(v___x_4905_, 4, v___f_4883_);
lean_ctor_set_uint8(v___x_4905_, sizeof(void*)*5, v_hasTrace_4884_);
lean_inc_ref(v_expr_4894_);
v___x_4906_ = l_Lean_Meta_Simp_main(v_expr_4894_, v_a_4893_, v___x_4904_, v___x_4905_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_);
if (lean_obj_tag(v___x_4906_) == 0)
{
lean_object* v_a_4907_; lean_object* v_fst_4908_; lean_object* v___x_4909_; 
v_a_4907_ = lean_ctor_get(v___x_4906_, 0);
lean_inc(v_a_4907_);
lean_dec_ref(v___x_4906_);
v_fst_4908_ = lean_ctor_get(v_a_4907_, 0);
lean_inc(v_fst_4908_);
lean_dec(v_a_4907_);
v___x_4909_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_4878_, v_fst_4908_, v___y_4885_, v___y_4886_, v___y_4887_, v___y_4888_);
return v___x_4909_;
}
else
{
lean_object* v_a_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4917_; 
lean_dec_ref(v_a_4878_);
v_a_4910_ = lean_ctor_get(v___x_4906_, 0);
v_isSharedCheck_4917_ = !lean_is_exclusive(v___x_4906_);
if (v_isSharedCheck_4917_ == 0)
{
v___x_4912_ = v___x_4906_;
v_isShared_4913_ = v_isSharedCheck_4917_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_a_4910_);
lean_dec(v___x_4906_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4917_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v___x_4915_; 
if (v_isShared_4913_ == 0)
{
v___x_4915_ = v___x_4912_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v_a_4910_);
v___x_4915_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
return v___x_4915_;
}
}
}
}
else
{
lean_object* v_a_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4925_; 
lean_dec(v_a_4891_);
lean_dec_ref(v___f_4883_);
lean_dec_ref(v___f_4882_);
lean_dec_ref(v___f_4881_);
lean_dec_ref(v___f_4880_);
lean_dec(v___x_4879_);
lean_dec_ref(v_a_4878_);
v_a_4918_ = lean_ctor_get(v___x_4892_, 0);
v_isSharedCheck_4925_ = !lean_is_exclusive(v___x_4892_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4920_ = v___x_4892_;
v_isShared_4921_ = v_isSharedCheck_4925_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_a_4918_);
lean_dec(v___x_4892_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4925_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v___x_4923_; 
if (v_isShared_4921_ == 0)
{
v___x_4923_ = v___x_4920_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v_a_4918_);
v___x_4923_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
return v___x_4923_;
}
}
}
}
else
{
lean_object* v_a_4926_; lean_object* v___x_4928_; uint8_t v_isShared_4929_; uint8_t v_isSharedCheck_4933_; 
lean_dec_ref(v___f_4883_);
lean_dec_ref(v___f_4882_);
lean_dec_ref(v___f_4881_);
lean_dec_ref(v___f_4880_);
lean_dec(v___x_4879_);
lean_dec_ref(v_a_4878_);
lean_dec_ref(v_a_4877_);
lean_dec_ref(v___x_4876_);
lean_dec_ref(v_config_4875_);
v_a_4926_ = lean_ctor_get(v___x_4890_, 0);
v_isSharedCheck_4933_ = !lean_is_exclusive(v___x_4890_);
if (v_isSharedCheck_4933_ == 0)
{
v___x_4928_ = v___x_4890_;
v_isShared_4929_ = v_isSharedCheck_4933_;
goto v_resetjp_4927_;
}
else
{
lean_inc(v_a_4926_);
lean_dec(v___x_4890_);
v___x_4928_ = lean_box(0);
v_isShared_4929_ = v_isSharedCheck_4933_;
goto v_resetjp_4927_;
}
v_resetjp_4927_:
{
lean_object* v___x_4931_; 
if (v_isShared_4929_ == 0)
{
v___x_4931_ = v___x_4928_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_4932_; 
v_reuseFailAlloc_4932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4932_, 0, v_a_4926_);
v___x_4931_ = v_reuseFailAlloc_4932_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
return v___x_4931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__15___boxed(lean_object* v_up_4934_, lean_object* v_config_4935_, lean_object* v___x_4936_, lean_object* v_a_4937_, lean_object* v_a_4938_, lean_object* v___x_4939_, lean_object* v___f_4940_, lean_object* v___f_4941_, lean_object* v___f_4942_, lean_object* v___f_4943_, lean_object* v_hasTrace_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_){
_start:
{
uint8_t v_hasTrace_boxed_4950_; lean_object* v_res_4951_; 
v_hasTrace_boxed_4950_ = lean_unbox(v_hasTrace_4944_);
v_res_4951_ = l_Lean_Elab_Tactic_NormCast_derive___lam__15(v_up_4934_, v_config_4935_, v___x_4936_, v_a_4937_, v_a_4938_, v___x_4939_, v___f_4940_, v___f_4941_, v___f_4942_, v___f_4943_, v_hasTrace_boxed_4950_, v___y_4945_, v___y_4946_, v___y_4947_, v___y_4948_);
lean_dec(v___y_4948_);
lean_dec_ref(v___y_4947_);
lean_dec(v___y_4946_);
lean_dec_ref(v___y_4945_);
lean_dec_ref(v_up_4934_);
return v_res_4951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__16(lean_object* v___x_4952_, uint8_t v___x_4953_, lean_object* v___x_4954_, lean_object* v___x_4955_, lean_object* v_phase_4956_, lean_object* v_k_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_){
_start:
{
lean_object* v_options_4963_; uint8_t v_hasTrace_4964_; 
v_options_4963_ = lean_ctor_get(v___y_4960_, 2);
v_hasTrace_4964_ = lean_ctor_get_uint8(v_options_4963_, sizeof(void*)*1);
if (v_hasTrace_4964_ == 0)
{
lean_object* v___x_4965_; 
lean_dec_ref(v_phase_4956_);
lean_dec_ref(v___x_4954_);
lean_dec(v___x_4952_);
lean_inc(v___y_4961_);
lean_inc_ref(v___y_4960_);
lean_inc(v___y_4959_);
lean_inc_ref(v___y_4958_);
v___x_4965_ = lean_apply_5(v_k_4957_, v___y_4958_, v___y_4959_, v___y_4960_, v___y_4961_, lean_box(0));
return v___x_4965_;
}
else
{
lean_object* v___x_4966_; lean_object* v_a_4967_; lean_object* v___f_4968_; lean_object* v___y_4970_; lean_object* v___y_4971_; lean_object* v_a_4972_; lean_object* v___y_4986_; lean_object* v___y_4987_; lean_object* v_a_4988_; uint8_t v___x_5038_; 
lean_inc(v___x_4952_);
v___x_4966_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___x_4952_, v___y_4960_);
v_a_4967_ = lean_ctor_get(v___x_4966_, 0);
lean_inc(v_a_4967_);
lean_dec_ref(v___x_4966_);
v___f_4968_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4968_, 0, v_phase_4956_);
v___x_5038_ = lean_unbox(v_a_4967_);
if (v___x_5038_ == 0)
{
lean_object* v___x_5039_; uint8_t v___x_5040_; 
v___x_5039_ = l_Lean_trace_profiler;
v___x_5040_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_4963_, v___x_5039_);
if (v___x_5040_ == 0)
{
lean_object* v___x_5041_; 
lean_dec_ref(v___f_4968_);
lean_dec(v_a_4967_);
lean_dec_ref(v___x_4954_);
lean_dec(v___x_4952_);
lean_inc(v___y_4961_);
lean_inc_ref(v___y_4960_);
lean_inc(v___y_4959_);
lean_inc_ref(v___y_4958_);
v___x_5041_ = lean_apply_5(v_k_4957_, v___y_4958_, v___y_4959_, v___y_4960_, v___y_4961_, lean_box(0));
return v___x_5041_;
}
else
{
goto v___jp_4998_;
}
}
else
{
goto v___jp_4998_;
}
v___jp_4969_:
{
lean_object* v___x_4973_; double v___x_4974_; double v___x_4975_; double v___x_4976_; double v___x_4977_; double v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; uint8_t v___x_4983_; lean_object* v___x_4984_; 
v___x_4973_ = lean_io_mono_nanos_now();
v___x_4974_ = lean_float_of_nat(v___y_4971_);
v___x_4975_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1);
v___x_4976_ = lean_float_div(v___x_4974_, v___x_4975_);
v___x_4977_ = lean_float_of_nat(v___x_4973_);
v___x_4978_ = lean_float_div(v___x_4977_, v___x_4975_);
v___x_4979_ = lean_box_float(v___x_4976_);
v___x_4980_ = lean_box_float(v___x_4978_);
v___x_4981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4981_, 0, v___x_4979_);
lean_ctor_set(v___x_4981_, 1, v___x_4980_);
v___x_4982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4982_, 0, v_a_4972_);
lean_ctor_set(v___x_4982_, 1, v___x_4981_);
v___x_4983_ = lean_unbox(v_a_4967_);
lean_dec(v_a_4967_);
v___x_4984_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4952_, v___x_4953_, v___x_4954_, v_options_4963_, v___x_4983_, v___y_4970_, v___f_4968_, v___x_4982_, v___y_4958_, v___y_4959_, v___y_4960_, v___y_4961_);
return v___x_4984_;
}
v___jp_4985_:
{
lean_object* v___x_4989_; double v___x_4990_; double v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; uint8_t v___x_4996_; lean_object* v___x_4997_; 
v___x_4989_ = lean_io_get_num_heartbeats();
v___x_4990_ = lean_float_of_nat(v___y_4987_);
v___x_4991_ = lean_float_of_nat(v___x_4989_);
v___x_4992_ = lean_box_float(v___x_4990_);
v___x_4993_ = lean_box_float(v___x_4991_);
v___x_4994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4994_, 0, v___x_4992_);
lean_ctor_set(v___x_4994_, 1, v___x_4993_);
v___x_4995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4995_, 0, v_a_4988_);
lean_ctor_set(v___x_4995_, 1, v___x_4994_);
v___x_4996_ = lean_unbox(v_a_4967_);
lean_dec(v_a_4967_);
v___x_4997_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4952_, v___x_4953_, v___x_4954_, v_options_4963_, v___x_4996_, v___y_4986_, v___f_4968_, v___x_4995_, v___y_4958_, v___y_4959_, v___y_4960_, v___y_4961_);
return v___x_4997_;
}
v___jp_4998_:
{
lean_object* v___x_4999_; lean_object* v_a_5000_; uint8_t v___x_5001_; 
v___x_4999_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg(v___y_4961_);
v_a_5000_ = lean_ctor_get(v___x_4999_, 0);
lean_inc(v_a_5000_);
lean_dec_ref(v___x_4999_);
v___x_5001_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_4963_, v___x_4955_);
if (v___x_5001_ == 0)
{
lean_object* v___x_5002_; lean_object* v___x_5003_; 
v___x_5002_ = lean_io_mono_nanos_now();
lean_inc(v___y_4961_);
lean_inc_ref(v___y_4960_);
lean_inc(v___y_4959_);
lean_inc_ref(v___y_4958_);
v___x_5003_ = lean_apply_5(v_k_4957_, v___y_4958_, v___y_4959_, v___y_4960_, v___y_4961_, lean_box(0));
if (lean_obj_tag(v___x_5003_) == 0)
{
lean_object* v_a_5004_; lean_object* v___x_5006_; uint8_t v_isShared_5007_; uint8_t v_isSharedCheck_5011_; 
v_a_5004_ = lean_ctor_get(v___x_5003_, 0);
v_isSharedCheck_5011_ = !lean_is_exclusive(v___x_5003_);
if (v_isSharedCheck_5011_ == 0)
{
v___x_5006_ = v___x_5003_;
v_isShared_5007_ = v_isSharedCheck_5011_;
goto v_resetjp_5005_;
}
else
{
lean_inc(v_a_5004_);
lean_dec(v___x_5003_);
v___x_5006_ = lean_box(0);
v_isShared_5007_ = v_isSharedCheck_5011_;
goto v_resetjp_5005_;
}
v_resetjp_5005_:
{
lean_object* v___x_5009_; 
if (v_isShared_5007_ == 0)
{
lean_ctor_set_tag(v___x_5006_, 1);
v___x_5009_ = v___x_5006_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5010_; 
v_reuseFailAlloc_5010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5010_, 0, v_a_5004_);
v___x_5009_ = v_reuseFailAlloc_5010_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
v___y_4970_ = v_a_5000_;
v___y_4971_ = v___x_5002_;
v_a_4972_ = v___x_5009_;
goto v___jp_4969_;
}
}
}
else
{
lean_object* v_a_5012_; lean_object* v___x_5014_; uint8_t v_isShared_5015_; uint8_t v_isSharedCheck_5019_; 
v_a_5012_ = lean_ctor_get(v___x_5003_, 0);
v_isSharedCheck_5019_ = !lean_is_exclusive(v___x_5003_);
if (v_isSharedCheck_5019_ == 0)
{
v___x_5014_ = v___x_5003_;
v_isShared_5015_ = v_isSharedCheck_5019_;
goto v_resetjp_5013_;
}
else
{
lean_inc(v_a_5012_);
lean_dec(v___x_5003_);
v___x_5014_ = lean_box(0);
v_isShared_5015_ = v_isSharedCheck_5019_;
goto v_resetjp_5013_;
}
v_resetjp_5013_:
{
lean_object* v___x_5017_; 
if (v_isShared_5015_ == 0)
{
lean_ctor_set_tag(v___x_5014_, 0);
v___x_5017_ = v___x_5014_;
goto v_reusejp_5016_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v_a_5012_);
v___x_5017_ = v_reuseFailAlloc_5018_;
goto v_reusejp_5016_;
}
v_reusejp_5016_:
{
v___y_4970_ = v_a_5000_;
v___y_4971_ = v___x_5002_;
v_a_4972_ = v___x_5017_;
goto v___jp_4969_;
}
}
}
}
else
{
lean_object* v___x_5020_; lean_object* v___x_5021_; 
v___x_5020_ = lean_io_get_num_heartbeats();
lean_inc(v___y_4961_);
lean_inc_ref(v___y_4960_);
lean_inc(v___y_4959_);
lean_inc_ref(v___y_4958_);
v___x_5021_ = lean_apply_5(v_k_4957_, v___y_4958_, v___y_4959_, v___y_4960_, v___y_4961_, lean_box(0));
if (lean_obj_tag(v___x_5021_) == 0)
{
lean_object* v_a_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5029_; 
v_a_5022_ = lean_ctor_get(v___x_5021_, 0);
v_isSharedCheck_5029_ = !lean_is_exclusive(v___x_5021_);
if (v_isSharedCheck_5029_ == 0)
{
v___x_5024_ = v___x_5021_;
v_isShared_5025_ = v_isSharedCheck_5029_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_a_5022_);
lean_dec(v___x_5021_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5029_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v___x_5027_; 
if (v_isShared_5025_ == 0)
{
lean_ctor_set_tag(v___x_5024_, 1);
v___x_5027_ = v___x_5024_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v_a_5022_);
v___x_5027_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
v___y_4986_ = v_a_5000_;
v___y_4987_ = v___x_5020_;
v_a_4988_ = v___x_5027_;
goto v___jp_4985_;
}
}
}
else
{
lean_object* v_a_5030_; lean_object* v___x_5032_; uint8_t v_isShared_5033_; uint8_t v_isSharedCheck_5037_; 
v_a_5030_ = lean_ctor_get(v___x_5021_, 0);
v_isSharedCheck_5037_ = !lean_is_exclusive(v___x_5021_);
if (v_isSharedCheck_5037_ == 0)
{
v___x_5032_ = v___x_5021_;
v_isShared_5033_ = v_isSharedCheck_5037_;
goto v_resetjp_5031_;
}
else
{
lean_inc(v_a_5030_);
lean_dec(v___x_5021_);
v___x_5032_ = lean_box(0);
v_isShared_5033_ = v_isSharedCheck_5037_;
goto v_resetjp_5031_;
}
v_resetjp_5031_:
{
lean_object* v___x_5035_; 
if (v_isShared_5033_ == 0)
{
lean_ctor_set_tag(v___x_5032_, 0);
v___x_5035_ = v___x_5032_;
goto v_reusejp_5034_;
}
else
{
lean_object* v_reuseFailAlloc_5036_; 
v_reuseFailAlloc_5036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5036_, 0, v_a_5030_);
v___x_5035_ = v_reuseFailAlloc_5036_;
goto v_reusejp_5034_;
}
v_reusejp_5034_:
{
v___y_4986_ = v_a_5000_;
v___y_4987_ = v___x_5020_;
v_a_4988_ = v___x_5035_;
goto v___jp_4985_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__16___boxed(lean_object* v___x_5042_, lean_object* v___x_5043_, lean_object* v___x_5044_, lean_object* v___x_5045_, lean_object* v_phase_5046_, lean_object* v_k_5047_, lean_object* v___y_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_){
_start:
{
uint8_t v___x_31957__boxed_5053_; lean_object* v_res_5054_; 
v___x_31957__boxed_5053_ = lean_unbox(v___x_5043_);
v_res_5054_ = l_Lean_Elab_Tactic_NormCast_derive___lam__16(v___x_5042_, v___x_31957__boxed_5053_, v___x_5044_, v___x_5045_, v_phase_5046_, v_k_5047_, v___y_5048_, v___y_5049_, v___y_5050_, v___y_5051_);
lean_dec(v___y_5051_);
lean_dec_ref(v___y_5050_);
lean_dec(v___y_5049_);
lean_dec_ref(v___y_5048_);
lean_dec_ref(v___x_5045_);
return v_res_5054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__27(lean_object* v___x_5055_, uint8_t v_hasTrace_5056_, lean_object* v_phase_5057_, lean_object* v_k_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_){
_start:
{
lean_object* v_options_5064_; uint8_t v_hasTrace_5065_; 
v_options_5064_ = lean_ctor_get(v___y_5061_, 2);
v_hasTrace_5065_ = lean_ctor_get_uint8(v_options_5064_, sizeof(void*)*1);
if (v_hasTrace_5065_ == 0)
{
lean_object* v___x_5066_; 
lean_dec_ref(v_phase_5057_);
lean_dec(v___x_5055_);
lean_inc(v___y_5062_);
lean_inc_ref(v___y_5061_);
lean_inc(v___y_5060_);
lean_inc_ref(v___y_5059_);
v___x_5066_ = lean_apply_5(v_k_5058_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_, lean_box(0));
return v___x_5066_;
}
else
{
lean_object* v___x_5067_; lean_object* v_a_5068_; lean_object* v___f_5069_; lean_object* v___x_5070_; lean_object* v___y_5072_; lean_object* v___y_5073_; lean_object* v_a_5074_; lean_object* v___y_5088_; lean_object* v___y_5089_; lean_object* v_a_5090_; uint8_t v___x_5141_; 
lean_inc(v___x_5055_);
v___x_5067_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___x_5055_, v___y_5061_);
v_a_5068_ = lean_ctor_get(v___x_5067_, 0);
lean_inc(v_a_5068_);
lean_dec_ref(v___x_5067_);
v___f_5069_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__4___boxed), 7, 1);
lean_closure_set(v___f_5069_, 0, v_phase_5057_);
v___x_5070_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_5141_ = lean_unbox(v_a_5068_);
if (v___x_5141_ == 0)
{
lean_object* v___x_5142_; uint8_t v___x_5143_; 
v___x_5142_ = l_Lean_trace_profiler;
v___x_5143_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_5064_, v___x_5142_);
if (v___x_5143_ == 0)
{
lean_object* v___x_5144_; 
lean_dec_ref(v___f_5069_);
lean_dec(v_a_5068_);
lean_dec(v___x_5055_);
lean_inc(v___y_5062_);
lean_inc_ref(v___y_5061_);
lean_inc(v___y_5060_);
lean_inc_ref(v___y_5059_);
v___x_5144_ = lean_apply_5(v_k_5058_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_, lean_box(0));
return v___x_5144_;
}
else
{
goto v___jp_5100_;
}
}
else
{
goto v___jp_5100_;
}
v___jp_5071_:
{
lean_object* v___x_5075_; double v___x_5076_; double v___x_5077_; double v___x_5078_; double v___x_5079_; double v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___x_5084_; uint8_t v___x_5085_; lean_object* v___x_5086_; 
v___x_5075_ = lean_io_mono_nanos_now();
v___x_5076_ = lean_float_of_nat(v___y_5073_);
v___x_5077_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1);
v___x_5078_ = lean_float_div(v___x_5076_, v___x_5077_);
v___x_5079_ = lean_float_of_nat(v___x_5075_);
v___x_5080_ = lean_float_div(v___x_5079_, v___x_5077_);
v___x_5081_ = lean_box_float(v___x_5078_);
v___x_5082_ = lean_box_float(v___x_5080_);
v___x_5083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5083_, 0, v___x_5081_);
lean_ctor_set(v___x_5083_, 1, v___x_5082_);
v___x_5084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5084_, 0, v_a_5074_);
lean_ctor_set(v___x_5084_, 1, v___x_5083_);
v___x_5085_ = lean_unbox(v_a_5068_);
lean_dec(v_a_5068_);
v___x_5086_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_5055_, v_hasTrace_5056_, v___x_5070_, v_options_5064_, v___x_5085_, v___y_5072_, v___f_5069_, v___x_5084_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_);
return v___x_5086_;
}
v___jp_5087_:
{
lean_object* v___x_5091_; double v___x_5092_; double v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; uint8_t v___x_5098_; lean_object* v___x_5099_; 
v___x_5091_ = lean_io_get_num_heartbeats();
v___x_5092_ = lean_float_of_nat(v___y_5088_);
v___x_5093_ = lean_float_of_nat(v___x_5091_);
v___x_5094_ = lean_box_float(v___x_5092_);
v___x_5095_ = lean_box_float(v___x_5093_);
v___x_5096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5096_, 0, v___x_5094_);
lean_ctor_set(v___x_5096_, 1, v___x_5095_);
v___x_5097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5097_, 0, v_a_5090_);
lean_ctor_set(v___x_5097_, 1, v___x_5096_);
v___x_5098_ = lean_unbox(v_a_5068_);
lean_dec(v_a_5068_);
v___x_5099_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_5055_, v_hasTrace_5056_, v___x_5070_, v_options_5064_, v___x_5098_, v___y_5089_, v___f_5069_, v___x_5097_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_);
return v___x_5099_;
}
v___jp_5100_:
{
lean_object* v___x_5101_; lean_object* v_a_5102_; lean_object* v___x_5103_; uint8_t v___x_5104_; 
v___x_5101_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg(v___y_5062_);
v_a_5102_ = lean_ctor_get(v___x_5101_, 0);
lean_inc(v_a_5102_);
lean_dec_ref(v___x_5101_);
v___x_5103_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5104_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_5064_, v___x_5103_);
if (v___x_5104_ == 0)
{
lean_object* v___x_5105_; lean_object* v___x_5106_; 
v___x_5105_ = lean_io_mono_nanos_now();
lean_inc(v___y_5062_);
lean_inc_ref(v___y_5061_);
lean_inc(v___y_5060_);
lean_inc_ref(v___y_5059_);
v___x_5106_ = lean_apply_5(v_k_5058_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_, lean_box(0));
if (lean_obj_tag(v___x_5106_) == 0)
{
lean_object* v_a_5107_; lean_object* v___x_5109_; uint8_t v_isShared_5110_; uint8_t v_isSharedCheck_5114_; 
v_a_5107_ = lean_ctor_get(v___x_5106_, 0);
v_isSharedCheck_5114_ = !lean_is_exclusive(v___x_5106_);
if (v_isSharedCheck_5114_ == 0)
{
v___x_5109_ = v___x_5106_;
v_isShared_5110_ = v_isSharedCheck_5114_;
goto v_resetjp_5108_;
}
else
{
lean_inc(v_a_5107_);
lean_dec(v___x_5106_);
v___x_5109_ = lean_box(0);
v_isShared_5110_ = v_isSharedCheck_5114_;
goto v_resetjp_5108_;
}
v_resetjp_5108_:
{
lean_object* v___x_5112_; 
if (v_isShared_5110_ == 0)
{
lean_ctor_set_tag(v___x_5109_, 1);
v___x_5112_ = v___x_5109_;
goto v_reusejp_5111_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v_a_5107_);
v___x_5112_ = v_reuseFailAlloc_5113_;
goto v_reusejp_5111_;
}
v_reusejp_5111_:
{
v___y_5072_ = v_a_5102_;
v___y_5073_ = v___x_5105_;
v_a_5074_ = v___x_5112_;
goto v___jp_5071_;
}
}
}
else
{
lean_object* v_a_5115_; lean_object* v___x_5117_; uint8_t v_isShared_5118_; uint8_t v_isSharedCheck_5122_; 
v_a_5115_ = lean_ctor_get(v___x_5106_, 0);
v_isSharedCheck_5122_ = !lean_is_exclusive(v___x_5106_);
if (v_isSharedCheck_5122_ == 0)
{
v___x_5117_ = v___x_5106_;
v_isShared_5118_ = v_isSharedCheck_5122_;
goto v_resetjp_5116_;
}
else
{
lean_inc(v_a_5115_);
lean_dec(v___x_5106_);
v___x_5117_ = lean_box(0);
v_isShared_5118_ = v_isSharedCheck_5122_;
goto v_resetjp_5116_;
}
v_resetjp_5116_:
{
lean_object* v___x_5120_; 
if (v_isShared_5118_ == 0)
{
lean_ctor_set_tag(v___x_5117_, 0);
v___x_5120_ = v___x_5117_;
goto v_reusejp_5119_;
}
else
{
lean_object* v_reuseFailAlloc_5121_; 
v_reuseFailAlloc_5121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5121_, 0, v_a_5115_);
v___x_5120_ = v_reuseFailAlloc_5121_;
goto v_reusejp_5119_;
}
v_reusejp_5119_:
{
v___y_5072_ = v_a_5102_;
v___y_5073_ = v___x_5105_;
v_a_5074_ = v___x_5120_;
goto v___jp_5071_;
}
}
}
}
else
{
lean_object* v___x_5123_; lean_object* v___x_5124_; 
v___x_5123_ = lean_io_get_num_heartbeats();
lean_inc(v___y_5062_);
lean_inc_ref(v___y_5061_);
lean_inc(v___y_5060_);
lean_inc_ref(v___y_5059_);
v___x_5124_ = lean_apply_5(v_k_5058_, v___y_5059_, v___y_5060_, v___y_5061_, v___y_5062_, lean_box(0));
if (lean_obj_tag(v___x_5124_) == 0)
{
lean_object* v_a_5125_; lean_object* v___x_5127_; uint8_t v_isShared_5128_; uint8_t v_isSharedCheck_5132_; 
v_a_5125_ = lean_ctor_get(v___x_5124_, 0);
v_isSharedCheck_5132_ = !lean_is_exclusive(v___x_5124_);
if (v_isSharedCheck_5132_ == 0)
{
v___x_5127_ = v___x_5124_;
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
else
{
lean_inc(v_a_5125_);
lean_dec(v___x_5124_);
v___x_5127_ = lean_box(0);
v_isShared_5128_ = v_isSharedCheck_5132_;
goto v_resetjp_5126_;
}
v_resetjp_5126_:
{
lean_object* v___x_5130_; 
if (v_isShared_5128_ == 0)
{
lean_ctor_set_tag(v___x_5127_, 1);
v___x_5130_ = v___x_5127_;
goto v_reusejp_5129_;
}
else
{
lean_object* v_reuseFailAlloc_5131_; 
v_reuseFailAlloc_5131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5131_, 0, v_a_5125_);
v___x_5130_ = v_reuseFailAlloc_5131_;
goto v_reusejp_5129_;
}
v_reusejp_5129_:
{
v___y_5088_ = v___x_5123_;
v___y_5089_ = v_a_5102_;
v_a_5090_ = v___x_5130_;
goto v___jp_5087_;
}
}
}
else
{
lean_object* v_a_5133_; lean_object* v___x_5135_; uint8_t v_isShared_5136_; uint8_t v_isSharedCheck_5140_; 
v_a_5133_ = lean_ctor_get(v___x_5124_, 0);
v_isSharedCheck_5140_ = !lean_is_exclusive(v___x_5124_);
if (v_isSharedCheck_5140_ == 0)
{
v___x_5135_ = v___x_5124_;
v_isShared_5136_ = v_isSharedCheck_5140_;
goto v_resetjp_5134_;
}
else
{
lean_inc(v_a_5133_);
lean_dec(v___x_5124_);
v___x_5135_ = lean_box(0);
v_isShared_5136_ = v_isSharedCheck_5140_;
goto v_resetjp_5134_;
}
v_resetjp_5134_:
{
lean_object* v___x_5138_; 
if (v_isShared_5136_ == 0)
{
lean_ctor_set_tag(v___x_5135_, 0);
v___x_5138_ = v___x_5135_;
goto v_reusejp_5137_;
}
else
{
lean_object* v_reuseFailAlloc_5139_; 
v_reuseFailAlloc_5139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5139_, 0, v_a_5133_);
v___x_5138_ = v_reuseFailAlloc_5139_;
goto v_reusejp_5137_;
}
v_reusejp_5137_:
{
v___y_5088_ = v___x_5123_;
v___y_5089_ = v_a_5102_;
v_a_5090_ = v___x_5138_;
goto v___jp_5087_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__27___boxed(lean_object* v___x_5145_, lean_object* v_hasTrace_5146_, lean_object* v_phase_5147_, lean_object* v_k_5148_, lean_object* v___y_5149_, lean_object* v___y_5150_, lean_object* v___y_5151_, lean_object* v___y_5152_, lean_object* v___y_5153_){
_start:
{
uint8_t v_hasTrace_boxed_5154_; lean_object* v_res_5155_; 
v_hasTrace_boxed_5154_ = lean_unbox(v_hasTrace_5146_);
v_res_5155_ = l_Lean_Elab_Tactic_NormCast_derive___lam__27(v___x_5145_, v_hasTrace_boxed_5154_, v_phase_5147_, v_k_5148_, v___y_5149_, v___y_5150_, v___y_5151_, v___y_5152_);
lean_dec(v___y_5152_);
lean_dec_ref(v___y_5151_);
lean_dec(v___y_5150_);
lean_dec_ref(v___y_5149_);
return v_res_5155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive(lean_object* v_e_5174_, lean_object* v_config_5175_, lean_object* v_a_5176_, lean_object* v_a_5177_, lean_object* v_a_5178_, lean_object* v_a_5179_){
_start:
{
lean_object* v_options_5181_; uint8_t v_hasTrace_5182_; lean_object* v___x_5183_; 
v_options_5181_ = lean_ctor_get(v_a_5178_, 2);
v_hasTrace_5182_ = lean_ctor_get_uint8(v_options_5181_, sizeof(void*)*1);
v___x_5183_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__2_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_));
if (v_hasTrace_5182_ == 0)
{
lean_object* v___x_5184_; lean_object* v_a_5185_; lean_object* v___x_5186_; 
v___x_5184_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_e_5174_, v_a_5177_);
v_a_5185_ = lean_ctor_get(v___x_5184_, 0);
lean_inc(v_a_5185_);
lean_dec_ref(v___x_5184_);
v___x_5186_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_5179_);
if (lean_obj_tag(v___x_5186_) == 0)
{
lean_object* v_a_5187_; lean_object* v___f_5188_; lean_object* v___f_5189_; lean_object* v___x_5190_; lean_object* v___f_5191_; lean_object* v___f_5192_; uint8_t v___x_5193_; lean_object* v___f_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___f_5200_; lean_object* v___x_5201_; 
v_a_5187_ = lean_ctor_get(v___x_5186_, 0);
lean_inc(v_a_5187_);
lean_dec_ref(v___x_5186_);
v___f_5188_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__0));
v___f_5189_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__1));
v___x_5190_ = lean_box(0);
v___f_5191_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__2));
v___f_5192_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__3));
v___x_5193_ = 1;
v___f_5194_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__4));
lean_inc(v_a_5185_);
v___x_5195_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5195_, 0, v_a_5185_);
lean_ctor_set(v___x_5195_, 1, v___x_5190_);
lean_ctor_set_uint8(v___x_5195_, sizeof(void*)*2, v___x_5193_);
v___x_5196_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__5));
v___x_5197_ = lean_unsigned_to_nat(0u);
v___x_5198_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__6));
v___x_5199_ = lean_box(v___x_5193_);
lean_inc(v_a_5187_);
lean_inc_ref(v_config_5175_);
v___f_5200_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__7___boxed), 17, 12);
lean_closure_set(v___f_5200_, 0, v_config_5175_);
lean_closure_set(v___f_5200_, 1, v___x_5198_);
lean_closure_set(v___f_5200_, 2, v_a_5187_);
lean_closure_set(v___f_5200_, 3, v___x_5197_);
lean_closure_set(v___f_5200_, 4, v___f_5188_);
lean_closure_set(v___f_5200_, 5, v___f_5194_);
lean_closure_set(v___f_5200_, 6, v___f_5191_);
lean_closure_set(v___f_5200_, 7, v___f_5189_);
lean_closure_set(v___f_5200_, 8, v___f_5192_);
lean_closure_set(v___f_5200_, 9, v___x_5199_);
lean_closure_set(v___f_5200_, 10, v_a_5185_);
lean_closure_set(v___f_5200_, 11, v___x_5195_);
v___x_5201_ = l_Lean_Elab_Tactic_NormCast_derive___lam__5(v___x_5183_, v___x_5193_, v___x_5196_, v___f_5200_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_);
if (lean_obj_tag(v___x_5201_) == 0)
{
lean_object* v_a_5202_; lean_object* v___x_5203_; lean_object* v_up_5204_; lean_object* v_squash_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___f_5208_; lean_object* v___x_5209_; 
v_a_5202_ = lean_ctor_get(v___x_5201_, 0);
lean_inc(v_a_5202_);
lean_dec_ref(v___x_5201_);
v___x_5203_ = l_Lean_Meta_NormCast_normCastExt;
v_up_5204_ = lean_ctor_get(v___x_5203_, 0);
lean_inc_ref(v_up_5204_);
v_squash_5205_ = lean_ctor_get(v___x_5203_, 2);
lean_inc_ref(v_squash_5205_);
v___x_5206_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__7));
v___x_5207_ = lean_box(v___x_5193_);
lean_inc(v_a_5187_);
lean_inc_ref(v_config_5175_);
v___f_5208_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__12___boxed), 16, 11);
lean_closure_set(v___f_5208_, 0, v_up_5204_);
lean_closure_set(v___f_5208_, 1, v_config_5175_);
lean_closure_set(v___f_5208_, 2, v___x_5198_);
lean_closure_set(v___f_5208_, 3, v_a_5187_);
lean_closure_set(v___f_5208_, 4, v_a_5202_);
lean_closure_set(v___f_5208_, 5, v___x_5197_);
lean_closure_set(v___f_5208_, 6, v___f_5188_);
lean_closure_set(v___f_5208_, 7, v___f_5191_);
lean_closure_set(v___f_5208_, 8, v___f_5189_);
lean_closure_set(v___f_5208_, 9, v___f_5192_);
lean_closure_set(v___f_5208_, 10, v___x_5207_);
v___x_5209_ = l_Lean_Elab_Tactic_NormCast_derive___lam__5(v___x_5183_, v___x_5193_, v___x_5206_, v___f_5208_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_);
if (lean_obj_tag(v___x_5209_) == 0)
{
lean_object* v_a_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; 
v_a_5210_ = lean_ctor_get(v___x_5209_, 0);
lean_inc(v_a_5210_);
lean_dec_ref(v___x_5209_);
v___x_5211_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__9));
v___x_5212_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_5198_, v___x_5211_, v_hasTrace_5182_, v_a_5178_, v_a_5179_);
if (lean_obj_tag(v___x_5212_) == 0)
{
lean_object* v_a_5213_; lean_object* v___f_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; 
v_a_5213_ = lean_ctor_get(v___x_5212_, 0);
lean_inc(v_a_5213_);
lean_dec_ref(v___x_5212_);
v___f_5214_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__8___boxed), 11, 6);
lean_closure_set(v___f_5214_, 0, v_squash_5205_);
lean_closure_set(v___f_5214_, 1, v_config_5175_);
lean_closure_set(v___f_5214_, 2, v_a_5187_);
lean_closure_set(v___f_5214_, 3, v_a_5210_);
lean_closure_set(v___f_5214_, 4, v___x_5197_);
lean_closure_set(v___f_5214_, 5, v_a_5213_);
v___x_5215_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__10));
v___x_5216_ = l_Lean_Elab_Tactic_NormCast_derive___lam__5(v___x_5183_, v___x_5193_, v___x_5215_, v___f_5214_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_);
return v___x_5216_;
}
else
{
lean_object* v_a_5217_; lean_object* v___x_5219_; uint8_t v_isShared_5220_; uint8_t v_isSharedCheck_5224_; 
lean_dec(v_a_5210_);
lean_dec_ref(v_squash_5205_);
lean_dec(v_a_5187_);
lean_dec_ref(v_config_5175_);
v_a_5217_ = lean_ctor_get(v___x_5212_, 0);
v_isSharedCheck_5224_ = !lean_is_exclusive(v___x_5212_);
if (v_isSharedCheck_5224_ == 0)
{
v___x_5219_ = v___x_5212_;
v_isShared_5220_ = v_isSharedCheck_5224_;
goto v_resetjp_5218_;
}
else
{
lean_inc(v_a_5217_);
lean_dec(v___x_5212_);
v___x_5219_ = lean_box(0);
v_isShared_5220_ = v_isSharedCheck_5224_;
goto v_resetjp_5218_;
}
v_resetjp_5218_:
{
lean_object* v___x_5222_; 
if (v_isShared_5220_ == 0)
{
v___x_5222_ = v___x_5219_;
goto v_reusejp_5221_;
}
else
{
lean_object* v_reuseFailAlloc_5223_; 
v_reuseFailAlloc_5223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5223_, 0, v_a_5217_);
v___x_5222_ = v_reuseFailAlloc_5223_;
goto v_reusejp_5221_;
}
v_reusejp_5221_:
{
return v___x_5222_;
}
}
}
}
else
{
lean_dec_ref(v_squash_5205_);
lean_dec(v_a_5187_);
lean_dec_ref(v_config_5175_);
return v___x_5209_;
}
}
else
{
lean_dec(v_a_5187_);
lean_dec_ref(v_config_5175_);
return v___x_5201_;
}
}
else
{
lean_object* v_a_5225_; lean_object* v___x_5227_; uint8_t v_isShared_5228_; uint8_t v_isSharedCheck_5232_; 
lean_dec(v_a_5185_);
lean_dec_ref(v_config_5175_);
v_a_5225_ = lean_ctor_get(v___x_5186_, 0);
v_isSharedCheck_5232_ = !lean_is_exclusive(v___x_5186_);
if (v_isSharedCheck_5232_ == 0)
{
v___x_5227_ = v___x_5186_;
v_isShared_5228_ = v_isSharedCheck_5232_;
goto v_resetjp_5226_;
}
else
{
lean_inc(v_a_5225_);
lean_dec(v___x_5186_);
v___x_5227_ = lean_box(0);
v_isShared_5228_ = v_isSharedCheck_5232_;
goto v_resetjp_5226_;
}
v_resetjp_5226_:
{
lean_object* v___x_5230_; 
if (v_isShared_5228_ == 0)
{
v___x_5230_ = v___x_5227_;
goto v_reusejp_5229_;
}
else
{
lean_object* v_reuseFailAlloc_5231_; 
v_reuseFailAlloc_5231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5231_, 0, v_a_5225_);
v___x_5230_ = v_reuseFailAlloc_5231_;
goto v_reusejp_5229_;
}
v_reusejp_5229_:
{
return v___x_5230_;
}
}
}
}
else
{
lean_object* v___x_5233_; lean_object* v_a_5234_; lean_object* v___x_5236_; uint8_t v_isShared_5237_; uint8_t v_isSharedCheck_5429_; 
v___x_5233_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___x_5183_, v_a_5178_);
v_a_5234_ = lean_ctor_get(v___x_5233_, 0);
v_isSharedCheck_5429_ = !lean_is_exclusive(v___x_5233_);
if (v_isSharedCheck_5429_ == 0)
{
v___x_5236_ = v___x_5233_;
v_isShared_5237_ = v_isSharedCheck_5429_;
goto v_resetjp_5235_;
}
else
{
lean_inc(v_a_5234_);
lean_dec(v___x_5233_);
v___x_5236_ = lean_box(0);
v_isShared_5237_ = v_isSharedCheck_5429_;
goto v_resetjp_5235_;
}
v_resetjp_5235_:
{
lean_object* v___f_5238_; lean_object* v___f_5239_; lean_object* v___f_5240_; lean_object* v___x_5241_; lean_object* v___y_5243_; lean_object* v___y_5244_; lean_object* v_a_5245_; lean_object* v___y_5256_; lean_object* v___y_5257_; lean_object* v_a_5258_; lean_object* v___y_5263_; lean_object* v___y_5264_; lean_object* v_a_5265_; lean_object* v___y_5279_; lean_object* v___y_5280_; lean_object* v_a_5281_; uint8_t v___x_5379_; 
v___f_5238_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__0));
v___f_5239_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__1));
lean_inc_ref(v_e_5174_);
v___f_5240_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__18___boxed), 7, 1);
lean_closure_set(v___f_5240_, 0, v_e_5174_);
v___x_5241_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_5379_ = lean_unbox(v_a_5234_);
if (v___x_5379_ == 0)
{
lean_object* v___x_5380_; uint8_t v___x_5381_; 
v___x_5380_ = l_Lean_trace_profiler;
v___x_5381_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_5181_, v___x_5380_);
if (v___x_5381_ == 0)
{
lean_object* v___x_5382_; lean_object* v_a_5383_; lean_object* v___x_5384_; 
lean_dec_ref(v___f_5240_);
lean_del_object(v___x_5236_);
lean_dec(v_a_5234_);
v___x_5382_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_e_5174_, v_a_5177_);
v_a_5383_ = lean_ctor_get(v___x_5382_, 0);
lean_inc(v_a_5383_);
lean_dec_ref(v___x_5382_);
v___x_5384_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_5179_);
if (lean_obj_tag(v___x_5384_) == 0)
{
lean_object* v_a_5385_; lean_object* v___x_5386_; lean_object* v___x_5387_; lean_object* v___f_5388_; lean_object* v___f_5389_; lean_object* v___f_5390_; lean_object* v___x_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___x_5394_; lean_object* v___x_5395_; lean_object* v___f_5396_; lean_object* v___x_5397_; 
v_a_5385_ = lean_ctor_get(v___x_5384_, 0);
lean_inc(v_a_5385_);
lean_dec_ref(v___x_5384_);
v___x_5386_ = lean_box(0);
v___x_5387_ = lean_box(v_hasTrace_5182_);
v___f_5388_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__9___boxed), 11, 2);
lean_closure_set(v___f_5388_, 0, v___x_5386_);
lean_closure_set(v___f_5388_, 1, v___x_5387_);
v___f_5389_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__2));
v___f_5390_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__3));
lean_inc(v_a_5383_);
v___x_5391_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5391_, 0, v_a_5383_);
lean_ctor_set(v___x_5391_, 1, v___x_5386_);
lean_ctor_set_uint8(v___x_5391_, sizeof(void*)*2, v_hasTrace_5182_);
v___x_5392_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__5));
v___x_5393_ = lean_unsigned_to_nat(0u);
v___x_5394_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__6));
v___x_5395_ = lean_box(v_hasTrace_5182_);
lean_inc(v_a_5385_);
lean_inc_ref(v_config_5175_);
v___f_5396_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__14___boxed), 17, 12);
lean_closure_set(v___f_5396_, 0, v_config_5175_);
lean_closure_set(v___f_5396_, 1, v___x_5394_);
lean_closure_set(v___f_5396_, 2, v_a_5385_);
lean_closure_set(v___f_5396_, 3, v___x_5393_);
lean_closure_set(v___f_5396_, 4, v___f_5238_);
lean_closure_set(v___f_5396_, 5, v___f_5388_);
lean_closure_set(v___f_5396_, 6, v___f_5389_);
lean_closure_set(v___f_5396_, 7, v___f_5239_);
lean_closure_set(v___f_5396_, 8, v___f_5390_);
lean_closure_set(v___f_5396_, 9, v___x_5395_);
lean_closure_set(v___f_5396_, 10, v_a_5383_);
lean_closure_set(v___f_5396_, 11, v___x_5391_);
v___x_5397_ = l_Lean_Elab_Tactic_NormCast_derive___lam__27(v___x_5183_, v_hasTrace_5182_, v___x_5392_, v___f_5396_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_);
if (lean_obj_tag(v___x_5397_) == 0)
{
lean_object* v_a_5398_; lean_object* v___x_5399_; lean_object* v_up_5400_; lean_object* v_squash_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___f_5404_; lean_object* v___x_5405_; 
v_a_5398_ = lean_ctor_get(v___x_5397_, 0);
lean_inc(v_a_5398_);
lean_dec_ref(v___x_5397_);
v___x_5399_ = l_Lean_Meta_NormCast_normCastExt;
v_up_5400_ = lean_ctor_get(v___x_5399_, 0);
lean_inc_ref(v_up_5400_);
v_squash_5401_ = lean_ctor_get(v___x_5399_, 2);
lean_inc_ref(v_squash_5401_);
v___x_5402_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__7));
v___x_5403_ = lean_box(v_hasTrace_5182_);
lean_inc(v_a_5385_);
lean_inc_ref(v_config_5175_);
v___f_5404_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__15___boxed), 16, 11);
lean_closure_set(v___f_5404_, 0, v_up_5400_);
lean_closure_set(v___f_5404_, 1, v_config_5175_);
lean_closure_set(v___f_5404_, 2, v___x_5394_);
lean_closure_set(v___f_5404_, 3, v_a_5385_);
lean_closure_set(v___f_5404_, 4, v_a_5398_);
lean_closure_set(v___f_5404_, 5, v___x_5393_);
lean_closure_set(v___f_5404_, 6, v___f_5238_);
lean_closure_set(v___f_5404_, 7, v___f_5389_);
lean_closure_set(v___f_5404_, 8, v___f_5239_);
lean_closure_set(v___f_5404_, 9, v___f_5390_);
lean_closure_set(v___f_5404_, 10, v___x_5403_);
v___x_5405_ = l_Lean_Elab_Tactic_NormCast_derive___lam__27(v___x_5183_, v_hasTrace_5182_, v___x_5402_, v___f_5404_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_);
if (lean_obj_tag(v___x_5405_) == 0)
{
lean_object* v_a_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; 
v_a_5406_ = lean_ctor_get(v___x_5405_, 0);
lean_inc(v_a_5406_);
lean_dec_ref(v___x_5405_);
v___x_5407_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__9));
v___x_5408_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_5394_, v___x_5407_, v___x_5381_, v_a_5178_, v_a_5179_);
if (lean_obj_tag(v___x_5408_) == 0)
{
lean_object* v_a_5409_; lean_object* v___f_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; 
v_a_5409_ = lean_ctor_get(v___x_5408_, 0);
lean_inc(v_a_5409_);
lean_dec_ref(v___x_5408_);
v___f_5410_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__8___boxed), 11, 6);
lean_closure_set(v___f_5410_, 0, v_squash_5401_);
lean_closure_set(v___f_5410_, 1, v_config_5175_);
lean_closure_set(v___f_5410_, 2, v_a_5385_);
lean_closure_set(v___f_5410_, 3, v_a_5406_);
lean_closure_set(v___f_5410_, 4, v___x_5393_);
lean_closure_set(v___f_5410_, 5, v_a_5409_);
v___x_5411_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__10));
v___x_5412_ = l_Lean_Elab_Tactic_NormCast_derive___lam__27(v___x_5183_, v_hasTrace_5182_, v___x_5411_, v___f_5410_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_);
return v___x_5412_;
}
else
{
lean_object* v_a_5413_; lean_object* v___x_5415_; uint8_t v_isShared_5416_; uint8_t v_isSharedCheck_5420_; 
lean_dec(v_a_5406_);
lean_dec_ref(v_squash_5401_);
lean_dec(v_a_5385_);
lean_dec_ref(v_config_5175_);
v_a_5413_ = lean_ctor_get(v___x_5408_, 0);
v_isSharedCheck_5420_ = !lean_is_exclusive(v___x_5408_);
if (v_isSharedCheck_5420_ == 0)
{
v___x_5415_ = v___x_5408_;
v_isShared_5416_ = v_isSharedCheck_5420_;
goto v_resetjp_5414_;
}
else
{
lean_inc(v_a_5413_);
lean_dec(v___x_5408_);
v___x_5415_ = lean_box(0);
v_isShared_5416_ = v_isSharedCheck_5420_;
goto v_resetjp_5414_;
}
v_resetjp_5414_:
{
lean_object* v___x_5418_; 
if (v_isShared_5416_ == 0)
{
v___x_5418_ = v___x_5415_;
goto v_reusejp_5417_;
}
else
{
lean_object* v_reuseFailAlloc_5419_; 
v_reuseFailAlloc_5419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5419_, 0, v_a_5413_);
v___x_5418_ = v_reuseFailAlloc_5419_;
goto v_reusejp_5417_;
}
v_reusejp_5417_:
{
return v___x_5418_;
}
}
}
}
else
{
lean_dec_ref(v_squash_5401_);
lean_dec(v_a_5385_);
lean_dec_ref(v_config_5175_);
return v___x_5405_;
}
}
else
{
lean_dec(v_a_5385_);
lean_dec_ref(v_config_5175_);
return v___x_5397_;
}
}
else
{
lean_object* v_a_5421_; lean_object* v___x_5423_; uint8_t v_isShared_5424_; uint8_t v_isSharedCheck_5428_; 
lean_dec(v_a_5383_);
lean_dec_ref(v_config_5175_);
v_a_5421_ = lean_ctor_get(v___x_5384_, 0);
v_isSharedCheck_5428_ = !lean_is_exclusive(v___x_5384_);
if (v_isSharedCheck_5428_ == 0)
{
v___x_5423_ = v___x_5384_;
v_isShared_5424_ = v_isSharedCheck_5428_;
goto v_resetjp_5422_;
}
else
{
lean_inc(v_a_5421_);
lean_dec(v___x_5384_);
v___x_5423_ = lean_box(0);
v_isShared_5424_ = v_isSharedCheck_5428_;
goto v_resetjp_5422_;
}
v_resetjp_5422_:
{
lean_object* v___x_5426_; 
if (v_isShared_5424_ == 0)
{
v___x_5426_ = v___x_5423_;
goto v_reusejp_5425_;
}
else
{
lean_object* v_reuseFailAlloc_5427_; 
v_reuseFailAlloc_5427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5427_, 0, v_a_5421_);
v___x_5426_ = v_reuseFailAlloc_5427_;
goto v_reusejp_5425_;
}
v_reusejp_5425_:
{
return v___x_5426_;
}
}
}
}
else
{
goto v___jp_5283_;
}
}
else
{
goto v___jp_5283_;
}
v___jp_5242_:
{
lean_object* v___x_5246_; double v___x_5247_; double v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; uint8_t v___x_5253_; lean_object* v___x_5254_; 
v___x_5246_ = lean_io_get_num_heartbeats();
v___x_5247_ = lean_float_of_nat(v___y_5244_);
v___x_5248_ = lean_float_of_nat(v___x_5246_);
v___x_5249_ = lean_box_float(v___x_5247_);
v___x_5250_ = lean_box_float(v___x_5248_);
v___x_5251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5251_, 0, v___x_5249_);
lean_ctor_set(v___x_5251_, 1, v___x_5250_);
v___x_5252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5252_, 0, v_a_5245_);
lean_ctor_set(v___x_5252_, 1, v___x_5251_);
v___x_5253_ = lean_unbox(v_a_5234_);
lean_dec(v_a_5234_);
v___x_5254_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_5183_, v_hasTrace_5182_, v___x_5241_, v_options_5181_, v___x_5253_, v___y_5243_, v___f_5240_, v___x_5252_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_);
return v___x_5254_;
}
v___jp_5255_:
{
lean_object* v___x_5260_; 
if (v_isShared_5237_ == 0)
{
lean_ctor_set(v___x_5236_, 0, v_a_5258_);
v___x_5260_ = v___x_5236_;
goto v_reusejp_5259_;
}
else
{
lean_object* v_reuseFailAlloc_5261_; 
v_reuseFailAlloc_5261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5261_, 0, v_a_5258_);
v___x_5260_ = v_reuseFailAlloc_5261_;
goto v_reusejp_5259_;
}
v_reusejp_5259_:
{
v___y_5243_ = v___y_5256_;
v___y_5244_ = v___y_5257_;
v_a_5245_ = v___x_5260_;
goto v___jp_5242_;
}
}
v___jp_5262_:
{
lean_object* v___x_5266_; double v___x_5267_; double v___x_5268_; double v___x_5269_; double v___x_5270_; double v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; uint8_t v___x_5276_; lean_object* v___x_5277_; 
v___x_5266_ = lean_io_mono_nanos_now();
v___x_5267_ = lean_float_of_nat(v___y_5264_);
v___x_5268_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1);
v___x_5269_ = lean_float_div(v___x_5267_, v___x_5268_);
v___x_5270_ = lean_float_of_nat(v___x_5266_);
v___x_5271_ = lean_float_div(v___x_5270_, v___x_5268_);
v___x_5272_ = lean_box_float(v___x_5269_);
v___x_5273_ = lean_box_float(v___x_5271_);
v___x_5274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5274_, 0, v___x_5272_);
lean_ctor_set(v___x_5274_, 1, v___x_5273_);
v___x_5275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5275_, 0, v_a_5265_);
lean_ctor_set(v___x_5275_, 1, v___x_5274_);
v___x_5276_ = lean_unbox(v_a_5234_);
lean_dec(v_a_5234_);
v___x_5277_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_5183_, v_hasTrace_5182_, v___x_5241_, v_options_5181_, v___x_5276_, v___y_5263_, v___f_5240_, v___x_5275_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_);
return v___x_5277_;
}
v___jp_5278_:
{
lean_object* v___x_5282_; 
v___x_5282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5282_, 0, v_a_5281_);
v___y_5263_ = v___y_5279_;
v___y_5264_ = v___y_5280_;
v_a_5265_ = v___x_5282_;
goto v___jp_5262_;
}
v___jp_5283_:
{
lean_object* v___x_5284_; lean_object* v_a_5285_; lean_object* v___x_5286_; uint8_t v___x_5287_; 
v___x_5284_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg(v_a_5179_);
v_a_5285_ = lean_ctor_get(v___x_5284_, 0);
lean_inc(v_a_5285_);
lean_dec_ref(v___x_5284_);
v___x_5286_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5287_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_5181_, v___x_5286_);
if (v___x_5287_ == 0)
{
lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v_a_5290_; lean_object* v___x_5291_; 
lean_del_object(v___x_5236_);
v___x_5288_ = lean_io_mono_nanos_now();
v___x_5289_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_e_5174_, v_a_5177_);
v_a_5290_ = lean_ctor_get(v___x_5289_, 0);
lean_inc(v_a_5290_);
lean_dec_ref(v___x_5289_);
v___x_5291_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_5179_);
if (lean_obj_tag(v___x_5291_) == 0)
{
lean_object* v_a_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; lean_object* v___f_5295_; lean_object* v___f_5296_; lean_object* v___f_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v___f_5303_; lean_object* v___x_5304_; 
v_a_5292_ = lean_ctor_get(v___x_5291_, 0);
lean_inc(v_a_5292_);
lean_dec_ref(v___x_5291_);
v___x_5293_ = lean_box(0);
v___x_5294_ = lean_box(v_hasTrace_5182_);
v___f_5295_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__9___boxed), 11, 2);
lean_closure_set(v___f_5295_, 0, v___x_5293_);
lean_closure_set(v___f_5295_, 1, v___x_5294_);
v___f_5296_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__2));
v___f_5297_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__3));
lean_inc(v_a_5290_);
v___x_5298_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5298_, 0, v_a_5290_);
lean_ctor_set(v___x_5298_, 1, v___x_5293_);
lean_ctor_set_uint8(v___x_5298_, sizeof(void*)*2, v_hasTrace_5182_);
v___x_5299_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__5));
v___x_5300_ = lean_unsigned_to_nat(0u);
v___x_5301_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__6));
v___x_5302_ = lean_box(v_hasTrace_5182_);
lean_inc(v_a_5292_);
lean_inc_ref(v_config_5175_);
v___f_5303_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__14___boxed), 17, 12);
lean_closure_set(v___f_5303_, 0, v_config_5175_);
lean_closure_set(v___f_5303_, 1, v___x_5301_);
lean_closure_set(v___f_5303_, 2, v_a_5292_);
lean_closure_set(v___f_5303_, 3, v___x_5300_);
lean_closure_set(v___f_5303_, 4, v___f_5238_);
lean_closure_set(v___f_5303_, 5, v___f_5295_);
lean_closure_set(v___f_5303_, 6, v___f_5296_);
lean_closure_set(v___f_5303_, 7, v___f_5239_);
lean_closure_set(v___f_5303_, 8, v___f_5297_);
lean_closure_set(v___f_5303_, 9, v___x_5302_);
lean_closure_set(v___f_5303_, 10, v_a_5290_);
lean_closure_set(v___f_5303_, 11, v___x_5298_);
v___x_5304_ = l_Lean_Elab_Tactic_NormCast_derive___lam__10(v___x_5183_, v_hasTrace_5182_, v___x_5299_, v___f_5303_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_);
if (lean_obj_tag(v___x_5304_) == 0)
{
lean_object* v_a_5305_; lean_object* v___x_5306_; lean_object* v_up_5307_; lean_object* v_squash_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___f_5311_; lean_object* v___x_5312_; 
v_a_5305_ = lean_ctor_get(v___x_5304_, 0);
lean_inc(v_a_5305_);
lean_dec_ref(v___x_5304_);
v___x_5306_ = l_Lean_Meta_NormCast_normCastExt;
v_up_5307_ = lean_ctor_get(v___x_5306_, 0);
lean_inc_ref(v_up_5307_);
v_squash_5308_ = lean_ctor_get(v___x_5306_, 2);
lean_inc_ref(v_squash_5308_);
v___x_5309_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__7));
v___x_5310_ = lean_box(v_hasTrace_5182_);
lean_inc(v_a_5292_);
lean_inc_ref(v_config_5175_);
v___f_5311_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__15___boxed), 16, 11);
lean_closure_set(v___f_5311_, 0, v_up_5307_);
lean_closure_set(v___f_5311_, 1, v_config_5175_);
lean_closure_set(v___f_5311_, 2, v___x_5301_);
lean_closure_set(v___f_5311_, 3, v_a_5292_);
lean_closure_set(v___f_5311_, 4, v_a_5305_);
lean_closure_set(v___f_5311_, 5, v___x_5300_);
lean_closure_set(v___f_5311_, 6, v___f_5238_);
lean_closure_set(v___f_5311_, 7, v___f_5296_);
lean_closure_set(v___f_5311_, 8, v___f_5239_);
lean_closure_set(v___f_5311_, 9, v___f_5297_);
lean_closure_set(v___f_5311_, 10, v___x_5310_);
v___x_5312_ = l_Lean_Elab_Tactic_NormCast_derive___lam__10(v___x_5183_, v_hasTrace_5182_, v___x_5309_, v___f_5311_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_);
if (lean_obj_tag(v___x_5312_) == 0)
{
lean_object* v_a_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; 
v_a_5313_ = lean_ctor_get(v___x_5312_, 0);
lean_inc(v_a_5313_);
lean_dec_ref(v___x_5312_);
v___x_5314_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__9));
v___x_5315_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_5301_, v___x_5314_, v___x_5287_, v_a_5178_, v_a_5179_);
if (lean_obj_tag(v___x_5315_) == 0)
{
lean_object* v_a_5316_; lean_object* v___f_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; 
v_a_5316_ = lean_ctor_get(v___x_5315_, 0);
lean_inc(v_a_5316_);
lean_dec_ref(v___x_5315_);
v___f_5317_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__8___boxed), 11, 6);
lean_closure_set(v___f_5317_, 0, v_squash_5308_);
lean_closure_set(v___f_5317_, 1, v_config_5175_);
lean_closure_set(v___f_5317_, 2, v_a_5292_);
lean_closure_set(v___f_5317_, 3, v_a_5313_);
lean_closure_set(v___f_5317_, 4, v___x_5300_);
lean_closure_set(v___f_5317_, 5, v_a_5316_);
v___x_5318_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__10));
v___x_5319_ = l_Lean_Elab_Tactic_NormCast_derive___lam__10(v___x_5183_, v_hasTrace_5182_, v___x_5318_, v___f_5317_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_);
if (lean_obj_tag(v___x_5319_) == 0)
{
lean_object* v_a_5320_; lean_object* v___x_5322_; uint8_t v_isShared_5323_; uint8_t v_isSharedCheck_5327_; 
v_a_5320_ = lean_ctor_get(v___x_5319_, 0);
v_isSharedCheck_5327_ = !lean_is_exclusive(v___x_5319_);
if (v_isSharedCheck_5327_ == 0)
{
v___x_5322_ = v___x_5319_;
v_isShared_5323_ = v_isSharedCheck_5327_;
goto v_resetjp_5321_;
}
else
{
lean_inc(v_a_5320_);
lean_dec(v___x_5319_);
v___x_5322_ = lean_box(0);
v_isShared_5323_ = v_isSharedCheck_5327_;
goto v_resetjp_5321_;
}
v_resetjp_5321_:
{
lean_object* v___x_5325_; 
if (v_isShared_5323_ == 0)
{
lean_ctor_set_tag(v___x_5322_, 1);
v___x_5325_ = v___x_5322_;
goto v_reusejp_5324_;
}
else
{
lean_object* v_reuseFailAlloc_5326_; 
v_reuseFailAlloc_5326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5326_, 0, v_a_5320_);
v___x_5325_ = v_reuseFailAlloc_5326_;
goto v_reusejp_5324_;
}
v_reusejp_5324_:
{
v___y_5263_ = v_a_5285_;
v___y_5264_ = v___x_5288_;
v_a_5265_ = v___x_5325_;
goto v___jp_5262_;
}
}
}
else
{
lean_object* v_a_5328_; 
v_a_5328_ = lean_ctor_get(v___x_5319_, 0);
lean_inc(v_a_5328_);
lean_dec_ref(v___x_5319_);
v___y_5279_ = v_a_5285_;
v___y_5280_ = v___x_5288_;
v_a_5281_ = v_a_5328_;
goto v___jp_5278_;
}
}
else
{
lean_object* v_a_5329_; 
lean_dec(v_a_5313_);
lean_dec_ref(v_squash_5308_);
lean_dec(v_a_5292_);
lean_dec_ref(v_config_5175_);
v_a_5329_ = lean_ctor_get(v___x_5315_, 0);
lean_inc(v_a_5329_);
lean_dec_ref(v___x_5315_);
v___y_5279_ = v_a_5285_;
v___y_5280_ = v___x_5288_;
v_a_5281_ = v_a_5329_;
goto v___jp_5278_;
}
}
else
{
lean_object* v_a_5330_; 
lean_dec_ref(v_squash_5308_);
lean_dec(v_a_5292_);
lean_dec_ref(v_config_5175_);
v_a_5330_ = lean_ctor_get(v___x_5312_, 0);
lean_inc(v_a_5330_);
lean_dec_ref(v___x_5312_);
v___y_5279_ = v_a_5285_;
v___y_5280_ = v___x_5288_;
v_a_5281_ = v_a_5330_;
goto v___jp_5278_;
}
}
else
{
lean_object* v_a_5331_; 
lean_dec(v_a_5292_);
lean_dec_ref(v_config_5175_);
v_a_5331_ = lean_ctor_get(v___x_5304_, 0);
lean_inc(v_a_5331_);
lean_dec_ref(v___x_5304_);
v___y_5279_ = v_a_5285_;
v___y_5280_ = v___x_5288_;
v_a_5281_ = v_a_5331_;
goto v___jp_5278_;
}
}
else
{
lean_object* v_a_5332_; 
lean_dec(v_a_5290_);
lean_dec_ref(v_config_5175_);
v_a_5332_ = lean_ctor_get(v___x_5291_, 0);
lean_inc(v_a_5332_);
lean_dec_ref(v___x_5291_);
v___y_5279_ = v_a_5285_;
v___y_5280_ = v___x_5288_;
v_a_5281_ = v_a_5332_;
goto v___jp_5278_;
}
}
else
{
lean_object* v___x_5333_; lean_object* v___x_5334_; lean_object* v_a_5335_; lean_object* v___x_5336_; 
v___x_5333_ = lean_io_get_num_heartbeats();
v___x_5334_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_e_5174_, v_a_5177_);
v_a_5335_ = lean_ctor_get(v___x_5334_, 0);
lean_inc(v_a_5335_);
lean_dec_ref(v___x_5334_);
v___x_5336_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_5179_);
if (lean_obj_tag(v___x_5336_) == 0)
{
lean_object* v_a_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___f_5340_; lean_object* v___f_5341_; lean_object* v___f_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; lean_object* v___f_5348_; lean_object* v___x_5349_; 
v_a_5337_ = lean_ctor_get(v___x_5336_, 0);
lean_inc(v_a_5337_);
lean_dec_ref(v___x_5336_);
v___x_5338_ = lean_box(0);
v___x_5339_ = lean_box(v___x_5287_);
v___f_5340_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__6___boxed), 11, 2);
lean_closure_set(v___f_5340_, 0, v___x_5338_);
lean_closure_set(v___f_5340_, 1, v___x_5339_);
v___f_5341_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__2));
v___f_5342_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__3));
lean_inc(v_a_5335_);
v___x_5343_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5343_, 0, v_a_5335_);
lean_ctor_set(v___x_5343_, 1, v___x_5338_);
lean_ctor_set_uint8(v___x_5343_, sizeof(void*)*2, v___x_5287_);
v___x_5344_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__5));
v___x_5345_ = lean_unsigned_to_nat(0u);
v___x_5346_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__6));
v___x_5347_ = lean_box(v___x_5287_);
lean_inc(v_a_5337_);
lean_inc_ref(v_config_5175_);
v___f_5348_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__7___boxed), 17, 12);
lean_closure_set(v___f_5348_, 0, v_config_5175_);
lean_closure_set(v___f_5348_, 1, v___x_5346_);
lean_closure_set(v___f_5348_, 2, v_a_5337_);
lean_closure_set(v___f_5348_, 3, v___x_5345_);
lean_closure_set(v___f_5348_, 4, v___f_5238_);
lean_closure_set(v___f_5348_, 5, v___f_5340_);
lean_closure_set(v___f_5348_, 6, v___f_5341_);
lean_closure_set(v___f_5348_, 7, v___f_5239_);
lean_closure_set(v___f_5348_, 8, v___f_5342_);
lean_closure_set(v___f_5348_, 9, v___x_5347_);
lean_closure_set(v___f_5348_, 10, v_a_5335_);
lean_closure_set(v___f_5348_, 11, v___x_5343_);
v___x_5349_ = l_Lean_Elab_Tactic_NormCast_derive___lam__16(v___x_5183_, v___x_5287_, v___x_5241_, v___x_5286_, v___x_5344_, v___f_5348_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_);
if (lean_obj_tag(v___x_5349_) == 0)
{
lean_object* v_a_5350_; lean_object* v___x_5351_; lean_object* v_up_5352_; lean_object* v_squash_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; lean_object* v___f_5356_; lean_object* v___x_5357_; 
v_a_5350_ = lean_ctor_get(v___x_5349_, 0);
lean_inc(v_a_5350_);
lean_dec_ref(v___x_5349_);
v___x_5351_ = l_Lean_Meta_NormCast_normCastExt;
v_up_5352_ = lean_ctor_get(v___x_5351_, 0);
lean_inc_ref(v_up_5352_);
v_squash_5353_ = lean_ctor_get(v___x_5351_, 2);
lean_inc_ref(v_squash_5353_);
v___x_5354_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__7));
v___x_5355_ = lean_box(v___x_5287_);
lean_inc(v_a_5337_);
lean_inc_ref(v_config_5175_);
v___f_5356_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__12___boxed), 16, 11);
lean_closure_set(v___f_5356_, 0, v_up_5352_);
lean_closure_set(v___f_5356_, 1, v_config_5175_);
lean_closure_set(v___f_5356_, 2, v___x_5346_);
lean_closure_set(v___f_5356_, 3, v_a_5337_);
lean_closure_set(v___f_5356_, 4, v_a_5350_);
lean_closure_set(v___f_5356_, 5, v___x_5345_);
lean_closure_set(v___f_5356_, 6, v___f_5238_);
lean_closure_set(v___f_5356_, 7, v___f_5341_);
lean_closure_set(v___f_5356_, 8, v___f_5239_);
lean_closure_set(v___f_5356_, 9, v___f_5342_);
lean_closure_set(v___f_5356_, 10, v___x_5355_);
v___x_5357_ = l_Lean_Elab_Tactic_NormCast_derive___lam__16(v___x_5183_, v___x_5287_, v___x_5241_, v___x_5286_, v___x_5354_, v___f_5356_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_);
if (lean_obj_tag(v___x_5357_) == 0)
{
lean_object* v_a_5358_; lean_object* v___x_5359_; uint8_t v___x_5360_; lean_object* v___x_5361_; 
v_a_5358_ = lean_ctor_get(v___x_5357_, 0);
lean_inc(v_a_5358_);
lean_dec_ref(v___x_5357_);
v___x_5359_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__9));
v___x_5360_ = 0;
v___x_5361_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_5346_, v___x_5359_, v___x_5360_, v_a_5178_, v_a_5179_);
if (lean_obj_tag(v___x_5361_) == 0)
{
lean_object* v_a_5362_; lean_object* v___f_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; 
v_a_5362_ = lean_ctor_get(v___x_5361_, 0);
lean_inc(v_a_5362_);
lean_dec_ref(v___x_5361_);
v___f_5363_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__8___boxed), 11, 6);
lean_closure_set(v___f_5363_, 0, v_squash_5353_);
lean_closure_set(v___f_5363_, 1, v_config_5175_);
lean_closure_set(v___f_5363_, 2, v_a_5337_);
lean_closure_set(v___f_5363_, 3, v_a_5358_);
lean_closure_set(v___f_5363_, 4, v___x_5345_);
lean_closure_set(v___f_5363_, 5, v_a_5362_);
v___x_5364_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__10));
v___x_5365_ = l_Lean_Elab_Tactic_NormCast_derive___lam__16(v___x_5183_, v___x_5287_, v___x_5241_, v___x_5286_, v___x_5364_, v___f_5363_, v_a_5176_, v_a_5177_, v_a_5178_, v_a_5179_);
if (lean_obj_tag(v___x_5365_) == 0)
{
lean_object* v_a_5366_; lean_object* v___x_5368_; uint8_t v_isShared_5369_; uint8_t v_isSharedCheck_5373_; 
lean_del_object(v___x_5236_);
v_a_5366_ = lean_ctor_get(v___x_5365_, 0);
v_isSharedCheck_5373_ = !lean_is_exclusive(v___x_5365_);
if (v_isSharedCheck_5373_ == 0)
{
v___x_5368_ = v___x_5365_;
v_isShared_5369_ = v_isSharedCheck_5373_;
goto v_resetjp_5367_;
}
else
{
lean_inc(v_a_5366_);
lean_dec(v___x_5365_);
v___x_5368_ = lean_box(0);
v_isShared_5369_ = v_isSharedCheck_5373_;
goto v_resetjp_5367_;
}
v_resetjp_5367_:
{
lean_object* v___x_5371_; 
if (v_isShared_5369_ == 0)
{
lean_ctor_set_tag(v___x_5368_, 1);
v___x_5371_ = v___x_5368_;
goto v_reusejp_5370_;
}
else
{
lean_object* v_reuseFailAlloc_5372_; 
v_reuseFailAlloc_5372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5372_, 0, v_a_5366_);
v___x_5371_ = v_reuseFailAlloc_5372_;
goto v_reusejp_5370_;
}
v_reusejp_5370_:
{
v___y_5243_ = v_a_5285_;
v___y_5244_ = v___x_5333_;
v_a_5245_ = v___x_5371_;
goto v___jp_5242_;
}
}
}
else
{
lean_object* v_a_5374_; 
v_a_5374_ = lean_ctor_get(v___x_5365_, 0);
lean_inc(v_a_5374_);
lean_dec_ref(v___x_5365_);
v___y_5256_ = v_a_5285_;
v___y_5257_ = v___x_5333_;
v_a_5258_ = v_a_5374_;
goto v___jp_5255_;
}
}
else
{
lean_object* v_a_5375_; 
lean_dec(v_a_5358_);
lean_dec_ref(v_squash_5353_);
lean_dec(v_a_5337_);
lean_dec_ref(v_config_5175_);
v_a_5375_ = lean_ctor_get(v___x_5361_, 0);
lean_inc(v_a_5375_);
lean_dec_ref(v___x_5361_);
v___y_5256_ = v_a_5285_;
v___y_5257_ = v___x_5333_;
v_a_5258_ = v_a_5375_;
goto v___jp_5255_;
}
}
else
{
lean_object* v_a_5376_; 
lean_dec_ref(v_squash_5353_);
lean_dec(v_a_5337_);
lean_dec_ref(v_config_5175_);
v_a_5376_ = lean_ctor_get(v___x_5357_, 0);
lean_inc(v_a_5376_);
lean_dec_ref(v___x_5357_);
v___y_5256_ = v_a_5285_;
v___y_5257_ = v___x_5333_;
v_a_5258_ = v_a_5376_;
goto v___jp_5255_;
}
}
else
{
lean_object* v_a_5377_; 
lean_dec(v_a_5337_);
lean_dec_ref(v_config_5175_);
v_a_5377_ = lean_ctor_get(v___x_5349_, 0);
lean_inc(v_a_5377_);
lean_dec_ref(v___x_5349_);
v___y_5256_ = v_a_5285_;
v___y_5257_ = v___x_5333_;
v_a_5258_ = v_a_5377_;
goto v___jp_5255_;
}
}
else
{
lean_object* v_a_5378_; 
lean_dec(v_a_5335_);
lean_dec_ref(v_config_5175_);
v_a_5378_ = lean_ctor_get(v___x_5336_, 0);
lean_inc(v_a_5378_);
lean_dec_ref(v___x_5336_);
v___y_5256_ = v_a_5285_;
v___y_5257_ = v___x_5333_;
v_a_5258_ = v_a_5378_;
goto v___jp_5255_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___boxed(lean_object* v_e_5430_, lean_object* v_config_5431_, lean_object* v_a_5432_, lean_object* v_a_5433_, lean_object* v_a_5434_, lean_object* v_a_5435_, lean_object* v_a_5436_){
_start:
{
lean_object* v_res_5437_; 
v_res_5437_ = l_Lean_Elab_Tactic_NormCast_derive(v_e_5430_, v_config_5431_, v_a_5432_, v_a_5433_, v_a_5434_, v_a_5435_);
lean_dec(v_a_5435_);
lean_dec_ref(v_a_5434_);
lean_dec(v_a_5433_);
lean_dec_ref(v_a_5432_);
return v_res_5437_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_5438_; lean_object* v___x_5439_; lean_object* v___x_5440_; 
v___x_5438_ = lean_box(0);
v___x_5439_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_5440_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5440_, 0, v___x_5439_);
lean_ctor_set(v___x_5440_, 1, v___x_5438_);
return v___x_5440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg(){
_start:
{
lean_object* v___x_5442_; lean_object* v___x_5443_; 
v___x_5442_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0);
v___x_5443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5443_, 0, v___x_5442_);
return v___x_5443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___boxed(lean_object* v___y_5444_){
_start:
{
lean_object* v_res_5445_; 
v_res_5445_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg();
return v_res_5445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0(lean_object* v_00_u03b1_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_){
_start:
{
lean_object* v___x_5454_; 
v___x_5454_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg();
return v___x_5454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___boxed(lean_object* v_00_u03b1_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_){
_start:
{
lean_object* v_res_5463_; 
v_res_5463_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0(v_00_u03b1_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_, v___y_5460_, v___y_5461_);
lean_dec(v___y_5461_);
lean_dec_ref(v___y_5460_);
lean_dec(v___y_5459_);
lean_dec_ref(v___y_5458_);
lean_dec(v___y_5457_);
lean_dec_ref(v___y_5456_);
return v_res_5463_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg(lean_object* v_e_5464_, lean_object* v___y_5465_){
_start:
{
uint8_t v___x_5467_; 
v___x_5467_ = l_Lean_Expr_hasMVar(v_e_5464_);
if (v___x_5467_ == 0)
{
lean_object* v___x_5468_; 
v___x_5468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5468_, 0, v_e_5464_);
return v___x_5468_;
}
else
{
lean_object* v___x_5469_; lean_object* v_mctx_5470_; lean_object* v___x_5471_; lean_object* v_fst_5472_; lean_object* v_snd_5473_; lean_object* v___x_5474_; lean_object* v_cache_5475_; lean_object* v_zetaDeltaFVarIds_5476_; lean_object* v_postponed_5477_; lean_object* v_diag_5478_; lean_object* v___x_5480_; uint8_t v_isShared_5481_; uint8_t v_isSharedCheck_5487_; 
v___x_5469_ = lean_st_ref_get(v___y_5465_);
v_mctx_5470_ = lean_ctor_get(v___x_5469_, 0);
lean_inc_ref(v_mctx_5470_);
lean_dec(v___x_5469_);
v___x_5471_ = l_Lean_instantiateMVarsCore(v_mctx_5470_, v_e_5464_);
v_fst_5472_ = lean_ctor_get(v___x_5471_, 0);
lean_inc(v_fst_5472_);
v_snd_5473_ = lean_ctor_get(v___x_5471_, 1);
lean_inc(v_snd_5473_);
lean_dec_ref(v___x_5471_);
v___x_5474_ = lean_st_ref_take(v___y_5465_);
v_cache_5475_ = lean_ctor_get(v___x_5474_, 1);
v_zetaDeltaFVarIds_5476_ = lean_ctor_get(v___x_5474_, 2);
v_postponed_5477_ = lean_ctor_get(v___x_5474_, 3);
v_diag_5478_ = lean_ctor_get(v___x_5474_, 4);
v_isSharedCheck_5487_ = !lean_is_exclusive(v___x_5474_);
if (v_isSharedCheck_5487_ == 0)
{
lean_object* v_unused_5488_; 
v_unused_5488_ = lean_ctor_get(v___x_5474_, 0);
lean_dec(v_unused_5488_);
v___x_5480_ = v___x_5474_;
v_isShared_5481_ = v_isSharedCheck_5487_;
goto v_resetjp_5479_;
}
else
{
lean_inc(v_diag_5478_);
lean_inc(v_postponed_5477_);
lean_inc(v_zetaDeltaFVarIds_5476_);
lean_inc(v_cache_5475_);
lean_dec(v___x_5474_);
v___x_5480_ = lean_box(0);
v_isShared_5481_ = v_isSharedCheck_5487_;
goto v_resetjp_5479_;
}
v_resetjp_5479_:
{
lean_object* v___x_5483_; 
if (v_isShared_5481_ == 0)
{
lean_ctor_set(v___x_5480_, 0, v_snd_5473_);
v___x_5483_ = v___x_5480_;
goto v_reusejp_5482_;
}
else
{
lean_object* v_reuseFailAlloc_5486_; 
v_reuseFailAlloc_5486_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5486_, 0, v_snd_5473_);
lean_ctor_set(v_reuseFailAlloc_5486_, 1, v_cache_5475_);
lean_ctor_set(v_reuseFailAlloc_5486_, 2, v_zetaDeltaFVarIds_5476_);
lean_ctor_set(v_reuseFailAlloc_5486_, 3, v_postponed_5477_);
lean_ctor_set(v_reuseFailAlloc_5486_, 4, v_diag_5478_);
v___x_5483_ = v_reuseFailAlloc_5486_;
goto v_reusejp_5482_;
}
v_reusejp_5482_:
{
lean_object* v___x_5484_; lean_object* v___x_5485_; 
v___x_5484_ = lean_st_ref_set(v___y_5465_, v___x_5483_);
v___x_5485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5485_, 0, v_fst_5472_);
return v___x_5485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg___boxed(lean_object* v_e_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_){
_start:
{
lean_object* v_res_5492_; 
v_res_5492_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg(v_e_5489_, v___y_5490_);
lean_dec(v___y_5490_);
return v_res_5492_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1(lean_object* v_e_5493_, lean_object* v___y_5494_, lean_object* v___y_5495_, lean_object* v___y_5496_, lean_object* v___y_5497_, lean_object* v___y_5498_, lean_object* v___y_5499_){
_start:
{
lean_object* v___x_5501_; 
v___x_5501_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg(v_e_5493_, v___y_5497_);
return v___x_5501_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___boxed(lean_object* v_e_5502_, lean_object* v___y_5503_, lean_object* v___y_5504_, lean_object* v___y_5505_, lean_object* v___y_5506_, lean_object* v___y_5507_, lean_object* v___y_5508_, lean_object* v___y_5509_){
_start:
{
lean_object* v_res_5510_; 
v_res_5510_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1(v_e_5502_, v___y_5503_, v___y_5504_, v___y_5505_, v___y_5506_, v___y_5507_, v___y_5508_);
lean_dec(v___y_5508_);
lean_dec_ref(v___y_5507_);
lean_dec(v___y_5506_);
lean_dec_ref(v___y_5505_);
lean_dec(v___y_5504_);
lean_dec_ref(v___y_5503_);
return v_res_5510_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__2(void){
_start:
{
lean_object* v___x_5514_; lean_object* v___x_5515_; 
v___x_5514_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__1));
v___x_5515_ = l_Lean_MessageData_ofFormat(v___x_5514_);
return v___x_5515_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5516_; lean_object* v___x_5517_; 
v___x_5516_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__2, &l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__2);
v___x_5517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5517_, 0, v___x_5516_);
return v___x_5517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0(uint8_t v___x_5518_, lean_object* v___x_5519_, lean_object* v_expectedType_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_, lean_object* v___y_5524_, lean_object* v___y_5525_, lean_object* v___y_5526_){
_start:
{
lean_object* v___y_5529_; lean_object* v___y_5530_; lean_object* v___y_5531_; lean_object* v___y_5532_; lean_object* v___y_5533_; lean_object* v___y_5534_; lean_object* v___y_5535_; lean_object* v___y_5558_; lean_object* v___y_5559_; lean_object* v___y_5560_; lean_object* v___y_5561_; lean_object* v___y_5562_; lean_object* v___y_5563_; lean_object* v___y_5564_; lean_object* v___y_5565_; lean_object* v___y_5566_; lean_object* v___y_5601_; lean_object* v___y_5602_; lean_object* v___y_5603_; lean_object* v___y_5604_; lean_object* v___y_5605_; lean_object* v___y_5606_; lean_object* v___x_5651_; lean_object* v_a_5652_; uint8_t v___x_5653_; 
lean_inc_ref(v_expectedType_5520_);
v___x_5651_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg(v_expectedType_5520_, v___y_5524_);
v_a_5652_ = lean_ctor_get(v___x_5651_, 0);
lean_inc(v_a_5652_);
lean_dec_ref(v___x_5651_);
v___x_5653_ = l_Lean_Expr_hasExprMVar(v_a_5652_);
lean_dec(v_a_5652_);
if (v___x_5653_ == 0)
{
v___y_5601_ = v___y_5521_;
v___y_5602_ = v___y_5522_;
v___y_5603_ = v___y_5523_;
v___y_5604_ = v___y_5524_;
v___y_5605_ = v___y_5525_;
v___y_5606_ = v___y_5526_;
goto v___jp_5600_;
}
else
{
lean_object* v___x_5654_; 
v___x_5654_ = l_Lean_Elab_Term_tryPostpone(v___y_5521_, v___y_5522_, v___y_5523_, v___y_5524_, v___y_5525_, v___y_5526_);
if (lean_obj_tag(v___x_5654_) == 0)
{
lean_dec_ref(v___x_5654_);
v___y_5601_ = v___y_5521_;
v___y_5602_ = v___y_5522_;
v___y_5603_ = v___y_5523_;
v___y_5604_ = v___y_5524_;
v___y_5605_ = v___y_5525_;
v___y_5606_ = v___y_5526_;
goto v___jp_5600_;
}
else
{
lean_object* v_a_5655_; lean_object* v___x_5657_; uint8_t v_isShared_5658_; uint8_t v_isSharedCheck_5662_; 
lean_dec_ref(v_expectedType_5520_);
lean_dec(v___x_5519_);
v_a_5655_ = lean_ctor_get(v___x_5654_, 0);
v_isSharedCheck_5662_ = !lean_is_exclusive(v___x_5654_);
if (v_isSharedCheck_5662_ == 0)
{
v___x_5657_ = v___x_5654_;
v_isShared_5658_ = v_isSharedCheck_5662_;
goto v_resetjp_5656_;
}
else
{
lean_inc(v_a_5655_);
lean_dec(v___x_5654_);
v___x_5657_ = lean_box(0);
v_isShared_5658_ = v_isSharedCheck_5662_;
goto v_resetjp_5656_;
}
v_resetjp_5656_:
{
lean_object* v___x_5660_; 
if (v_isShared_5658_ == 0)
{
v___x_5660_ = v___x_5657_;
goto v_reusejp_5659_;
}
else
{
lean_object* v_reuseFailAlloc_5661_; 
v_reuseFailAlloc_5661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5661_, 0, v_a_5655_);
v___x_5660_ = v_reuseFailAlloc_5661_;
goto v_reusejp_5659_;
}
v_reusejp_5659_:
{
return v___x_5660_;
}
}
}
}
v___jp_5528_:
{
lean_object* v___x_5536_; 
v___x_5536_ = l_Lean_Meta_Simp_Result_mkEqSymm(v_expectedType_5520_, v___y_5530_, v___y_5532_, v___y_5533_, v___y_5534_, v___y_5535_);
if (lean_obj_tag(v___x_5536_) == 0)
{
lean_object* v_a_5537_; lean_object* v___x_5538_; 
v_a_5537_ = lean_ctor_get(v___x_5536_, 0);
lean_inc(v_a_5537_);
lean_dec_ref(v___x_5536_);
v___x_5538_ = l_Lean_Meta_Simp_Result_mkEqTrans(v___y_5529_, v_a_5537_, v___y_5532_, v___y_5533_, v___y_5534_, v___y_5535_);
if (lean_obj_tag(v___x_5538_) == 0)
{
lean_object* v_a_5539_; lean_object* v___x_5540_; 
v_a_5539_ = lean_ctor_get(v___x_5538_, 0);
lean_inc(v_a_5539_);
lean_dec_ref(v___x_5538_);
v___x_5540_ = l_Lean_Meta_Simp_Result_mkCast(v_a_5539_, v___y_5531_, v___y_5532_, v___y_5533_, v___y_5534_, v___y_5535_);
return v___x_5540_;
}
else
{
lean_object* v_a_5541_; lean_object* v___x_5543_; uint8_t v_isShared_5544_; uint8_t v_isSharedCheck_5548_; 
lean_dec_ref(v___y_5531_);
v_a_5541_ = lean_ctor_get(v___x_5538_, 0);
v_isSharedCheck_5548_ = !lean_is_exclusive(v___x_5538_);
if (v_isSharedCheck_5548_ == 0)
{
v___x_5543_ = v___x_5538_;
v_isShared_5544_ = v_isSharedCheck_5548_;
goto v_resetjp_5542_;
}
else
{
lean_inc(v_a_5541_);
lean_dec(v___x_5538_);
v___x_5543_ = lean_box(0);
v_isShared_5544_ = v_isSharedCheck_5548_;
goto v_resetjp_5542_;
}
v_resetjp_5542_:
{
lean_object* v___x_5546_; 
if (v_isShared_5544_ == 0)
{
v___x_5546_ = v___x_5543_;
goto v_reusejp_5545_;
}
else
{
lean_object* v_reuseFailAlloc_5547_; 
v_reuseFailAlloc_5547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5547_, 0, v_a_5541_);
v___x_5546_ = v_reuseFailAlloc_5547_;
goto v_reusejp_5545_;
}
v_reusejp_5545_:
{
return v___x_5546_;
}
}
}
}
else
{
lean_object* v_a_5549_; lean_object* v___x_5551_; uint8_t v_isShared_5552_; uint8_t v_isSharedCheck_5556_; 
lean_dec_ref(v___y_5531_);
lean_dec_ref(v___y_5529_);
v_a_5549_ = lean_ctor_get(v___x_5536_, 0);
v_isSharedCheck_5556_ = !lean_is_exclusive(v___x_5536_);
if (v_isSharedCheck_5556_ == 0)
{
v___x_5551_ = v___x_5536_;
v_isShared_5552_ = v_isSharedCheck_5556_;
goto v_resetjp_5550_;
}
else
{
lean_inc(v_a_5549_);
lean_dec(v___x_5536_);
v___x_5551_ = lean_box(0);
v_isShared_5552_ = v_isSharedCheck_5556_;
goto v_resetjp_5550_;
}
v_resetjp_5550_:
{
lean_object* v___x_5554_; 
if (v_isShared_5552_ == 0)
{
v___x_5554_ = v___x_5551_;
goto v_reusejp_5553_;
}
else
{
lean_object* v_reuseFailAlloc_5555_; 
v_reuseFailAlloc_5555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5555_, 0, v_a_5549_);
v___x_5554_ = v_reuseFailAlloc_5555_;
goto v_reusejp_5553_;
}
v_reusejp_5553_:
{
return v___x_5554_;
}
}
}
}
v___jp_5557_:
{
lean_object* v___x_5567_; 
v___x_5567_ = l_Lean_Elab_Tactic_NormCast_derive(v___y_5558_, v___y_5561_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_);
if (lean_obj_tag(v___x_5567_) == 0)
{
lean_object* v_a_5568_; lean_object* v_expr_5569_; lean_object* v___x_5570_; 
v_a_5568_ = lean_ctor_get(v___x_5567_, 0);
lean_inc(v_a_5568_);
lean_dec_ref(v___x_5567_);
v_expr_5569_ = lean_ctor_get(v_a_5568_, 0);
lean_inc_ref(v___y_5562_);
lean_inc_ref(v_expr_5569_);
v___x_5570_ = l_Lean_Meta_isExprDefEq(v_expr_5569_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_);
if (lean_obj_tag(v___x_5570_) == 0)
{
lean_object* v_a_5571_; uint8_t v___x_5572_; 
v_a_5571_ = lean_ctor_get(v___x_5570_, 0);
lean_inc(v_a_5571_);
lean_dec_ref(v___x_5570_);
v___x_5572_ = lean_unbox(v_a_5571_);
lean_dec(v_a_5571_);
if (v___x_5572_ == 0)
{
lean_object* v___x_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; 
v___x_5573_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__3, &l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__3);
v___x_5574_ = lean_box(0);
lean_inc_ref(v___y_5560_);
lean_inc_ref(v_expr_5569_);
v___x_5575_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_5573_, v___y_5562_, v_expr_5569_, v___y_5560_, v___x_5574_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_);
if (lean_obj_tag(v___x_5575_) == 0)
{
lean_dec_ref(v___x_5575_);
v___y_5529_ = v_a_5568_;
v___y_5530_ = v___y_5559_;
v___y_5531_ = v___y_5560_;
v___y_5532_ = v___y_5563_;
v___y_5533_ = v___y_5564_;
v___y_5534_ = v___y_5565_;
v___y_5535_ = v___y_5566_;
goto v___jp_5528_;
}
else
{
lean_object* v_a_5576_; lean_object* v___x_5578_; uint8_t v_isShared_5579_; uint8_t v_isSharedCheck_5583_; 
lean_dec(v_a_5568_);
lean_dec_ref(v___y_5560_);
lean_dec_ref(v___y_5559_);
lean_dec_ref(v_expectedType_5520_);
v_a_5576_ = lean_ctor_get(v___x_5575_, 0);
v_isSharedCheck_5583_ = !lean_is_exclusive(v___x_5575_);
if (v_isSharedCheck_5583_ == 0)
{
v___x_5578_ = v___x_5575_;
v_isShared_5579_ = v_isSharedCheck_5583_;
goto v_resetjp_5577_;
}
else
{
lean_inc(v_a_5576_);
lean_dec(v___x_5575_);
v___x_5578_ = lean_box(0);
v_isShared_5579_ = v_isSharedCheck_5583_;
goto v_resetjp_5577_;
}
v_resetjp_5577_:
{
lean_object* v___x_5581_; 
if (v_isShared_5579_ == 0)
{
v___x_5581_ = v___x_5578_;
goto v_reusejp_5580_;
}
else
{
lean_object* v_reuseFailAlloc_5582_; 
v_reuseFailAlloc_5582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5582_, 0, v_a_5576_);
v___x_5581_ = v_reuseFailAlloc_5582_;
goto v_reusejp_5580_;
}
v_reusejp_5580_:
{
return v___x_5581_;
}
}
}
}
else
{
lean_dec_ref(v___y_5562_);
v___y_5529_ = v_a_5568_;
v___y_5530_ = v___y_5559_;
v___y_5531_ = v___y_5560_;
v___y_5532_ = v___y_5563_;
v___y_5533_ = v___y_5564_;
v___y_5534_ = v___y_5565_;
v___y_5535_ = v___y_5566_;
goto v___jp_5528_;
}
}
else
{
lean_object* v_a_5584_; lean_object* v___x_5586_; uint8_t v_isShared_5587_; uint8_t v_isSharedCheck_5591_; 
lean_dec(v_a_5568_);
lean_dec_ref(v___y_5562_);
lean_dec_ref(v___y_5560_);
lean_dec_ref(v___y_5559_);
lean_dec_ref(v_expectedType_5520_);
v_a_5584_ = lean_ctor_get(v___x_5570_, 0);
v_isSharedCheck_5591_ = !lean_is_exclusive(v___x_5570_);
if (v_isSharedCheck_5591_ == 0)
{
v___x_5586_ = v___x_5570_;
v_isShared_5587_ = v_isSharedCheck_5591_;
goto v_resetjp_5585_;
}
else
{
lean_inc(v_a_5584_);
lean_dec(v___x_5570_);
v___x_5586_ = lean_box(0);
v_isShared_5587_ = v_isSharedCheck_5591_;
goto v_resetjp_5585_;
}
v_resetjp_5585_:
{
lean_object* v___x_5589_; 
if (v_isShared_5587_ == 0)
{
v___x_5589_ = v___x_5586_;
goto v_reusejp_5588_;
}
else
{
lean_object* v_reuseFailAlloc_5590_; 
v_reuseFailAlloc_5590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5590_, 0, v_a_5584_);
v___x_5589_ = v_reuseFailAlloc_5590_;
goto v_reusejp_5588_;
}
v_reusejp_5588_:
{
return v___x_5589_;
}
}
}
}
else
{
lean_object* v_a_5592_; lean_object* v___x_5594_; uint8_t v_isShared_5595_; uint8_t v_isSharedCheck_5599_; 
lean_dec_ref(v___y_5562_);
lean_dec_ref(v___y_5560_);
lean_dec_ref(v___y_5559_);
lean_dec_ref(v_expectedType_5520_);
v_a_5592_ = lean_ctor_get(v___x_5567_, 0);
v_isSharedCheck_5599_ = !lean_is_exclusive(v___x_5567_);
if (v_isSharedCheck_5599_ == 0)
{
v___x_5594_ = v___x_5567_;
v_isShared_5595_ = v_isSharedCheck_5599_;
goto v_resetjp_5593_;
}
else
{
lean_inc(v_a_5592_);
lean_dec(v___x_5567_);
v___x_5594_ = lean_box(0);
v_isShared_5595_ = v_isSharedCheck_5599_;
goto v_resetjp_5593_;
}
v_resetjp_5593_:
{
lean_object* v___x_5597_; 
if (v_isShared_5595_ == 0)
{
v___x_5597_ = v___x_5594_;
goto v_reusejp_5596_;
}
else
{
lean_object* v_reuseFailAlloc_5598_; 
v_reuseFailAlloc_5598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5598_, 0, v_a_5592_);
v___x_5597_ = v_reuseFailAlloc_5598_;
goto v_reusejp_5596_;
}
v_reusejp_5596_:
{
return v___x_5597_;
}
}
}
}
v___jp_5600_:
{
lean_object* v___x_5607_; lean_object* v___x_5608_; uint8_t v___x_5609_; uint8_t v___x_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v___x_5613_; 
v___x_5607_ = lean_unsigned_to_nat(100000u);
v___x_5608_ = lean_unsigned_to_nat(2u);
v___x_5609_ = 0;
v___x_5610_ = 0;
v___x_5611_ = lean_box(0);
v___x_5612_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_5612_, 0, v___x_5607_);
lean_ctor_set(v___x_5612_, 1, v___x_5608_);
lean_ctor_set(v___x_5612_, 2, v___x_5611_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3, v___x_5609_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 1, v___x_5518_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 2, v___x_5609_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 3, v___x_5609_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 4, v___x_5609_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 5, v___x_5609_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 6, v___x_5610_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 7, v___x_5609_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 8, v___x_5609_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 9, v___x_5609_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 10, v___x_5609_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 11, v___x_5609_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 12, v___x_5518_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 13, v___x_5518_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 14, v___x_5609_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 15, v___x_5609_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 16, v___x_5609_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 17, v___x_5518_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 18, v___x_5518_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 19, v___x_5518_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 20, v___x_5518_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 21, v___x_5518_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 22, v___x_5518_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 23, v___x_5518_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 24, v___x_5518_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 25, v___x_5518_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 26, v___x_5609_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 27, v___x_5609_);
lean_ctor_set_uint8(v___x_5612_, sizeof(void*)*3 + 28, v___x_5609_);
lean_inc_ref(v___x_5612_);
lean_inc_ref(v_expectedType_5520_);
v___x_5613_ = l_Lean_Elab_Tactic_NormCast_derive(v_expectedType_5520_, v___x_5612_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_);
if (lean_obj_tag(v___x_5613_) == 0)
{
lean_object* v_a_5614_; lean_object* v_expr_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; 
v_a_5614_ = lean_ctor_get(v___x_5613_, 0);
lean_inc(v_a_5614_);
lean_dec_ref(v___x_5613_);
v_expr_5615_ = lean_ctor_get(v_a_5614_, 0);
lean_inc_ref(v_expr_5615_);
lean_inc_ref(v_expr_5615_);
v___x_5616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5616_, 0, v_expr_5615_);
v___x_5617_ = l_Lean_Elab_Term_elabTerm(v___x_5519_, v___x_5616_, v___x_5518_, v___x_5518_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_);
if (lean_obj_tag(v___x_5617_) == 0)
{
lean_object* v_a_5618_; uint8_t v___x_5619_; lean_object* v___x_5620_; 
v_a_5618_ = lean_ctor_get(v___x_5617_, 0);
lean_inc(v_a_5618_);
lean_dec_ref(v___x_5617_);
v___x_5619_ = 0;
v___x_5620_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_5619_, v___x_5609_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_);
if (lean_obj_tag(v___x_5620_) == 0)
{
lean_object* v___x_5621_; 
lean_dec_ref(v___x_5620_);
lean_inc(v___y_5606_);
lean_inc_ref(v___y_5605_);
lean_inc(v___y_5604_);
lean_inc_ref(v___y_5603_);
lean_inc(v_a_5618_);
v___x_5621_ = lean_infer_type(v_a_5618_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_);
if (lean_obj_tag(v___x_5621_) == 0)
{
lean_object* v_a_5622_; lean_object* v___x_5623_; lean_object* v_a_5624_; uint8_t v___x_5625_; 
v_a_5622_ = lean_ctor_get(v___x_5621_, 0);
lean_inc(v_a_5622_);
lean_dec_ref(v___x_5621_);
v___x_5623_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg(v_a_5622_, v___y_5604_);
v_a_5624_ = lean_ctor_get(v___x_5623_, 0);
lean_inc(v_a_5624_);
lean_dec_ref(v___x_5623_);
v___x_5625_ = l_Lean_Expr_hasExprMVar(v_a_5624_);
if (v___x_5625_ == 0)
{
v___y_5558_ = v_a_5624_;
v___y_5559_ = v_a_5614_;
v___y_5560_ = v_a_5618_;
v___y_5561_ = v___x_5612_;
v___y_5562_ = v_expr_5615_;
v___y_5563_ = v___y_5603_;
v___y_5564_ = v___y_5604_;
v___y_5565_ = v___y_5605_;
v___y_5566_ = v___y_5606_;
goto v___jp_5557_;
}
else
{
lean_object* v___x_5626_; 
v___x_5626_ = l_Lean_Elab_Term_tryPostpone(v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_);
if (lean_obj_tag(v___x_5626_) == 0)
{
lean_dec_ref(v___x_5626_);
v___y_5558_ = v_a_5624_;
v___y_5559_ = v_a_5614_;
v___y_5560_ = v_a_5618_;
v___y_5561_ = v___x_5612_;
v___y_5562_ = v_expr_5615_;
v___y_5563_ = v___y_5603_;
v___y_5564_ = v___y_5604_;
v___y_5565_ = v___y_5605_;
v___y_5566_ = v___y_5606_;
goto v___jp_5557_;
}
else
{
lean_object* v_a_5627_; lean_object* v___x_5629_; uint8_t v_isShared_5630_; uint8_t v_isSharedCheck_5634_; 
lean_dec(v_a_5624_);
lean_dec(v_a_5618_);
lean_dec_ref(v_expr_5615_);
lean_dec(v_a_5614_);
lean_dec_ref(v___x_5612_);
lean_dec_ref(v_expectedType_5520_);
v_a_5627_ = lean_ctor_get(v___x_5626_, 0);
v_isSharedCheck_5634_ = !lean_is_exclusive(v___x_5626_);
if (v_isSharedCheck_5634_ == 0)
{
v___x_5629_ = v___x_5626_;
v_isShared_5630_ = v_isSharedCheck_5634_;
goto v_resetjp_5628_;
}
else
{
lean_inc(v_a_5627_);
lean_dec(v___x_5626_);
v___x_5629_ = lean_box(0);
v_isShared_5630_ = v_isSharedCheck_5634_;
goto v_resetjp_5628_;
}
v_resetjp_5628_:
{
lean_object* v___x_5632_; 
if (v_isShared_5630_ == 0)
{
v___x_5632_ = v___x_5629_;
goto v_reusejp_5631_;
}
else
{
lean_object* v_reuseFailAlloc_5633_; 
v_reuseFailAlloc_5633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5633_, 0, v_a_5627_);
v___x_5632_ = v_reuseFailAlloc_5633_;
goto v_reusejp_5631_;
}
v_reusejp_5631_:
{
return v___x_5632_;
}
}
}
}
}
else
{
lean_dec(v_a_5618_);
lean_dec_ref(v_expr_5615_);
lean_dec(v_a_5614_);
lean_dec_ref(v___x_5612_);
lean_dec_ref(v_expectedType_5520_);
return v___x_5621_;
}
}
else
{
lean_object* v_a_5635_; lean_object* v___x_5637_; uint8_t v_isShared_5638_; uint8_t v_isSharedCheck_5642_; 
lean_dec(v_a_5618_);
lean_dec_ref(v_expr_5615_);
lean_dec(v_a_5614_);
lean_dec_ref(v___x_5612_);
lean_dec_ref(v_expectedType_5520_);
v_a_5635_ = lean_ctor_get(v___x_5620_, 0);
v_isSharedCheck_5642_ = !lean_is_exclusive(v___x_5620_);
if (v_isSharedCheck_5642_ == 0)
{
v___x_5637_ = v___x_5620_;
v_isShared_5638_ = v_isSharedCheck_5642_;
goto v_resetjp_5636_;
}
else
{
lean_inc(v_a_5635_);
lean_dec(v___x_5620_);
v___x_5637_ = lean_box(0);
v_isShared_5638_ = v_isSharedCheck_5642_;
goto v_resetjp_5636_;
}
v_resetjp_5636_:
{
lean_object* v___x_5640_; 
if (v_isShared_5638_ == 0)
{
v___x_5640_ = v___x_5637_;
goto v_reusejp_5639_;
}
else
{
lean_object* v_reuseFailAlloc_5641_; 
v_reuseFailAlloc_5641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5641_, 0, v_a_5635_);
v___x_5640_ = v_reuseFailAlloc_5641_;
goto v_reusejp_5639_;
}
v_reusejp_5639_:
{
return v___x_5640_;
}
}
}
}
else
{
lean_dec_ref(v_expr_5615_);
lean_dec(v_a_5614_);
lean_dec_ref(v___x_5612_);
lean_dec_ref(v_expectedType_5520_);
return v___x_5617_;
}
}
else
{
lean_object* v_a_5643_; lean_object* v___x_5645_; uint8_t v_isShared_5646_; uint8_t v_isSharedCheck_5650_; 
lean_dec_ref(v___x_5612_);
lean_dec_ref(v_expectedType_5520_);
lean_dec(v___x_5519_);
v_a_5643_ = lean_ctor_get(v___x_5613_, 0);
v_isSharedCheck_5650_ = !lean_is_exclusive(v___x_5613_);
if (v_isSharedCheck_5650_ == 0)
{
v___x_5645_ = v___x_5613_;
v_isShared_5646_ = v_isSharedCheck_5650_;
goto v_resetjp_5644_;
}
else
{
lean_inc(v_a_5643_);
lean_dec(v___x_5613_);
v___x_5645_ = lean_box(0);
v_isShared_5646_ = v_isSharedCheck_5650_;
goto v_resetjp_5644_;
}
v_resetjp_5644_:
{
lean_object* v___x_5648_; 
if (v_isShared_5646_ == 0)
{
v___x_5648_ = v___x_5645_;
goto v_reusejp_5647_;
}
else
{
lean_object* v_reuseFailAlloc_5649_; 
v_reuseFailAlloc_5649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5649_, 0, v_a_5643_);
v___x_5648_ = v_reuseFailAlloc_5649_;
goto v_reusejp_5647_;
}
v_reusejp_5647_:
{
return v___x_5648_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___boxed(lean_object* v___x_5663_, lean_object* v___x_5664_, lean_object* v_expectedType_5665_, lean_object* v___y_5666_, lean_object* v___y_5667_, lean_object* v___y_5668_, lean_object* v___y_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_){
_start:
{
uint8_t v___x_4150__boxed_5673_; lean_object* v_res_5674_; 
v___x_4150__boxed_5673_ = lean_unbox(v___x_5663_);
v_res_5674_ = l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0(v___x_4150__boxed_5673_, v___x_5664_, v_expectedType_5665_, v___y_5666_, v___y_5667_, v___y_5668_, v___y_5669_, v___y_5670_, v___y_5671_);
lean_dec(v___y_5671_);
lean_dec_ref(v___y_5670_);
lean_dec(v___y_5669_);
lean_dec_ref(v___y_5668_);
lean_dec(v___y_5667_);
lean_dec_ref(v___y_5666_);
return v_res_5674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast(lean_object* v_stx_5679_, lean_object* v_expectedType_x3f_5680_, lean_object* v_a_5681_, lean_object* v_a_5682_, lean_object* v_a_5683_, lean_object* v_a_5684_, lean_object* v_a_5685_, lean_object* v_a_5686_){
_start:
{
lean_object* v___x_5688_; uint8_t v___x_5689_; 
v___x_5688_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabModCast___closed__1));
lean_inc(v_stx_5679_);
v___x_5689_ = l_Lean_Syntax_isOfKind(v_stx_5679_, v___x_5688_);
if (v___x_5689_ == 0)
{
lean_object* v___x_5690_; 
lean_dec(v_expectedType_x3f_5680_);
lean_dec(v_stx_5679_);
v___x_5690_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg();
return v___x_5690_;
}
else
{
lean_object* v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; lean_object* v___f_5694_; lean_object* v___x_5695_; 
v___x_5691_ = lean_unsigned_to_nat(1u);
v___x_5692_ = l_Lean_Syntax_getArg(v_stx_5679_, v___x_5691_);
lean_dec(v_stx_5679_);
v___x_5693_ = lean_box(v___x_5689_);
v___f_5694_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___boxed), 10, 2);
lean_closure_set(v___f_5694_, 0, v___x_5693_);
lean_closure_set(v___f_5694_, 1, v___x_5692_);
v___x_5695_ = l_Lean_Elab_Term_withExpectedType(v_expectedType_x3f_5680_, v___f_5694_, v_a_5681_, v_a_5682_, v_a_5683_, v_a_5684_, v_a_5685_, v_a_5686_);
return v___x_5695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___boxed(lean_object* v_stx_5696_, lean_object* v_expectedType_x3f_5697_, lean_object* v_a_5698_, lean_object* v_a_5699_, lean_object* v_a_5700_, lean_object* v_a_5701_, lean_object* v_a_5702_, lean_object* v_a_5703_, lean_object* v_a_5704_){
_start:
{
lean_object* v_res_5705_; 
v_res_5705_ = l_Lean_Elab_Tactic_NormCast_elabModCast(v_stx_5696_, v_expectedType_x3f_5697_, v_a_5698_, v_a_5699_, v_a_5700_, v_a_5701_, v_a_5702_, v_a_5703_);
lean_dec(v_a_5703_);
lean_dec_ref(v_a_5702_);
lean_dec(v_a_5701_);
lean_dec_ref(v_a_5700_);
lean_dec(v_a_5699_);
lean_dec_ref(v_a_5698_);
return v_res_5705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1(){
_start:
{
lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5716_; lean_object* v___x_5717_; lean_object* v___x_5718_; 
v___x_5714_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5715_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabModCast___closed__1));
v___x_5716_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1));
v___x_5717_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_elabModCast___boxed), 9, 0);
v___x_5718_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5714_, v___x_5715_, v___x_5716_, v___x_5717_);
return v___x_5718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___boxed(lean_object* v_a_5719_){
_start:
{
lean_object* v_res_5720_; 
v_res_5720_ = l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1();
return v_res_5720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3(){
_start:
{
lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; 
v___x_5747_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1));
v___x_5748_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__6));
v___x_5749_ = l_Lean_addBuiltinDeclarationRanges(v___x_5747_, v___x_5748_);
return v___x_5749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___boxed(lean_object* v_a_5750_){
_start:
{
lean_object* v_res_5751_; 
v_res_5751_ = l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3();
return v_res_5751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___lam__0(lean_object* v_cfg_5752_, lean_object* v___y_5753_, lean_object* v___y_5754_, lean_object* v___y_5755_, lean_object* v___y_5756_, lean_object* v___y_5757_, lean_object* v___y_5758_, lean_object* v___y_5759_, lean_object* v___y_5760_){
_start:
{
lean_object* v___x_5762_; 
v___x_5762_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_5754_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_);
if (lean_obj_tag(v___x_5762_) == 0)
{
lean_object* v_a_5763_; lean_object* v___x_5764_; 
v_a_5763_ = lean_ctor_get(v___x_5762_, 0);
lean_inc(v_a_5763_);
lean_dec_ref(v___x_5762_);
lean_inc(v_a_5763_);
v___x_5764_ = l_Lean_MVarId_getType(v_a_5763_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_);
if (lean_obj_tag(v___x_5764_) == 0)
{
lean_object* v_a_5765_; lean_object* v___x_5766_; lean_object* v_a_5767_; lean_object* v___x_5768_; 
v_a_5765_ = lean_ctor_get(v___x_5764_, 0);
lean_inc(v_a_5765_);
lean_dec_ref(v___x_5764_);
v___x_5766_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_a_5765_, v___y_5758_);
v_a_5767_ = lean_ctor_get(v___x_5766_, 0);
lean_inc(v_a_5767_);
lean_dec_ref(v___x_5766_);
lean_inc(v_a_5767_);
v___x_5768_ = l_Lean_Elab_Tactic_NormCast_derive(v_a_5767_, v_cfg_5752_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_);
if (lean_obj_tag(v___x_5768_) == 0)
{
lean_object* v_a_5769_; lean_object* v___x_5770_; 
v_a_5769_ = lean_ctor_get(v___x_5768_, 0);
lean_inc(v_a_5769_);
lean_dec_ref(v___x_5768_);
v___x_5770_ = l_Lean_Meta_applySimpResultToTarget(v_a_5763_, v_a_5767_, v_a_5769_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_);
lean_dec(v_a_5767_);
if (lean_obj_tag(v___x_5770_) == 0)
{
lean_object* v_a_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; lean_object* v___x_5774_; 
v_a_5771_ = lean_ctor_get(v___x_5770_, 0);
lean_inc(v_a_5771_);
lean_dec_ref(v___x_5770_);
v___x_5772_ = lean_box(0);
v___x_5773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5773_, 0, v_a_5771_);
lean_ctor_set(v___x_5773_, 1, v___x_5772_);
v___x_5774_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_5773_, v___y_5754_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_);
return v___x_5774_;
}
else
{
lean_object* v_a_5775_; lean_object* v___x_5777_; uint8_t v_isShared_5778_; uint8_t v_isSharedCheck_5782_; 
v_a_5775_ = lean_ctor_get(v___x_5770_, 0);
v_isSharedCheck_5782_ = !lean_is_exclusive(v___x_5770_);
if (v_isSharedCheck_5782_ == 0)
{
v___x_5777_ = v___x_5770_;
v_isShared_5778_ = v_isSharedCheck_5782_;
goto v_resetjp_5776_;
}
else
{
lean_inc(v_a_5775_);
lean_dec(v___x_5770_);
v___x_5777_ = lean_box(0);
v_isShared_5778_ = v_isSharedCheck_5782_;
goto v_resetjp_5776_;
}
v_resetjp_5776_:
{
lean_object* v___x_5780_; 
if (v_isShared_5778_ == 0)
{
v___x_5780_ = v___x_5777_;
goto v_reusejp_5779_;
}
else
{
lean_object* v_reuseFailAlloc_5781_; 
v_reuseFailAlloc_5781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5781_, 0, v_a_5775_);
v___x_5780_ = v_reuseFailAlloc_5781_;
goto v_reusejp_5779_;
}
v_reusejp_5779_:
{
return v___x_5780_;
}
}
}
}
else
{
lean_object* v_a_5783_; lean_object* v___x_5785_; uint8_t v_isShared_5786_; uint8_t v_isSharedCheck_5790_; 
lean_dec(v_a_5767_);
lean_dec(v_a_5763_);
v_a_5783_ = lean_ctor_get(v___x_5768_, 0);
v_isSharedCheck_5790_ = !lean_is_exclusive(v___x_5768_);
if (v_isSharedCheck_5790_ == 0)
{
v___x_5785_ = v___x_5768_;
v_isShared_5786_ = v_isSharedCheck_5790_;
goto v_resetjp_5784_;
}
else
{
lean_inc(v_a_5783_);
lean_dec(v___x_5768_);
v___x_5785_ = lean_box(0);
v_isShared_5786_ = v_isSharedCheck_5790_;
goto v_resetjp_5784_;
}
v_resetjp_5784_:
{
lean_object* v___x_5788_; 
if (v_isShared_5786_ == 0)
{
v___x_5788_ = v___x_5785_;
goto v_reusejp_5787_;
}
else
{
lean_object* v_reuseFailAlloc_5789_; 
v_reuseFailAlloc_5789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5789_, 0, v_a_5783_);
v___x_5788_ = v_reuseFailAlloc_5789_;
goto v_reusejp_5787_;
}
v_reusejp_5787_:
{
return v___x_5788_;
}
}
}
}
else
{
lean_object* v_a_5791_; lean_object* v___x_5793_; uint8_t v_isShared_5794_; uint8_t v_isSharedCheck_5798_; 
lean_dec(v_a_5763_);
lean_dec_ref(v_cfg_5752_);
v_a_5791_ = lean_ctor_get(v___x_5764_, 0);
v_isSharedCheck_5798_ = !lean_is_exclusive(v___x_5764_);
if (v_isSharedCheck_5798_ == 0)
{
v___x_5793_ = v___x_5764_;
v_isShared_5794_ = v_isSharedCheck_5798_;
goto v_resetjp_5792_;
}
else
{
lean_inc(v_a_5791_);
lean_dec(v___x_5764_);
v___x_5793_ = lean_box(0);
v_isShared_5794_ = v_isSharedCheck_5798_;
goto v_resetjp_5792_;
}
v_resetjp_5792_:
{
lean_object* v___x_5796_; 
if (v_isShared_5794_ == 0)
{
v___x_5796_ = v___x_5793_;
goto v_reusejp_5795_;
}
else
{
lean_object* v_reuseFailAlloc_5797_; 
v_reuseFailAlloc_5797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5797_, 0, v_a_5791_);
v___x_5796_ = v_reuseFailAlloc_5797_;
goto v_reusejp_5795_;
}
v_reusejp_5795_:
{
return v___x_5796_;
}
}
}
}
else
{
lean_object* v_a_5799_; lean_object* v___x_5801_; uint8_t v_isShared_5802_; uint8_t v_isSharedCheck_5806_; 
lean_dec_ref(v_cfg_5752_);
v_a_5799_ = lean_ctor_get(v___x_5762_, 0);
v_isSharedCheck_5806_ = !lean_is_exclusive(v___x_5762_);
if (v_isSharedCheck_5806_ == 0)
{
v___x_5801_ = v___x_5762_;
v_isShared_5802_ = v_isSharedCheck_5806_;
goto v_resetjp_5800_;
}
else
{
lean_inc(v_a_5799_);
lean_dec(v___x_5762_);
v___x_5801_ = lean_box(0);
v_isShared_5802_ = v_isSharedCheck_5806_;
goto v_resetjp_5800_;
}
v_resetjp_5800_:
{
lean_object* v___x_5804_; 
if (v_isShared_5802_ == 0)
{
v___x_5804_ = v___x_5801_;
goto v_reusejp_5803_;
}
else
{
lean_object* v_reuseFailAlloc_5805_; 
v_reuseFailAlloc_5805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5805_, 0, v_a_5799_);
v___x_5804_ = v_reuseFailAlloc_5805_;
goto v_reusejp_5803_;
}
v_reusejp_5803_:
{
return v___x_5804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___lam__0___boxed(lean_object* v_cfg_5807_, lean_object* v___y_5808_, lean_object* v___y_5809_, lean_object* v___y_5810_, lean_object* v___y_5811_, lean_object* v___y_5812_, lean_object* v___y_5813_, lean_object* v___y_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_){
_start:
{
lean_object* v_res_5817_; 
v_res_5817_ = l_Lean_Elab_Tactic_NormCast_normCastTarget___lam__0(v_cfg_5807_, v___y_5808_, v___y_5809_, v___y_5810_, v___y_5811_, v___y_5812_, v___y_5813_, v___y_5814_, v___y_5815_);
lean_dec(v___y_5815_);
lean_dec_ref(v___y_5814_);
lean_dec(v___y_5813_);
lean_dec_ref(v___y_5812_);
lean_dec(v___y_5811_);
lean_dec_ref(v___y_5810_);
lean_dec(v___y_5809_);
lean_dec_ref(v___y_5808_);
return v_res_5817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget(lean_object* v_cfg_5818_, lean_object* v_a_5819_, lean_object* v_a_5820_, lean_object* v_a_5821_, lean_object* v_a_5822_, lean_object* v_a_5823_, lean_object* v_a_5824_, lean_object* v_a_5825_, lean_object* v_a_5826_){
_start:
{
lean_object* v___f_5828_; lean_object* v___x_5829_; 
v___f_5828_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_normCastTarget___lam__0___boxed), 10, 1);
lean_closure_set(v___f_5828_, 0, v_cfg_5818_);
v___x_5829_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_5828_, v_a_5819_, v_a_5820_, v_a_5821_, v_a_5822_, v_a_5823_, v_a_5824_, v_a_5825_, v_a_5826_);
return v___x_5829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___boxed(lean_object* v_cfg_5830_, lean_object* v_a_5831_, lean_object* v_a_5832_, lean_object* v_a_5833_, lean_object* v_a_5834_, lean_object* v_a_5835_, lean_object* v_a_5836_, lean_object* v_a_5837_, lean_object* v_a_5838_, lean_object* v_a_5839_){
_start:
{
lean_object* v_res_5840_; 
v_res_5840_ = l_Lean_Elab_Tactic_NormCast_normCastTarget(v_cfg_5830_, v_a_5831_, v_a_5832_, v_a_5833_, v_a_5834_, v_a_5835_, v_a_5836_, v_a_5837_, v_a_5838_);
lean_dec(v_a_5838_);
lean_dec_ref(v_a_5837_);
lean_dec(v_a_5836_);
lean_dec_ref(v_a_5835_);
lean_dec(v_a_5834_);
lean_dec_ref(v_a_5833_);
lean_dec(v_a_5832_);
lean_dec_ref(v_a_5831_);
return v_res_5840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp___lam__0(lean_object* v_fvarId_5841_, lean_object* v_cfg_5842_, lean_object* v___y_5843_, lean_object* v___y_5844_, lean_object* v___y_5845_, lean_object* v___y_5846_, lean_object* v___y_5847_, lean_object* v___y_5848_, lean_object* v___y_5849_, lean_object* v___y_5850_){
_start:
{
lean_object* v___x_5852_; 
v___x_5852_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_5844_, v___y_5847_, v___y_5848_, v___y_5849_, v___y_5850_);
if (lean_obj_tag(v___x_5852_) == 0)
{
lean_object* v_a_5853_; lean_object* v___x_5854_; 
v_a_5853_ = lean_ctor_get(v___x_5852_, 0);
lean_inc(v_a_5853_);
lean_dec_ref(v___x_5852_);
lean_inc_ref(v___y_5847_);
lean_inc(v_fvarId_5841_);
v___x_5854_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_5841_, v___y_5847_, v___y_5849_, v___y_5850_);
if (lean_obj_tag(v___x_5854_) == 0)
{
lean_object* v_a_5855_; lean_object* v___x_5856_; lean_object* v___x_5857_; lean_object* v_a_5858_; lean_object* v___x_5859_; 
v_a_5855_ = lean_ctor_get(v___x_5854_, 0);
lean_inc(v_a_5855_);
lean_dec_ref(v___x_5854_);
v___x_5856_ = l_Lean_LocalDecl_type(v_a_5855_);
lean_dec(v_a_5855_);
v___x_5857_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v___x_5856_, v___y_5848_);
v_a_5858_ = lean_ctor_get(v___x_5857_, 0);
lean_inc(v_a_5858_);
lean_dec_ref(v___x_5857_);
v___x_5859_ = l_Lean_Elab_Tactic_NormCast_derive(v_a_5858_, v_cfg_5842_, v___y_5847_, v___y_5848_, v___y_5849_, v___y_5850_);
if (lean_obj_tag(v___x_5859_) == 0)
{
lean_object* v_a_5860_; uint8_t v___x_5861_; lean_object* v___x_5862_; 
v_a_5860_ = lean_ctor_get(v___x_5859_, 0);
lean_inc(v_a_5860_);
lean_dec_ref(v___x_5859_);
v___x_5861_ = 0;
v___x_5862_ = l_Lean_Meta_applySimpResultToLocalDecl(v_a_5853_, v_fvarId_5841_, v_a_5860_, v___x_5861_, v___y_5847_, v___y_5848_, v___y_5849_, v___y_5850_);
if (lean_obj_tag(v___x_5862_) == 0)
{
lean_object* v_a_5863_; 
v_a_5863_ = lean_ctor_get(v___x_5862_, 0);
lean_inc(v_a_5863_);
lean_dec_ref(v___x_5862_);
if (lean_obj_tag(v_a_5863_) == 0)
{
lean_object* v___x_5864_; lean_object* v___x_5865_; 
v___x_5864_ = lean_box(0);
v___x_5865_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_5864_, v___y_5844_, v___y_5847_, v___y_5848_, v___y_5849_, v___y_5850_);
lean_dec_ref(v___y_5847_);
return v___x_5865_;
}
else
{
lean_object* v_val_5866_; lean_object* v_snd_5867_; lean_object* v___x_5869_; uint8_t v_isShared_5870_; uint8_t v_isSharedCheck_5876_; 
v_val_5866_ = lean_ctor_get(v_a_5863_, 0);
lean_inc(v_val_5866_);
lean_dec_ref(v_a_5863_);
v_snd_5867_ = lean_ctor_get(v_val_5866_, 1);
v_isSharedCheck_5876_ = !lean_is_exclusive(v_val_5866_);
if (v_isSharedCheck_5876_ == 0)
{
lean_object* v_unused_5877_; 
v_unused_5877_ = lean_ctor_get(v_val_5866_, 0);
lean_dec(v_unused_5877_);
v___x_5869_ = v_val_5866_;
v_isShared_5870_ = v_isSharedCheck_5876_;
goto v_resetjp_5868_;
}
else
{
lean_inc(v_snd_5867_);
lean_dec(v_val_5866_);
v___x_5869_ = lean_box(0);
v_isShared_5870_ = v_isSharedCheck_5876_;
goto v_resetjp_5868_;
}
v_resetjp_5868_:
{
lean_object* v___x_5871_; lean_object* v___x_5873_; 
v___x_5871_ = lean_box(0);
if (v_isShared_5870_ == 0)
{
lean_ctor_set_tag(v___x_5869_, 1);
lean_ctor_set(v___x_5869_, 1, v___x_5871_);
lean_ctor_set(v___x_5869_, 0, v_snd_5867_);
v___x_5873_ = v___x_5869_;
goto v_reusejp_5872_;
}
else
{
lean_object* v_reuseFailAlloc_5875_; 
v_reuseFailAlloc_5875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5875_, 0, v_snd_5867_);
lean_ctor_set(v_reuseFailAlloc_5875_, 1, v___x_5871_);
v___x_5873_ = v_reuseFailAlloc_5875_;
goto v_reusejp_5872_;
}
v_reusejp_5872_:
{
lean_object* v___x_5874_; 
v___x_5874_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_5873_, v___y_5844_, v___y_5847_, v___y_5848_, v___y_5849_, v___y_5850_);
lean_dec_ref(v___y_5847_);
return v___x_5874_;
}
}
}
}
else
{
lean_object* v_a_5878_; lean_object* v___x_5880_; uint8_t v_isShared_5881_; uint8_t v_isSharedCheck_5885_; 
lean_dec_ref(v___y_5847_);
v_a_5878_ = lean_ctor_get(v___x_5862_, 0);
v_isSharedCheck_5885_ = !lean_is_exclusive(v___x_5862_);
if (v_isSharedCheck_5885_ == 0)
{
v___x_5880_ = v___x_5862_;
v_isShared_5881_ = v_isSharedCheck_5885_;
goto v_resetjp_5879_;
}
else
{
lean_inc(v_a_5878_);
lean_dec(v___x_5862_);
v___x_5880_ = lean_box(0);
v_isShared_5881_ = v_isSharedCheck_5885_;
goto v_resetjp_5879_;
}
v_resetjp_5879_:
{
lean_object* v___x_5883_; 
if (v_isShared_5881_ == 0)
{
v___x_5883_ = v___x_5880_;
goto v_reusejp_5882_;
}
else
{
lean_object* v_reuseFailAlloc_5884_; 
v_reuseFailAlloc_5884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5884_, 0, v_a_5878_);
v___x_5883_ = v_reuseFailAlloc_5884_;
goto v_reusejp_5882_;
}
v_reusejp_5882_:
{
return v___x_5883_;
}
}
}
}
else
{
lean_object* v_a_5886_; lean_object* v___x_5888_; uint8_t v_isShared_5889_; uint8_t v_isSharedCheck_5893_; 
lean_dec(v_a_5853_);
lean_dec_ref(v___y_5847_);
lean_dec(v_fvarId_5841_);
v_a_5886_ = lean_ctor_get(v___x_5859_, 0);
v_isSharedCheck_5893_ = !lean_is_exclusive(v___x_5859_);
if (v_isSharedCheck_5893_ == 0)
{
v___x_5888_ = v___x_5859_;
v_isShared_5889_ = v_isSharedCheck_5893_;
goto v_resetjp_5887_;
}
else
{
lean_inc(v_a_5886_);
lean_dec(v___x_5859_);
v___x_5888_ = lean_box(0);
v_isShared_5889_ = v_isSharedCheck_5893_;
goto v_resetjp_5887_;
}
v_resetjp_5887_:
{
lean_object* v___x_5891_; 
if (v_isShared_5889_ == 0)
{
v___x_5891_ = v___x_5888_;
goto v_reusejp_5890_;
}
else
{
lean_object* v_reuseFailAlloc_5892_; 
v_reuseFailAlloc_5892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5892_, 0, v_a_5886_);
v___x_5891_ = v_reuseFailAlloc_5892_;
goto v_reusejp_5890_;
}
v_reusejp_5890_:
{
return v___x_5891_;
}
}
}
}
else
{
lean_object* v_a_5894_; lean_object* v___x_5896_; uint8_t v_isShared_5897_; uint8_t v_isSharedCheck_5901_; 
lean_dec(v_a_5853_);
lean_dec_ref(v___y_5847_);
lean_dec_ref(v_cfg_5842_);
lean_dec(v_fvarId_5841_);
v_a_5894_ = lean_ctor_get(v___x_5854_, 0);
v_isSharedCheck_5901_ = !lean_is_exclusive(v___x_5854_);
if (v_isSharedCheck_5901_ == 0)
{
v___x_5896_ = v___x_5854_;
v_isShared_5897_ = v_isSharedCheck_5901_;
goto v_resetjp_5895_;
}
else
{
lean_inc(v_a_5894_);
lean_dec(v___x_5854_);
v___x_5896_ = lean_box(0);
v_isShared_5897_ = v_isSharedCheck_5901_;
goto v_resetjp_5895_;
}
v_resetjp_5895_:
{
lean_object* v___x_5899_; 
if (v_isShared_5897_ == 0)
{
v___x_5899_ = v___x_5896_;
goto v_reusejp_5898_;
}
else
{
lean_object* v_reuseFailAlloc_5900_; 
v_reuseFailAlloc_5900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5900_, 0, v_a_5894_);
v___x_5899_ = v_reuseFailAlloc_5900_;
goto v_reusejp_5898_;
}
v_reusejp_5898_:
{
return v___x_5899_;
}
}
}
}
else
{
lean_object* v_a_5902_; lean_object* v___x_5904_; uint8_t v_isShared_5905_; uint8_t v_isSharedCheck_5909_; 
lean_dec_ref(v___y_5847_);
lean_dec_ref(v_cfg_5842_);
lean_dec(v_fvarId_5841_);
v_a_5902_ = lean_ctor_get(v___x_5852_, 0);
v_isSharedCheck_5909_ = !lean_is_exclusive(v___x_5852_);
if (v_isSharedCheck_5909_ == 0)
{
v___x_5904_ = v___x_5852_;
v_isShared_5905_ = v_isSharedCheck_5909_;
goto v_resetjp_5903_;
}
else
{
lean_inc(v_a_5902_);
lean_dec(v___x_5852_);
v___x_5904_ = lean_box(0);
v_isShared_5905_ = v_isSharedCheck_5909_;
goto v_resetjp_5903_;
}
v_resetjp_5903_:
{
lean_object* v___x_5907_; 
if (v_isShared_5905_ == 0)
{
v___x_5907_ = v___x_5904_;
goto v_reusejp_5906_;
}
else
{
lean_object* v_reuseFailAlloc_5908_; 
v_reuseFailAlloc_5908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5908_, 0, v_a_5902_);
v___x_5907_ = v_reuseFailAlloc_5908_;
goto v_reusejp_5906_;
}
v_reusejp_5906_:
{
return v___x_5907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp___lam__0___boxed(lean_object* v_fvarId_5910_, lean_object* v_cfg_5911_, lean_object* v___y_5912_, lean_object* v___y_5913_, lean_object* v___y_5914_, lean_object* v___y_5915_, lean_object* v___y_5916_, lean_object* v___y_5917_, lean_object* v___y_5918_, lean_object* v___y_5919_, lean_object* v___y_5920_){
_start:
{
lean_object* v_res_5921_; 
v_res_5921_ = l_Lean_Elab_Tactic_NormCast_normCastHyp___lam__0(v_fvarId_5910_, v_cfg_5911_, v___y_5912_, v___y_5913_, v___y_5914_, v___y_5915_, v___y_5916_, v___y_5917_, v___y_5918_, v___y_5919_);
lean_dec(v___y_5919_);
lean_dec_ref(v___y_5918_);
lean_dec(v___y_5917_);
lean_dec(v___y_5915_);
lean_dec_ref(v___y_5914_);
lean_dec(v___y_5913_);
lean_dec_ref(v___y_5912_);
return v_res_5921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp(lean_object* v_cfg_5922_, lean_object* v_fvarId_5923_, lean_object* v_a_5924_, lean_object* v_a_5925_, lean_object* v_a_5926_, lean_object* v_a_5927_, lean_object* v_a_5928_, lean_object* v_a_5929_, lean_object* v_a_5930_, lean_object* v_a_5931_){
_start:
{
lean_object* v___f_5933_; lean_object* v___x_5934_; 
v___f_5933_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_normCastHyp___lam__0___boxed), 11, 2);
lean_closure_set(v___f_5933_, 0, v_fvarId_5923_);
lean_closure_set(v___f_5933_, 1, v_cfg_5922_);
v___x_5934_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_5933_, v_a_5924_, v_a_5925_, v_a_5926_, v_a_5927_, v_a_5928_, v_a_5929_, v_a_5930_, v_a_5931_);
return v___x_5934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp___boxed(lean_object* v_cfg_5935_, lean_object* v_fvarId_5936_, lean_object* v_a_5937_, lean_object* v_a_5938_, lean_object* v_a_5939_, lean_object* v_a_5940_, lean_object* v_a_5941_, lean_object* v_a_5942_, lean_object* v_a_5943_, lean_object* v_a_5944_, lean_object* v_a_5945_){
_start:
{
lean_object* v_res_5946_; 
v_res_5946_ = l_Lean_Elab_Tactic_NormCast_normCastHyp(v_cfg_5935_, v_fvarId_5936_, v_a_5937_, v_a_5938_, v_a_5939_, v_a_5940_, v_a_5941_, v_a_5942_, v_a_5943_, v_a_5944_);
lean_dec(v_a_5944_);
lean_dec_ref(v_a_5943_);
lean_dec(v_a_5942_);
lean_dec_ref(v_a_5941_);
lean_dec(v_a_5940_);
lean_dec_ref(v_a_5939_);
lean_dec(v_a_5938_);
lean_dec_ref(v_a_5937_);
return v_res_5946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg(){
_start:
{
lean_object* v___x_5948_; lean_object* v___x_5949_; 
v___x_5948_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0);
v___x_5949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5949_, 0, v___x_5948_);
return v___x_5949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg___boxed(lean_object* v___y_5950_){
_start:
{
lean_object* v_res_5951_; 
v_res_5951_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg();
return v_res_5951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0(lean_object* v_00_u03b1_5952_, lean_object* v___y_5953_, lean_object* v___y_5954_, lean_object* v___y_5955_, lean_object* v___y_5956_, lean_object* v___y_5957_, lean_object* v___y_5958_, lean_object* v___y_5959_, lean_object* v___y_5960_){
_start:
{
lean_object* v___x_5962_; 
v___x_5962_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg();
return v___x_5962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___boxed(lean_object* v_00_u03b1_5963_, lean_object* v___y_5964_, lean_object* v___y_5965_, lean_object* v___y_5966_, lean_object* v___y_5967_, lean_object* v___y_5968_, lean_object* v___y_5969_, lean_object* v___y_5970_, lean_object* v___y_5971_, lean_object* v___y_5972_){
_start:
{
lean_object* v_res_5973_; 
v_res_5973_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0(v_00_u03b1_5963_, v___y_5964_, v___y_5965_, v___y_5966_, v___y_5967_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_);
lean_dec(v___y_5971_);
lean_dec_ref(v___y_5970_);
lean_dec(v___y_5969_);
lean_dec_ref(v___y_5968_);
lean_dec(v___y_5967_);
lean_dec_ref(v___y_5966_);
lean_dec(v___y_5965_);
lean_dec_ref(v___y_5964_);
return v_res_5973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1(lean_object* v_a_5974_, lean_object* v_as_5975_, size_t v_i_5976_, size_t v_stop_5977_, lean_object* v_b_5978_, lean_object* v___y_5979_, lean_object* v___y_5980_, lean_object* v___y_5981_, lean_object* v___y_5982_, lean_object* v___y_5983_, lean_object* v___y_5984_, lean_object* v___y_5985_, lean_object* v___y_5986_){
_start:
{
uint8_t v___x_5988_; 
v___x_5988_ = lean_usize_dec_eq(v_i_5976_, v_stop_5977_);
if (v___x_5988_ == 0)
{
lean_object* v___x_5989_; lean_object* v___x_5990_; 
v___x_5989_ = lean_array_uget_borrowed(v_as_5975_, v_i_5976_);
lean_inc(v___x_5989_);
lean_inc_ref(v_a_5974_);
v___x_5990_ = l_Lean_Elab_Tactic_NormCast_normCastHyp(v_a_5974_, v___x_5989_, v___y_5979_, v___y_5980_, v___y_5981_, v___y_5982_, v___y_5983_, v___y_5984_, v___y_5985_, v___y_5986_);
if (lean_obj_tag(v___x_5990_) == 0)
{
lean_object* v_a_5991_; size_t v___x_5992_; size_t v___x_5993_; 
v_a_5991_ = lean_ctor_get(v___x_5990_, 0);
lean_inc(v_a_5991_);
lean_dec_ref(v___x_5990_);
v___x_5992_ = ((size_t)1ULL);
v___x_5993_ = lean_usize_add(v_i_5976_, v___x_5992_);
v_i_5976_ = v___x_5993_;
v_b_5978_ = v_a_5991_;
goto _start;
}
else
{
lean_dec_ref(v_a_5974_);
return v___x_5990_;
}
}
else
{
lean_object* v___x_5995_; 
lean_dec_ref(v_a_5974_);
v___x_5995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5995_, 0, v_b_5978_);
return v___x_5995_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1___boxed(lean_object* v_a_5996_, lean_object* v_as_5997_, lean_object* v_i_5998_, lean_object* v_stop_5999_, lean_object* v_b_6000_, lean_object* v___y_6001_, lean_object* v___y_6002_, lean_object* v___y_6003_, lean_object* v___y_6004_, lean_object* v___y_6005_, lean_object* v___y_6006_, lean_object* v___y_6007_, lean_object* v___y_6008_, lean_object* v___y_6009_){
_start:
{
size_t v_i_boxed_6010_; size_t v_stop_boxed_6011_; lean_object* v_res_6012_; 
v_i_boxed_6010_ = lean_unbox_usize(v_i_5998_);
lean_dec(v_i_5998_);
v_stop_boxed_6011_ = lean_unbox_usize(v_stop_5999_);
lean_dec(v_stop_5999_);
v_res_6012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1(v_a_5996_, v_as_5997_, v_i_boxed_6010_, v_stop_boxed_6011_, v_b_6000_, v___y_6001_, v___y_6002_, v___y_6003_, v___y_6004_, v___y_6005_, v___y_6006_, v___y_6007_, v___y_6008_);
lean_dec(v___y_6008_);
lean_dec_ref(v___y_6007_);
lean_dec(v___y_6006_);
lean_dec_ref(v___y_6005_);
lean_dec(v___y_6004_);
lean_dec_ref(v___y_6003_);
lean_dec(v___y_6002_);
lean_dec_ref(v___y_6001_);
lean_dec_ref(v_as_5997_);
return v_res_6012_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lam__0(lean_object* v___y_6013_, lean_object* v_a_6014_, lean_object* v___x_6015_, lean_object* v___y_6016_, lean_object* v___y_6017_, lean_object* v___y_6018_, lean_object* v___y_6019_, lean_object* v___y_6020_, lean_object* v___y_6021_, lean_object* v___y_6022_, lean_object* v___y_6023_){
_start:
{
if (lean_obj_tag(v___y_6013_) == 0)
{
lean_object* v___x_6025_; 
lean_inc_ref(v_a_6014_);
v___x_6025_ = l_Lean_Elab_Tactic_NormCast_normCastTarget(v_a_6014_, v___y_6016_, v___y_6017_, v___y_6018_, v___y_6019_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_);
if (lean_obj_tag(v___x_6025_) == 0)
{
lean_object* v___x_6026_; 
lean_dec_ref(v___x_6025_);
v___x_6026_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6017_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_);
if (lean_obj_tag(v___x_6026_) == 0)
{
lean_object* v_a_6027_; lean_object* v___x_6028_; 
v_a_6027_ = lean_ctor_get(v___x_6026_, 0);
lean_inc(v_a_6027_);
lean_dec_ref(v___x_6026_);
v___x_6028_ = l_Lean_MVarId_getNondepPropHyps(v_a_6027_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_);
if (lean_obj_tag(v___x_6028_) == 0)
{
lean_object* v_a_6029_; lean_object* v___x_6031_; uint8_t v_isShared_6032_; uint8_t v_isSharedCheck_6049_; 
v_a_6029_ = lean_ctor_get(v___x_6028_, 0);
v_isSharedCheck_6049_ = !lean_is_exclusive(v___x_6028_);
if (v_isSharedCheck_6049_ == 0)
{
v___x_6031_ = v___x_6028_;
v_isShared_6032_ = v_isSharedCheck_6049_;
goto v_resetjp_6030_;
}
else
{
lean_inc(v_a_6029_);
lean_dec(v___x_6028_);
v___x_6031_ = lean_box(0);
v_isShared_6032_ = v_isSharedCheck_6049_;
goto v_resetjp_6030_;
}
v_resetjp_6030_:
{
lean_object* v___x_6033_; lean_object* v___x_6034_; uint8_t v___x_6035_; 
v___x_6033_ = lean_array_get_size(v_a_6029_);
v___x_6034_ = lean_box(0);
v___x_6035_ = lean_nat_dec_lt(v___x_6015_, v___x_6033_);
if (v___x_6035_ == 0)
{
lean_object* v___x_6037_; 
lean_dec(v_a_6029_);
lean_dec_ref(v_a_6014_);
if (v_isShared_6032_ == 0)
{
lean_ctor_set(v___x_6031_, 0, v___x_6034_);
v___x_6037_ = v___x_6031_;
goto v_reusejp_6036_;
}
else
{
lean_object* v_reuseFailAlloc_6038_; 
v_reuseFailAlloc_6038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6038_, 0, v___x_6034_);
v___x_6037_ = v_reuseFailAlloc_6038_;
goto v_reusejp_6036_;
}
v_reusejp_6036_:
{
return v___x_6037_;
}
}
else
{
uint8_t v___x_6039_; 
v___x_6039_ = lean_nat_dec_le(v___x_6033_, v___x_6033_);
if (v___x_6039_ == 0)
{
if (v___x_6035_ == 0)
{
lean_object* v___x_6041_; 
lean_dec(v_a_6029_);
lean_dec_ref(v_a_6014_);
if (v_isShared_6032_ == 0)
{
lean_ctor_set(v___x_6031_, 0, v___x_6034_);
v___x_6041_ = v___x_6031_;
goto v_reusejp_6040_;
}
else
{
lean_object* v_reuseFailAlloc_6042_; 
v_reuseFailAlloc_6042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6042_, 0, v___x_6034_);
v___x_6041_ = v_reuseFailAlloc_6042_;
goto v_reusejp_6040_;
}
v_reusejp_6040_:
{
return v___x_6041_;
}
}
else
{
size_t v___x_6043_; size_t v___x_6044_; lean_object* v___x_6045_; 
lean_del_object(v___x_6031_);
v___x_6043_ = ((size_t)0ULL);
v___x_6044_ = lean_usize_of_nat(v___x_6033_);
v___x_6045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1(v_a_6014_, v_a_6029_, v___x_6043_, v___x_6044_, v___x_6034_, v___y_6016_, v___y_6017_, v___y_6018_, v___y_6019_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_);
lean_dec(v_a_6029_);
return v___x_6045_;
}
}
else
{
size_t v___x_6046_; size_t v___x_6047_; lean_object* v___x_6048_; 
lean_del_object(v___x_6031_);
v___x_6046_ = ((size_t)0ULL);
v___x_6047_ = lean_usize_of_nat(v___x_6033_);
v___x_6048_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1(v_a_6014_, v_a_6029_, v___x_6046_, v___x_6047_, v___x_6034_, v___y_6016_, v___y_6017_, v___y_6018_, v___y_6019_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_);
lean_dec(v_a_6029_);
return v___x_6048_;
}
}
}
}
else
{
lean_object* v_a_6050_; lean_object* v___x_6052_; uint8_t v_isShared_6053_; uint8_t v_isSharedCheck_6057_; 
lean_dec_ref(v_a_6014_);
v_a_6050_ = lean_ctor_get(v___x_6028_, 0);
v_isSharedCheck_6057_ = !lean_is_exclusive(v___x_6028_);
if (v_isSharedCheck_6057_ == 0)
{
v___x_6052_ = v___x_6028_;
v_isShared_6053_ = v_isSharedCheck_6057_;
goto v_resetjp_6051_;
}
else
{
lean_inc(v_a_6050_);
lean_dec(v___x_6028_);
v___x_6052_ = lean_box(0);
v_isShared_6053_ = v_isSharedCheck_6057_;
goto v_resetjp_6051_;
}
v_resetjp_6051_:
{
lean_object* v___x_6055_; 
if (v_isShared_6053_ == 0)
{
v___x_6055_ = v___x_6052_;
goto v_reusejp_6054_;
}
else
{
lean_object* v_reuseFailAlloc_6056_; 
v_reuseFailAlloc_6056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6056_, 0, v_a_6050_);
v___x_6055_ = v_reuseFailAlloc_6056_;
goto v_reusejp_6054_;
}
v_reusejp_6054_:
{
return v___x_6055_;
}
}
}
}
else
{
lean_object* v_a_6058_; lean_object* v___x_6060_; uint8_t v_isShared_6061_; uint8_t v_isSharedCheck_6065_; 
lean_dec_ref(v_a_6014_);
v_a_6058_ = lean_ctor_get(v___x_6026_, 0);
v_isSharedCheck_6065_ = !lean_is_exclusive(v___x_6026_);
if (v_isSharedCheck_6065_ == 0)
{
v___x_6060_ = v___x_6026_;
v_isShared_6061_ = v_isSharedCheck_6065_;
goto v_resetjp_6059_;
}
else
{
lean_inc(v_a_6058_);
lean_dec(v___x_6026_);
v___x_6060_ = lean_box(0);
v_isShared_6061_ = v_isSharedCheck_6065_;
goto v_resetjp_6059_;
}
v_resetjp_6059_:
{
lean_object* v___x_6063_; 
if (v_isShared_6061_ == 0)
{
v___x_6063_ = v___x_6060_;
goto v_reusejp_6062_;
}
else
{
lean_object* v_reuseFailAlloc_6064_; 
v_reuseFailAlloc_6064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6064_, 0, v_a_6058_);
v___x_6063_ = v_reuseFailAlloc_6064_;
goto v_reusejp_6062_;
}
v_reusejp_6062_:
{
return v___x_6063_;
}
}
}
}
else
{
lean_dec_ref(v_a_6014_);
return v___x_6025_;
}
}
else
{
lean_object* v_hypotheses_6066_; uint8_t v_type_6067_; lean_object* v___y_6069_; lean_object* v___y_6070_; lean_object* v___y_6071_; lean_object* v___y_6072_; lean_object* v___y_6073_; lean_object* v___y_6074_; lean_object* v___y_6075_; lean_object* v___y_6076_; 
v_hypotheses_6066_ = lean_ctor_get(v___y_6013_, 0);
lean_inc_ref(v_hypotheses_6066_);
v_type_6067_ = lean_ctor_get_uint8(v___y_6013_, sizeof(void*)*1);
lean_dec_ref(v___y_6013_);
if (v_type_6067_ == 0)
{
v___y_6069_ = v___y_6016_;
v___y_6070_ = v___y_6017_;
v___y_6071_ = v___y_6018_;
v___y_6072_ = v___y_6019_;
v___y_6073_ = v___y_6020_;
v___y_6074_ = v___y_6021_;
v___y_6075_ = v___y_6022_;
v___y_6076_ = v___y_6023_;
goto v___jp_6068_;
}
else
{
lean_object* v___x_6107_; 
lean_inc_ref(v_a_6014_);
v___x_6107_ = l_Lean_Elab_Tactic_NormCast_normCastTarget(v_a_6014_, v___y_6016_, v___y_6017_, v___y_6018_, v___y_6019_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_);
if (lean_obj_tag(v___x_6107_) == 0)
{
lean_dec_ref(v___x_6107_);
v___y_6069_ = v___y_6016_;
v___y_6070_ = v___y_6017_;
v___y_6071_ = v___y_6018_;
v___y_6072_ = v___y_6019_;
v___y_6073_ = v___y_6020_;
v___y_6074_ = v___y_6021_;
v___y_6075_ = v___y_6022_;
v___y_6076_ = v___y_6023_;
goto v___jp_6068_;
}
else
{
lean_dec_ref(v_hypotheses_6066_);
lean_dec_ref(v_a_6014_);
return v___x_6107_;
}
}
v___jp_6068_:
{
lean_object* v___x_6077_; 
v___x_6077_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_6066_, v___y_6069_, v___y_6070_, v___y_6071_, v___y_6072_, v___y_6073_, v___y_6074_, v___y_6075_, v___y_6076_);
if (lean_obj_tag(v___x_6077_) == 0)
{
lean_object* v_a_6078_; lean_object* v___x_6080_; uint8_t v_isShared_6081_; uint8_t v_isSharedCheck_6098_; 
v_a_6078_ = lean_ctor_get(v___x_6077_, 0);
v_isSharedCheck_6098_ = !lean_is_exclusive(v___x_6077_);
if (v_isSharedCheck_6098_ == 0)
{
v___x_6080_ = v___x_6077_;
v_isShared_6081_ = v_isSharedCheck_6098_;
goto v_resetjp_6079_;
}
else
{
lean_inc(v_a_6078_);
lean_dec(v___x_6077_);
v___x_6080_ = lean_box(0);
v_isShared_6081_ = v_isSharedCheck_6098_;
goto v_resetjp_6079_;
}
v_resetjp_6079_:
{
lean_object* v___x_6082_; lean_object* v___x_6083_; uint8_t v___x_6084_; 
v___x_6082_ = lean_array_get_size(v_a_6078_);
v___x_6083_ = lean_box(0);
v___x_6084_ = lean_nat_dec_lt(v___x_6015_, v___x_6082_);
if (v___x_6084_ == 0)
{
lean_object* v___x_6086_; 
lean_dec(v_a_6078_);
lean_dec_ref(v_a_6014_);
if (v_isShared_6081_ == 0)
{
lean_ctor_set(v___x_6080_, 0, v___x_6083_);
v___x_6086_ = v___x_6080_;
goto v_reusejp_6085_;
}
else
{
lean_object* v_reuseFailAlloc_6087_; 
v_reuseFailAlloc_6087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6087_, 0, v___x_6083_);
v___x_6086_ = v_reuseFailAlloc_6087_;
goto v_reusejp_6085_;
}
v_reusejp_6085_:
{
return v___x_6086_;
}
}
else
{
uint8_t v___x_6088_; 
v___x_6088_ = lean_nat_dec_le(v___x_6082_, v___x_6082_);
if (v___x_6088_ == 0)
{
if (v___x_6084_ == 0)
{
lean_object* v___x_6090_; 
lean_dec(v_a_6078_);
lean_dec_ref(v_a_6014_);
if (v_isShared_6081_ == 0)
{
lean_ctor_set(v___x_6080_, 0, v___x_6083_);
v___x_6090_ = v___x_6080_;
goto v_reusejp_6089_;
}
else
{
lean_object* v_reuseFailAlloc_6091_; 
v_reuseFailAlloc_6091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6091_, 0, v___x_6083_);
v___x_6090_ = v_reuseFailAlloc_6091_;
goto v_reusejp_6089_;
}
v_reusejp_6089_:
{
return v___x_6090_;
}
}
else
{
size_t v___x_6092_; size_t v___x_6093_; lean_object* v___x_6094_; 
lean_del_object(v___x_6080_);
v___x_6092_ = ((size_t)0ULL);
v___x_6093_ = lean_usize_of_nat(v___x_6082_);
v___x_6094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1(v_a_6014_, v_a_6078_, v___x_6092_, v___x_6093_, v___x_6083_, v___y_6069_, v___y_6070_, v___y_6071_, v___y_6072_, v___y_6073_, v___y_6074_, v___y_6075_, v___y_6076_);
lean_dec(v_a_6078_);
return v___x_6094_;
}
}
else
{
size_t v___x_6095_; size_t v___x_6096_; lean_object* v___x_6097_; 
lean_del_object(v___x_6080_);
v___x_6095_ = ((size_t)0ULL);
v___x_6096_ = lean_usize_of_nat(v___x_6082_);
v___x_6097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1(v_a_6014_, v_a_6078_, v___x_6095_, v___x_6096_, v___x_6083_, v___y_6069_, v___y_6070_, v___y_6071_, v___y_6072_, v___y_6073_, v___y_6074_, v___y_6075_, v___y_6076_);
lean_dec(v_a_6078_);
return v___x_6097_;
}
}
}
}
else
{
lean_object* v_a_6099_; lean_object* v___x_6101_; uint8_t v_isShared_6102_; uint8_t v_isSharedCheck_6106_; 
lean_dec_ref(v_a_6014_);
v_a_6099_ = lean_ctor_get(v___x_6077_, 0);
v_isSharedCheck_6106_ = !lean_is_exclusive(v___x_6077_);
if (v_isSharedCheck_6106_ == 0)
{
v___x_6101_ = v___x_6077_;
v_isShared_6102_ = v_isSharedCheck_6106_;
goto v_resetjp_6100_;
}
else
{
lean_inc(v_a_6099_);
lean_dec(v___x_6077_);
v___x_6101_ = lean_box(0);
v_isShared_6102_ = v_isSharedCheck_6106_;
goto v_resetjp_6100_;
}
v_resetjp_6100_:
{
lean_object* v___x_6104_; 
if (v_isShared_6102_ == 0)
{
v___x_6104_ = v___x_6101_;
goto v_reusejp_6103_;
}
else
{
lean_object* v_reuseFailAlloc_6105_; 
v_reuseFailAlloc_6105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6105_, 0, v_a_6099_);
v___x_6104_ = v_reuseFailAlloc_6105_;
goto v_reusejp_6103_;
}
v_reusejp_6103_:
{
return v___x_6104_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lam__0___boxed(lean_object* v___y_6108_, lean_object* v_a_6109_, lean_object* v___x_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_, lean_object* v___y_6115_, lean_object* v___y_6116_, lean_object* v___y_6117_, lean_object* v___y_6118_, lean_object* v___y_6119_){
_start:
{
lean_object* v_res_6120_; 
v_res_6120_ = l_Lean_Elab_Tactic_NormCast_evalNormCast0___lam__0(v___y_6108_, v_a_6109_, v___x_6110_, v___y_6111_, v___y_6112_, v___y_6113_, v___y_6114_, v___y_6115_, v___y_6116_, v___y_6117_, v___y_6118_);
lean_dec(v___y_6118_);
lean_dec_ref(v___y_6117_);
lean_dec(v___y_6116_);
lean_dec_ref(v___y_6115_);
lean_dec(v___y_6114_);
lean_dec_ref(v___y_6113_);
lean_dec(v___y_6112_);
lean_dec_ref(v___y_6111_);
lean_dec(v___x_6110_);
return v_res_6120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0(lean_object* v_stx_6130_, lean_object* v_a_6131_, lean_object* v_a_6132_, lean_object* v_a_6133_, lean_object* v_a_6134_, lean_object* v_a_6135_, lean_object* v_a_6136_, lean_object* v_a_6137_, lean_object* v_a_6138_){
_start:
{
lean_object* v___x_6140_; uint8_t v___x_6141_; 
v___x_6140_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__2));
lean_inc(v_stx_6130_);
v___x_6141_ = l_Lean_Syntax_isOfKind(v_stx_6130_, v___x_6140_);
if (v___x_6141_ == 0)
{
lean_object* v___x_6142_; 
lean_dec(v_stx_6130_);
v___x_6142_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg();
return v___x_6142_;
}
else
{
lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___y_6147_; lean_object* v___y_6148_; lean_object* v___y_6149_; lean_object* v___y_6150_; lean_object* v___y_6151_; lean_object* v___y_6152_; lean_object* v___y_6153_; lean_object* v___y_6154_; lean_object* v___y_6155_; lean_object* v___x_6168_; lean_object* v___x_6169_; uint8_t v___x_6170_; 
v___x_6143_ = lean_unsigned_to_nat(0u);
v___x_6144_ = lean_unsigned_to_nat(1u);
v___x_6145_ = l_Lean_Syntax_getArg(v_stx_6130_, v___x_6144_);
v___x_6168_ = lean_unsigned_to_nat(2u);
v___x_6169_ = l_Lean_Syntax_getArg(v_stx_6130_, v___x_6168_);
lean_dec(v_stx_6130_);
v___x_6170_ = l_Lean_Syntax_isNone(v___x_6169_);
if (v___x_6170_ == 0)
{
uint8_t v___x_6171_; 
lean_inc(v___x_6169_);
v___x_6171_ = l_Lean_Syntax_matchesNull(v___x_6169_, v___x_6144_);
if (v___x_6171_ == 0)
{
lean_object* v___x_6172_; 
lean_dec(v___x_6169_);
lean_dec(v___x_6145_);
v___x_6172_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg();
return v___x_6172_;
}
else
{
lean_object* v_loc_x3f_6173_; lean_object* v___x_6174_; 
v_loc_x3f_6173_ = l_Lean_Syntax_getArg(v___x_6169_, v___x_6143_);
lean_dec(v___x_6169_);
v___x_6174_ = l_Lean_Elab_Tactic_expandLocation(v_loc_x3f_6173_);
lean_dec(v_loc_x3f_6173_);
v___y_6147_ = v_a_6136_;
v___y_6148_ = v_a_6132_;
v___y_6149_ = v_a_6138_;
v___y_6150_ = v_a_6134_;
v___y_6151_ = v_a_6135_;
v___y_6152_ = v_a_6133_;
v___y_6153_ = v_a_6131_;
v___y_6154_ = v_a_6137_;
v___y_6155_ = v___x_6174_;
goto v___jp_6146_;
}
}
else
{
lean_object* v___x_6175_; lean_object* v___x_6176_; 
lean_dec(v___x_6169_);
v___x_6175_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__3));
v___x_6176_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_6176_, 0, v___x_6175_);
lean_ctor_set_uint8(v___x_6176_, sizeof(void*)*1, v___x_6141_);
v___y_6147_ = v_a_6136_;
v___y_6148_ = v_a_6132_;
v___y_6149_ = v_a_6138_;
v___y_6150_ = v_a_6134_;
v___y_6151_ = v_a_6135_;
v___y_6152_ = v_a_6133_;
v___y_6153_ = v_a_6131_;
v___y_6154_ = v_a_6137_;
v___y_6155_ = v___x_6176_;
goto v___jp_6146_;
}
v___jp_6146_:
{
lean_object* v___x_6156_; 
v___x_6156_ = l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg(v___x_6145_, v___y_6153_, v___y_6152_, v___y_6150_, v___y_6151_, v___y_6147_, v___y_6154_, v___y_6149_);
if (lean_obj_tag(v___x_6156_) == 0)
{
lean_object* v_a_6157_; lean_object* v___y_6158_; lean_object* v___x_6159_; 
v_a_6157_ = lean_ctor_get(v___x_6156_, 0);
lean_inc(v_a_6157_);
lean_dec_ref(v___x_6156_);
v___y_6158_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___lam__0___boxed), 12, 3);
lean_closure_set(v___y_6158_, 0, v___y_6155_);
lean_closure_set(v___y_6158_, 1, v_a_6157_);
lean_closure_set(v___y_6158_, 2, v___x_6143_);
v___x_6159_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_6158_, v___y_6153_, v___y_6148_, v___y_6152_, v___y_6150_, v___y_6151_, v___y_6147_, v___y_6154_, v___y_6149_);
return v___x_6159_;
}
else
{
lean_object* v_a_6160_; lean_object* v___x_6162_; uint8_t v_isShared_6163_; uint8_t v_isSharedCheck_6167_; 
lean_dec(v___y_6155_);
v_a_6160_ = lean_ctor_get(v___x_6156_, 0);
v_isSharedCheck_6167_ = !lean_is_exclusive(v___x_6156_);
if (v_isSharedCheck_6167_ == 0)
{
v___x_6162_ = v___x_6156_;
v_isShared_6163_ = v_isSharedCheck_6167_;
goto v_resetjp_6161_;
}
else
{
lean_inc(v_a_6160_);
lean_dec(v___x_6156_);
v___x_6162_ = lean_box(0);
v_isShared_6163_ = v_isSharedCheck_6167_;
goto v_resetjp_6161_;
}
v_resetjp_6161_:
{
lean_object* v___x_6165_; 
if (v_isShared_6163_ == 0)
{
v___x_6165_ = v___x_6162_;
goto v_reusejp_6164_;
}
else
{
lean_object* v_reuseFailAlloc_6166_; 
v_reuseFailAlloc_6166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6166_, 0, v_a_6160_);
v___x_6165_ = v_reuseFailAlloc_6166_;
goto v_reusejp_6164_;
}
v_reusejp_6164_:
{
return v___x_6165_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___boxed(lean_object* v_stx_6177_, lean_object* v_a_6178_, lean_object* v_a_6179_, lean_object* v_a_6180_, lean_object* v_a_6181_, lean_object* v_a_6182_, lean_object* v_a_6183_, lean_object* v_a_6184_, lean_object* v_a_6185_, lean_object* v_a_6186_){
_start:
{
lean_object* v_res_6187_; 
v_res_6187_ = l_Lean_Elab_Tactic_NormCast_evalNormCast0(v_stx_6177_, v_a_6178_, v_a_6179_, v_a_6180_, v_a_6181_, v_a_6182_, v_a_6183_, v_a_6184_, v_a_6185_);
lean_dec(v_a_6185_);
lean_dec_ref(v_a_6184_);
lean_dec(v_a_6183_);
lean_dec_ref(v_a_6182_);
lean_dec(v_a_6181_);
lean_dec_ref(v_a_6180_);
lean_dec(v_a_6179_);
lean_dec_ref(v_a_6178_);
return v_res_6187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1(){
_start:
{
lean_object* v___x_6196_; lean_object* v___x_6197_; lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; 
v___x_6196_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6197_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__2));
v___x_6198_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1));
v___x_6199_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___boxed), 10, 0);
v___x_6200_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6196_, v___x_6197_, v___x_6198_, v___x_6199_);
return v___x_6200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___boxed(lean_object* v_a_6201_){
_start:
{
lean_object* v_res_6202_; 
v_res_6202_ = l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1();
return v_res_6202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3(){
_start:
{
lean_object* v___x_6229_; lean_object* v___x_6230_; lean_object* v___x_6231_; 
v___x_6229_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1));
v___x_6230_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__6));
v___x_6231_ = l_Lean_addBuiltinDeclarationRanges(v___x_6229_, v___x_6230_);
return v___x_6231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___boxed(lean_object* v_a_6232_){
_start:
{
lean_object* v_res_6233_; 
v_res_6233_ = l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3();
return v_res_6233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___lam__0(lean_object* v___y_6234_, lean_object* v___y_6235_, lean_object* v___y_6236_, lean_object* v___y_6237_, lean_object* v___y_6238_, lean_object* v___y_6239_, lean_object* v___y_6240_, lean_object* v___y_6241_){
_start:
{
lean_object* v___x_6243_; 
v___x_6243_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_6235_, v___y_6238_, v___y_6239_, v___y_6240_, v___y_6241_);
if (lean_obj_tag(v___x_6243_) == 0)
{
lean_object* v_a_6244_; lean_object* v___x_6245_; lean_object* v___x_6246_; 
v_a_6244_ = lean_ctor_get(v___x_6243_, 0);
lean_inc(v_a_6244_);
lean_dec_ref(v___x_6243_);
v___x_6245_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__10));
v___x_6246_ = l_Lean_Elab_Tactic_NormCast_derive(v_a_6244_, v___x_6245_, v___y_6238_, v___y_6239_, v___y_6240_, v___y_6241_);
if (lean_obj_tag(v___x_6246_) == 0)
{
lean_object* v_a_6247_; lean_object* v___x_6248_; 
v_a_6247_ = lean_ctor_get(v___x_6246_, 0);
lean_inc(v_a_6247_);
lean_dec_ref(v___x_6246_);
v___x_6248_ = l_Lean_Elab_Tactic_Conv_applySimpResult(v_a_6247_, v___y_6234_, v___y_6235_, v___y_6236_, v___y_6237_, v___y_6238_, v___y_6239_, v___y_6240_, v___y_6241_);
return v___x_6248_;
}
else
{
lean_object* v_a_6249_; lean_object* v___x_6251_; uint8_t v_isShared_6252_; uint8_t v_isSharedCheck_6256_; 
v_a_6249_ = lean_ctor_get(v___x_6246_, 0);
v_isSharedCheck_6256_ = !lean_is_exclusive(v___x_6246_);
if (v_isSharedCheck_6256_ == 0)
{
v___x_6251_ = v___x_6246_;
v_isShared_6252_ = v_isSharedCheck_6256_;
goto v_resetjp_6250_;
}
else
{
lean_inc(v_a_6249_);
lean_dec(v___x_6246_);
v___x_6251_ = lean_box(0);
v_isShared_6252_ = v_isSharedCheck_6256_;
goto v_resetjp_6250_;
}
v_resetjp_6250_:
{
lean_object* v___x_6254_; 
if (v_isShared_6252_ == 0)
{
v___x_6254_ = v___x_6251_;
goto v_reusejp_6253_;
}
else
{
lean_object* v_reuseFailAlloc_6255_; 
v_reuseFailAlloc_6255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6255_, 0, v_a_6249_);
v___x_6254_ = v_reuseFailAlloc_6255_;
goto v_reusejp_6253_;
}
v_reusejp_6253_:
{
return v___x_6254_;
}
}
}
}
else
{
lean_object* v_a_6257_; lean_object* v___x_6259_; uint8_t v_isShared_6260_; uint8_t v_isSharedCheck_6264_; 
v_a_6257_ = lean_ctor_get(v___x_6243_, 0);
v_isSharedCheck_6264_ = !lean_is_exclusive(v___x_6243_);
if (v_isSharedCheck_6264_ == 0)
{
v___x_6259_ = v___x_6243_;
v_isShared_6260_ = v_isSharedCheck_6264_;
goto v_resetjp_6258_;
}
else
{
lean_inc(v_a_6257_);
lean_dec(v___x_6243_);
v___x_6259_ = lean_box(0);
v_isShared_6260_ = v_isSharedCheck_6264_;
goto v_resetjp_6258_;
}
v_resetjp_6258_:
{
lean_object* v___x_6262_; 
if (v_isShared_6260_ == 0)
{
v___x_6262_ = v___x_6259_;
goto v_reusejp_6261_;
}
else
{
lean_object* v_reuseFailAlloc_6263_; 
v_reuseFailAlloc_6263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6263_, 0, v_a_6257_);
v___x_6262_ = v_reuseFailAlloc_6263_;
goto v_reusejp_6261_;
}
v_reusejp_6261_:
{
return v___x_6262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___lam__0___boxed(lean_object* v___y_6265_, lean_object* v___y_6266_, lean_object* v___y_6267_, lean_object* v___y_6268_, lean_object* v___y_6269_, lean_object* v___y_6270_, lean_object* v___y_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_){
_start:
{
lean_object* v_res_6274_; 
v_res_6274_ = l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___lam__0(v___y_6265_, v___y_6266_, v___y_6267_, v___y_6268_, v___y_6269_, v___y_6270_, v___y_6271_, v___y_6272_);
lean_dec(v___y_6272_);
lean_dec_ref(v___y_6271_);
lean_dec(v___y_6270_);
lean_dec_ref(v___y_6269_);
lean_dec(v___y_6268_);
lean_dec_ref(v___y_6267_);
lean_dec(v___y_6266_);
lean_dec_ref(v___y_6265_);
return v_res_6274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg(lean_object* v_a_6276_, lean_object* v_a_6277_, lean_object* v_a_6278_, lean_object* v_a_6279_, lean_object* v_a_6280_, lean_object* v_a_6281_, lean_object* v_a_6282_, lean_object* v_a_6283_){
_start:
{
lean_object* v___f_6285_; lean_object* v___x_6286_; 
v___f_6285_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___closed__0));
v___x_6286_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_6285_, v_a_6276_, v_a_6277_, v_a_6278_, v_a_6279_, v_a_6280_, v_a_6281_, v_a_6282_, v_a_6283_);
return v___x_6286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___boxed(lean_object* v_a_6287_, lean_object* v_a_6288_, lean_object* v_a_6289_, lean_object* v_a_6290_, lean_object* v_a_6291_, lean_object* v_a_6292_, lean_object* v_a_6293_, lean_object* v_a_6294_, lean_object* v_a_6295_){
_start:
{
lean_object* v_res_6296_; 
v_res_6296_ = l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg(v_a_6287_, v_a_6288_, v_a_6289_, v_a_6290_, v_a_6291_, v_a_6292_, v_a_6293_, v_a_6294_);
lean_dec(v_a_6294_);
lean_dec_ref(v_a_6293_);
lean_dec(v_a_6292_);
lean_dec_ref(v_a_6291_);
lean_dec(v_a_6290_);
lean_dec_ref(v_a_6289_);
lean_dec(v_a_6288_);
lean_dec_ref(v_a_6287_);
return v_res_6296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast(lean_object* v_x_6297_, lean_object* v_a_6298_, lean_object* v_a_6299_, lean_object* v_a_6300_, lean_object* v_a_6301_, lean_object* v_a_6302_, lean_object* v_a_6303_, lean_object* v_a_6304_, lean_object* v_a_6305_){
_start:
{
lean_object* v___x_6307_; 
v___x_6307_ = l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg(v_a_6298_, v_a_6299_, v_a_6300_, v_a_6301_, v_a_6302_, v_a_6303_, v_a_6304_, v_a_6305_);
return v___x_6307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___boxed(lean_object* v_x_6308_, lean_object* v_a_6309_, lean_object* v_a_6310_, lean_object* v_a_6311_, lean_object* v_a_6312_, lean_object* v_a_6313_, lean_object* v_a_6314_, lean_object* v_a_6315_, lean_object* v_a_6316_, lean_object* v_a_6317_){
_start:
{
lean_object* v_res_6318_; 
v_res_6318_ = l_Lean_Elab_Tactic_NormCast_evalConvNormCast(v_x_6308_, v_a_6309_, v_a_6310_, v_a_6311_, v_a_6312_, v_a_6313_, v_a_6314_, v_a_6315_, v_a_6316_);
lean_dec(v_a_6316_);
lean_dec_ref(v_a_6315_);
lean_dec(v_a_6314_);
lean_dec_ref(v_a_6313_);
lean_dec(v_a_6312_);
lean_dec_ref(v_a_6311_);
lean_dec(v_a_6310_);
lean_dec_ref(v_a_6309_);
lean_dec(v_x_6308_);
return v_res_6318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1(){
_start:
{
lean_object* v___x_6335_; lean_object* v___x_6336_; lean_object* v___x_6337_; lean_object* v___x_6338_; lean_object* v___x_6339_; 
v___x_6335_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6336_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2));
v___x_6337_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4));
v___x_6338_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalConvNormCast___boxed), 10, 0);
v___x_6339_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6335_, v___x_6336_, v___x_6337_, v___x_6338_);
return v___x_6339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___boxed(lean_object* v_a_6340_){
_start:
{
lean_object* v_res_6341_; 
v_res_6341_ = l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1();
return v_res_6341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3(){
_start:
{
lean_object* v___x_6368_; lean_object* v___x_6369_; lean_object* v___x_6370_; 
v___x_6368_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4));
v___x_6369_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__6));
v___x_6370_ = l_Lean_addBuiltinDeclarationRanges(v___x_6368_, v___x_6369_);
return v___x_6370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___boxed(lean_object* v_a_6371_){
_start:
{
lean_object* v_res_6372_; 
v_res_6372_ = l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3();
return v_res_6372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0(lean_object* v_stx_6373_, lean_object* v___x_6374_, lean_object* v_simprocs_6375_, lean_object* v_discharge_x3f_6376_, lean_object* v___y_6377_, lean_object* v___y_6378_, lean_object* v___y_6379_, lean_object* v___y_6380_, lean_object* v___y_6381_, lean_object* v___y_6382_, lean_object* v___y_6383_, lean_object* v___y_6384_){
_start:
{
lean_object* v___x_6386_; lean_object* v___x_6387_; lean_object* v___x_6388_; lean_object* v___x_6389_; 
v___x_6386_ = lean_unsigned_to_nat(5u);
v___x_6387_ = l_Lean_Syntax_getArg(v_stx_6373_, v___x_6386_);
v___x_6388_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_6387_);
lean_dec(v___x_6387_);
v___x_6389_ = l_Lean_Elab_Tactic_simpLocation(v___x_6374_, v_simprocs_6375_, v_discharge_x3f_6376_, v___x_6388_, v___y_6377_, v___y_6378_, v___y_6379_, v___y_6380_, v___y_6381_, v___y_6382_, v___y_6383_, v___y_6384_);
if (lean_obj_tag(v___x_6389_) == 0)
{
lean_object* v___x_6391_; uint8_t v_isShared_6392_; uint8_t v_isSharedCheck_6397_; 
v_isSharedCheck_6397_ = !lean_is_exclusive(v___x_6389_);
if (v_isSharedCheck_6397_ == 0)
{
lean_object* v_unused_6398_; 
v_unused_6398_ = lean_ctor_get(v___x_6389_, 0);
lean_dec(v_unused_6398_);
v___x_6391_ = v___x_6389_;
v_isShared_6392_ = v_isSharedCheck_6397_;
goto v_resetjp_6390_;
}
else
{
lean_dec(v___x_6389_);
v___x_6391_ = lean_box(0);
v_isShared_6392_ = v_isSharedCheck_6397_;
goto v_resetjp_6390_;
}
v_resetjp_6390_:
{
lean_object* v___x_6393_; lean_object* v___x_6395_; 
v___x_6393_ = lean_box(0);
if (v_isShared_6392_ == 0)
{
lean_ctor_set(v___x_6391_, 0, v___x_6393_);
v___x_6395_ = v___x_6391_;
goto v_reusejp_6394_;
}
else
{
lean_object* v_reuseFailAlloc_6396_; 
v_reuseFailAlloc_6396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6396_, 0, v___x_6393_);
v___x_6395_ = v_reuseFailAlloc_6396_;
goto v_reusejp_6394_;
}
v_reusejp_6394_:
{
return v___x_6395_;
}
}
}
else
{
lean_object* v_a_6399_; lean_object* v___x_6401_; uint8_t v_isShared_6402_; uint8_t v_isSharedCheck_6406_; 
v_a_6399_ = lean_ctor_get(v___x_6389_, 0);
v_isSharedCheck_6406_ = !lean_is_exclusive(v___x_6389_);
if (v_isSharedCheck_6406_ == 0)
{
v___x_6401_ = v___x_6389_;
v_isShared_6402_ = v_isSharedCheck_6406_;
goto v_resetjp_6400_;
}
else
{
lean_inc(v_a_6399_);
lean_dec(v___x_6389_);
v___x_6401_ = lean_box(0);
v_isShared_6402_ = v_isSharedCheck_6406_;
goto v_resetjp_6400_;
}
v_resetjp_6400_:
{
lean_object* v___x_6404_; 
if (v_isShared_6402_ == 0)
{
v___x_6404_ = v___x_6401_;
goto v_reusejp_6403_;
}
else
{
lean_object* v_reuseFailAlloc_6405_; 
v_reuseFailAlloc_6405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6405_, 0, v_a_6399_);
v___x_6404_ = v_reuseFailAlloc_6405_;
goto v_reusejp_6403_;
}
v_reusejp_6403_:
{
return v___x_6404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0___boxed(lean_object* v_stx_6407_, lean_object* v___x_6408_, lean_object* v_simprocs_6409_, lean_object* v_discharge_x3f_6410_, lean_object* v___y_6411_, lean_object* v___y_6412_, lean_object* v___y_6413_, lean_object* v___y_6414_, lean_object* v___y_6415_, lean_object* v___y_6416_, lean_object* v___y_6417_, lean_object* v___y_6418_, lean_object* v___y_6419_){
_start:
{
lean_object* v_res_6420_; 
v_res_6420_ = l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0(v_stx_6407_, v___x_6408_, v_simprocs_6409_, v_discharge_x3f_6410_, v___y_6411_, v___y_6412_, v___y_6413_, v___y_6414_, v___y_6415_, v___y_6416_, v___y_6417_, v___y_6418_);
lean_dec(v___y_6418_);
lean_dec_ref(v___y_6417_);
lean_dec(v___y_6416_);
lean_dec_ref(v___y_6415_);
lean_dec(v___y_6414_);
lean_dec_ref(v___y_6413_);
lean_dec(v___y_6412_);
lean_dec_ref(v___y_6411_);
lean_dec(v_stx_6407_);
return v_res_6420_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__0(void){
_start:
{
lean_object* v___x_6421_; lean_object* v___x_6422_; 
v___x_6421_ = l_Lean_Meta_NormCast_pushCastExt;
v___x_6422_ = lean_alloc_closure((void*)(l_Lean_Meta_SimpExtension_getTheorems___boxed), 4, 1);
lean_closure_set(v___x_6422_, 0, v___x_6421_);
return v___x_6422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast(lean_object* v_stx_6423_, lean_object* v_a_6424_, lean_object* v_a_6425_, lean_object* v_a_6426_, lean_object* v_a_6427_, lean_object* v_a_6428_, lean_object* v_a_6429_, lean_object* v_a_6430_, lean_object* v_a_6431_){
_start:
{
uint8_t v___x_6433_; uint8_t v___x_6434_; lean_object* v___x_6435_; lean_object* v___x_6436_; lean_object* v___x_6437_; lean_object* v___x_6438_; lean_object* v___x_6439_; lean_object* v___x_6440_; 
v___x_6433_ = 0;
v___x_6434_ = 0;
v___x_6435_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__0, &l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__0_once, _init_l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__0);
v___x_6436_ = lean_box(v___x_6433_);
v___x_6437_ = lean_box(v___x_6434_);
v___x_6438_ = lean_box(v___x_6433_);
lean_inc(v_stx_6423_);
v___x_6439_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_6439_, 0, v_stx_6423_);
lean_closure_set(v___x_6439_, 1, v___x_6436_);
lean_closure_set(v___x_6439_, 2, v___x_6437_);
lean_closure_set(v___x_6439_, 3, v___x_6438_);
lean_closure_set(v___x_6439_, 4, v___x_6435_);
v___x_6440_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_6439_, v_a_6424_, v_a_6425_, v_a_6426_, v_a_6427_, v_a_6428_, v_a_6429_, v_a_6430_, v_a_6431_);
if (lean_obj_tag(v___x_6440_) == 0)
{
lean_object* v_a_6441_; lean_object* v_ctx_6442_; lean_object* v_simprocs_6443_; lean_object* v_dischargeWrapper_6444_; lean_object* v___x_6445_; lean_object* v___f_6446_; lean_object* v___x_6447_; 
v_a_6441_ = lean_ctor_get(v___x_6440_, 0);
lean_inc(v_a_6441_);
lean_dec_ref(v___x_6440_);
v_ctx_6442_ = lean_ctor_get(v_a_6441_, 0);
lean_inc_ref(v_ctx_6442_);
v_simprocs_6443_ = lean_ctor_get(v_a_6441_, 1);
lean_inc_ref(v_simprocs_6443_);
v_dischargeWrapper_6444_ = lean_ctor_get(v_a_6441_, 2);
lean_inc(v_dischargeWrapper_6444_);
lean_dec(v_a_6441_);
v___x_6445_ = l_Lean_Meta_Simp_Context_setFailIfUnchanged(v_ctx_6442_, v___x_6433_);
v___f_6446_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0___boxed), 13, 3);
lean_closure_set(v___f_6446_, 0, v_stx_6423_);
lean_closure_set(v___f_6446_, 1, v___x_6445_);
lean_closure_set(v___f_6446_, 2, v_simprocs_6443_);
v___x_6447_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v_dischargeWrapper_6444_, v___f_6446_, v_a_6424_, v_a_6425_, v_a_6426_, v_a_6427_, v_a_6428_, v_a_6429_, v_a_6430_, v_a_6431_);
lean_dec(v_dischargeWrapper_6444_);
return v___x_6447_;
}
else
{
lean_object* v_a_6448_; lean_object* v___x_6450_; uint8_t v_isShared_6451_; uint8_t v_isSharedCheck_6455_; 
lean_dec(v_stx_6423_);
v_a_6448_ = lean_ctor_get(v___x_6440_, 0);
v_isSharedCheck_6455_ = !lean_is_exclusive(v___x_6440_);
if (v_isSharedCheck_6455_ == 0)
{
v___x_6450_ = v___x_6440_;
v_isShared_6451_ = v_isSharedCheck_6455_;
goto v_resetjp_6449_;
}
else
{
lean_inc(v_a_6448_);
lean_dec(v___x_6440_);
v___x_6450_ = lean_box(0);
v_isShared_6451_ = v_isSharedCheck_6455_;
goto v_resetjp_6449_;
}
v_resetjp_6449_:
{
lean_object* v___x_6453_; 
if (v_isShared_6451_ == 0)
{
v___x_6453_ = v___x_6450_;
goto v_reusejp_6452_;
}
else
{
lean_object* v_reuseFailAlloc_6454_; 
v_reuseFailAlloc_6454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6454_, 0, v_a_6448_);
v___x_6453_ = v_reuseFailAlloc_6454_;
goto v_reusejp_6452_;
}
v_reusejp_6452_:
{
return v___x_6453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___boxed(lean_object* v_stx_6456_, lean_object* v_a_6457_, lean_object* v_a_6458_, lean_object* v_a_6459_, lean_object* v_a_6460_, lean_object* v_a_6461_, lean_object* v_a_6462_, lean_object* v_a_6463_, lean_object* v_a_6464_, lean_object* v_a_6465_){
_start:
{
lean_object* v_res_6466_; 
v_res_6466_ = l_Lean_Elab_Tactic_NormCast_evalPushCast(v_stx_6456_, v_a_6457_, v_a_6458_, v_a_6459_, v_a_6460_, v_a_6461_, v_a_6462_, v_a_6463_, v_a_6464_);
lean_dec(v_a_6464_);
lean_dec_ref(v_a_6463_);
lean_dec(v_a_6462_);
lean_dec_ref(v_a_6461_);
lean_dec(v_a_6460_);
lean_dec_ref(v_a_6459_);
lean_dec(v_a_6458_);
lean_dec_ref(v_a_6457_);
return v_res_6466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1(){
_start:
{
lean_object* v___x_6481_; lean_object* v___x_6482_; lean_object* v___x_6483_; lean_object* v___x_6484_; lean_object* v___x_6485_; 
v___x_6481_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6482_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1));
v___x_6483_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3));
v___x_6484_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalPushCast___boxed), 10, 0);
v___x_6485_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6481_, v___x_6482_, v___x_6483_, v___x_6484_);
return v___x_6485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___boxed(lean_object* v_a_6486_){
_start:
{
lean_object* v_res_6487_; 
v_res_6487_ = l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1();
return v_res_6487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3(){
_start:
{
lean_object* v___x_6514_; lean_object* v___x_6515_; lean_object* v___x_6516_; 
v___x_6514_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3));
v___x_6515_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__6));
v___x_6516_ = l_Lean_addBuiltinDeclarationRanges(v___x_6514_, v___x_6515_);
return v___x_6516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___boxed(lean_object* v_a_6517_){
_start:
{
lean_object* v_res_6518_; 
v_res_6518_ = l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3();
return v_res_6518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg(){
_start:
{
lean_object* v___x_6520_; lean_object* v___x_6521_; 
v___x_6520_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0);
v___x_6521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6521_, 0, v___x_6520_);
return v___x_6521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg___boxed(lean_object* v___y_6522_){
_start:
{
lean_object* v_res_6523_; 
v_res_6523_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg();
return v_res_6523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0(lean_object* v_00_u03b1_6524_, lean_object* v___y_6525_, lean_object* v___y_6526_){
_start:
{
lean_object* v___x_6528_; 
v___x_6528_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg();
return v___x_6528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___boxed(lean_object* v_00_u03b1_6529_, lean_object* v___y_6530_, lean_object* v___y_6531_, lean_object* v___y_6532_){
_start:
{
lean_object* v_res_6533_; 
v_res_6533_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0(v_00_u03b1_6529_, v___y_6530_, v___y_6531_);
lean_dec(v___y_6531_);
lean_dec_ref(v___y_6530_);
return v_res_6533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___lam__0(lean_object* v___x_6534_, lean_object* v___x_6535_, lean_object* v___x_6536_, lean_object* v___y_6537_, lean_object* v___y_6538_){
_start:
{
lean_object* v___x_6540_; lean_object* v___x_6541_; 
v___x_6540_ = lean_st_mk_ref(v___x_6534_);
v___x_6541_ = l_Lean_realizeGlobalConstNoOverload(v___x_6535_, v___y_6537_, v___y_6538_);
if (lean_obj_tag(v___x_6541_) == 0)
{
lean_object* v_a_6542_; uint8_t v___x_6543_; lean_object* v___x_6544_; lean_object* v___x_6545_; 
v_a_6542_ = lean_ctor_get(v___x_6541_, 0);
lean_inc(v_a_6542_);
lean_dec_ref(v___x_6541_);
v___x_6543_ = 0;
v___x_6544_ = lean_unsigned_to_nat(1000u);
v___x_6545_ = l_Lean_Meta_NormCast_addElim(v_a_6542_, v___x_6543_, v___x_6544_, v___x_6536_, v___x_6540_, v___y_6537_, v___y_6538_);
if (lean_obj_tag(v___x_6545_) == 0)
{
lean_object* v_a_6546_; lean_object* v___x_6548_; uint8_t v_isShared_6549_; uint8_t v_isSharedCheck_6554_; 
v_a_6546_ = lean_ctor_get(v___x_6545_, 0);
v_isSharedCheck_6554_ = !lean_is_exclusive(v___x_6545_);
if (v_isSharedCheck_6554_ == 0)
{
v___x_6548_ = v___x_6545_;
v_isShared_6549_ = v_isSharedCheck_6554_;
goto v_resetjp_6547_;
}
else
{
lean_inc(v_a_6546_);
lean_dec(v___x_6545_);
v___x_6548_ = lean_box(0);
v_isShared_6549_ = v_isSharedCheck_6554_;
goto v_resetjp_6547_;
}
v_resetjp_6547_:
{
lean_object* v___x_6550_; lean_object* v___x_6552_; 
v___x_6550_ = lean_st_ref_get(v___x_6540_);
lean_dec(v___x_6540_);
lean_dec(v___x_6550_);
if (v_isShared_6549_ == 0)
{
v___x_6552_ = v___x_6548_;
goto v_reusejp_6551_;
}
else
{
lean_object* v_reuseFailAlloc_6553_; 
v_reuseFailAlloc_6553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6553_, 0, v_a_6546_);
v___x_6552_ = v_reuseFailAlloc_6553_;
goto v_reusejp_6551_;
}
v_reusejp_6551_:
{
return v___x_6552_;
}
}
}
else
{
lean_dec(v___x_6540_);
return v___x_6545_;
}
}
else
{
lean_object* v_a_6555_; lean_object* v___x_6557_; uint8_t v_isShared_6558_; uint8_t v_isSharedCheck_6562_; 
lean_dec(v___x_6540_);
v_a_6555_ = lean_ctor_get(v___x_6541_, 0);
v_isSharedCheck_6562_ = !lean_is_exclusive(v___x_6541_);
if (v_isSharedCheck_6562_ == 0)
{
v___x_6557_ = v___x_6541_;
v_isShared_6558_ = v_isSharedCheck_6562_;
goto v_resetjp_6556_;
}
else
{
lean_inc(v_a_6555_);
lean_dec(v___x_6541_);
v___x_6557_ = lean_box(0);
v_isShared_6558_ = v_isSharedCheck_6562_;
goto v_resetjp_6556_;
}
v_resetjp_6556_:
{
lean_object* v___x_6560_; 
if (v_isShared_6558_ == 0)
{
v___x_6560_ = v___x_6557_;
goto v_reusejp_6559_;
}
else
{
lean_object* v_reuseFailAlloc_6561_; 
v_reuseFailAlloc_6561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6561_, 0, v_a_6555_);
v___x_6560_ = v_reuseFailAlloc_6561_;
goto v_reusejp_6559_;
}
v_reusejp_6559_:
{
return v___x_6560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___lam__0___boxed(lean_object* v___x_6563_, lean_object* v___x_6564_, lean_object* v___x_6565_, lean_object* v___y_6566_, lean_object* v___y_6567_, lean_object* v___y_6568_){
_start:
{
lean_object* v_res_6569_; 
v_res_6569_ = l_Lean_Elab_Tactic_NormCast_elabAddElim___lam__0(v___x_6563_, v___x_6564_, v___x_6565_, v___y_6566_, v___y_6567_);
lean_dec(v___y_6567_);
lean_dec_ref(v___y_6566_);
lean_dec_ref(v___x_6565_);
return v_res_6569_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__4(void){
_start:
{
lean_object* v___x_6579_; 
v___x_6579_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_6579_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5(void){
_start:
{
lean_object* v___x_6580_; lean_object* v___x_6581_; 
v___x_6580_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__4, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__4_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__4);
v___x_6581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6581_, 0, v___x_6580_);
return v___x_6581_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__6(void){
_start:
{
lean_object* v___x_6582_; lean_object* v___x_6583_; lean_object* v___x_6584_; 
v___x_6582_ = lean_unsigned_to_nat(32u);
v___x_6583_ = lean_mk_empty_array_with_capacity(v___x_6582_);
v___x_6584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6584_, 0, v___x_6583_);
return v___x_6584_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7(void){
_start:
{
size_t v___x_6585_; lean_object* v___x_6586_; lean_object* v___x_6587_; lean_object* v___x_6588_; lean_object* v___x_6589_; lean_object* v___x_6590_; 
v___x_6585_ = ((size_t)5ULL);
v___x_6586_ = lean_unsigned_to_nat(0u);
v___x_6587_ = lean_unsigned_to_nat(32u);
v___x_6588_ = lean_mk_empty_array_with_capacity(v___x_6587_);
v___x_6589_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__6, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__6_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__6);
v___x_6590_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6590_, 0, v___x_6589_);
lean_ctor_set(v___x_6590_, 1, v___x_6588_);
lean_ctor_set(v___x_6590_, 2, v___x_6586_);
lean_ctor_set(v___x_6590_, 3, v___x_6586_);
lean_ctor_set_usize(v___x_6590_, 4, v___x_6585_);
return v___x_6590_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__8(void){
_start:
{
lean_object* v___x_6591_; lean_object* v___x_6592_; lean_object* v___x_6593_; lean_object* v___x_6594_; 
v___x_6591_ = lean_box(1);
v___x_6592_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7);
v___x_6593_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5);
v___x_6594_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6594_, 0, v___x_6593_);
lean_ctor_set(v___x_6594_, 1, v___x_6592_);
lean_ctor_set(v___x_6594_, 2, v___x_6591_);
return v___x_6594_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__10(void){
_start:
{
lean_object* v___x_6597_; lean_object* v___x_6598_; lean_object* v___x_6599_; 
v___x_6597_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5);
v___x_6598_ = lean_unsigned_to_nat(0u);
v___x_6599_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_6599_, 0, v___x_6598_);
lean_ctor_set(v___x_6599_, 1, v___x_6598_);
lean_ctor_set(v___x_6599_, 2, v___x_6598_);
lean_ctor_set(v___x_6599_, 3, v___x_6597_);
lean_ctor_set(v___x_6599_, 4, v___x_6597_);
lean_ctor_set(v___x_6599_, 5, v___x_6597_);
lean_ctor_set(v___x_6599_, 6, v___x_6597_);
lean_ctor_set(v___x_6599_, 7, v___x_6597_);
lean_ctor_set(v___x_6599_, 8, v___x_6597_);
return v___x_6599_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__11(void){
_start:
{
lean_object* v___x_6600_; lean_object* v___x_6601_; 
v___x_6600_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5);
v___x_6601_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6601_, 0, v___x_6600_);
lean_ctor_set(v___x_6601_, 1, v___x_6600_);
lean_ctor_set(v___x_6601_, 2, v___x_6600_);
lean_ctor_set(v___x_6601_, 3, v___x_6600_);
lean_ctor_set(v___x_6601_, 4, v___x_6600_);
lean_ctor_set(v___x_6601_, 5, v___x_6600_);
return v___x_6601_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__12(void){
_start:
{
lean_object* v___x_6602_; lean_object* v___x_6603_; 
v___x_6602_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5);
v___x_6603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6603_, 0, v___x_6602_);
lean_ctor_set(v___x_6603_, 1, v___x_6602_);
lean_ctor_set(v___x_6603_, 2, v___x_6602_);
lean_ctor_set(v___x_6603_, 3, v___x_6602_);
lean_ctor_set(v___x_6603_, 4, v___x_6602_);
return v___x_6603_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__13(void){
_start:
{
lean_object* v___x_6604_; lean_object* v___x_6605_; lean_object* v___x_6606_; lean_object* v___x_6607_; lean_object* v___x_6608_; lean_object* v___x_6609_; 
v___x_6604_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__12, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__12_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__12);
v___x_6605_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7);
v___x_6606_ = lean_box(1);
v___x_6607_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__11, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__11_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__11);
v___x_6608_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__10, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__10_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__10);
v___x_6609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6609_, 0, v___x_6608_);
lean_ctor_set(v___x_6609_, 1, v___x_6607_);
lean_ctor_set(v___x_6609_, 2, v___x_6606_);
lean_ctor_set(v___x_6609_, 3, v___x_6605_);
lean_ctor_set(v___x_6609_, 4, v___x_6604_);
return v___x_6609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim(lean_object* v_stx_6610_, lean_object* v_a_6611_, lean_object* v_a_6612_){
_start:
{
lean_object* v___x_6614_; uint8_t v___x_6615_; 
v___x_6614_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__1));
lean_inc(v_stx_6610_);
v___x_6615_ = l_Lean_Syntax_isOfKind(v_stx_6610_, v___x_6614_);
if (v___x_6615_ == 0)
{
lean_object* v___x_6616_; 
lean_dec(v_stx_6610_);
v___x_6616_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg();
return v___x_6616_;
}
else
{
lean_object* v___x_6617_; lean_object* v___x_6618_; lean_object* v___x_6619_; uint8_t v___x_6620_; 
v___x_6617_ = lean_unsigned_to_nat(1u);
v___x_6618_ = l_Lean_Syntax_getArg(v_stx_6610_, v___x_6617_);
lean_dec(v_stx_6610_);
v___x_6619_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__3));
lean_inc(v___x_6618_);
v___x_6620_ = l_Lean_Syntax_isOfKind(v___x_6618_, v___x_6619_);
if (v___x_6620_ == 0)
{
lean_object* v___x_6621_; 
lean_dec(v___x_6618_);
v___x_6621_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg();
return v___x_6621_;
}
else
{
lean_object* v___x_6622_; uint8_t v___x_6623_; uint8_t v___x_6624_; uint8_t v___x_6625_; uint8_t v___x_6626_; lean_object* v___x_6627_; uint64_t v___x_6628_; lean_object* v___x_6629_; lean_object* v___x_6630_; lean_object* v___x_6631_; lean_object* v___x_6632_; lean_object* v___x_6633_; lean_object* v___x_6634_; lean_object* v___x_6635_; lean_object* v___f_6636_; lean_object* v___x_6637_; 
v___x_6622_ = lean_unsigned_to_nat(0u);
v___x_6623_ = 0;
v___x_6624_ = 1;
v___x_6625_ = 0;
v___x_6626_ = 2;
v___x_6627_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_6627_, 0, v___x_6623_);
lean_ctor_set_uint8(v___x_6627_, 1, v___x_6623_);
lean_ctor_set_uint8(v___x_6627_, 2, v___x_6623_);
lean_ctor_set_uint8(v___x_6627_, 3, v___x_6623_);
lean_ctor_set_uint8(v___x_6627_, 4, v___x_6623_);
lean_ctor_set_uint8(v___x_6627_, 5, v___x_6620_);
lean_ctor_set_uint8(v___x_6627_, 6, v___x_6620_);
lean_ctor_set_uint8(v___x_6627_, 7, v___x_6623_);
lean_ctor_set_uint8(v___x_6627_, 8, v___x_6620_);
lean_ctor_set_uint8(v___x_6627_, 9, v___x_6624_);
lean_ctor_set_uint8(v___x_6627_, 10, v___x_6625_);
lean_ctor_set_uint8(v___x_6627_, 11, v___x_6620_);
lean_ctor_set_uint8(v___x_6627_, 12, v___x_6620_);
lean_ctor_set_uint8(v___x_6627_, 13, v___x_6620_);
lean_ctor_set_uint8(v___x_6627_, 14, v___x_6626_);
lean_ctor_set_uint8(v___x_6627_, 15, v___x_6620_);
lean_ctor_set_uint8(v___x_6627_, 16, v___x_6620_);
lean_ctor_set_uint8(v___x_6627_, 17, v___x_6620_);
lean_ctor_set_uint8(v___x_6627_, 18, v___x_6620_);
v___x_6628_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6627_);
v___x_6629_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_6629_, 0, v___x_6627_);
lean_ctor_set_uint64(v___x_6629_, sizeof(void*)*1, v___x_6628_);
v___x_6630_ = lean_box(1);
v___x_6631_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__8, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__8);
v___x_6632_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__9));
v___x_6633_ = lean_box(0);
v___x_6634_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6634_, 0, v___x_6629_);
lean_ctor_set(v___x_6634_, 1, v___x_6630_);
lean_ctor_set(v___x_6634_, 2, v___x_6631_);
lean_ctor_set(v___x_6634_, 3, v___x_6632_);
lean_ctor_set(v___x_6634_, 4, v___x_6633_);
lean_ctor_set(v___x_6634_, 5, v___x_6622_);
lean_ctor_set(v___x_6634_, 6, v___x_6633_);
lean_ctor_set_uint8(v___x_6634_, sizeof(void*)*7, v___x_6623_);
lean_ctor_set_uint8(v___x_6634_, sizeof(void*)*7 + 1, v___x_6623_);
lean_ctor_set_uint8(v___x_6634_, sizeof(void*)*7 + 2, v___x_6623_);
lean_ctor_set_uint8(v___x_6634_, sizeof(void*)*7 + 3, v___x_6620_);
v___x_6635_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__13, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__13_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__13);
v___f_6636_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___lam__0___boxed), 6, 3);
lean_closure_set(v___f_6636_, 0, v___x_6635_);
lean_closure_set(v___f_6636_, 1, v___x_6618_);
lean_closure_set(v___f_6636_, 2, v___x_6634_);
v___x_6637_ = l_Lean_Elab_Command_liftCoreM___redArg(v___f_6636_, v_a_6611_, v_a_6612_);
return v___x_6637_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___boxed(lean_object* v_stx_6638_, lean_object* v_a_6639_, lean_object* v_a_6640_, lean_object* v_a_6641_){
_start:
{
lean_object* v_res_6642_; 
v_res_6642_ = l_Lean_Elab_Tactic_NormCast_elabAddElim(v_stx_6638_, v_a_6639_, v_a_6640_);
lean_dec(v_a_6640_);
lean_dec_ref(v_a_6639_);
return v_res_6642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1(){
_start:
{
lean_object* v___x_6651_; lean_object* v___x_6652_; lean_object* v___x_6653_; lean_object* v___x_6654_; lean_object* v___x_6655_; 
v___x_6651_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_6652_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__1));
v___x_6653_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1));
v___x_6654_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___boxed), 4, 0);
v___x_6655_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6651_, v___x_6652_, v___x_6653_, v___x_6654_);
return v___x_6655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___boxed(lean_object* v_a_6656_){
_start:
{
lean_object* v_res_6657_; 
v_res_6657_ = l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1();
return v_res_6657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3(){
_start:
{
lean_object* v___x_6684_; lean_object* v___x_6685_; lean_object* v___x_6686_; 
v___x_6684_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1));
v___x_6685_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__6));
v___x_6686_ = l_Lean_addBuiltinDeclarationRanges(v___x_6684_, v___x_6685_);
return v___x_6686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___boxed(lean_object* v_a_6687_){
_start:
{
lean_object* v_res_6688_; 
v_res_6688_ = l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3();
return v_res_6688_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_NormCast(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Conv_Simp(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_NormCast(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_NormCast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Conv_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_NormCast(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_NormCast(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Conv_Simp(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_NormCast(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_NormCast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Conv_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_NormCast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_NormCast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_NormCast(builtin);
}
#ifdef __cplusplus
}
#endif

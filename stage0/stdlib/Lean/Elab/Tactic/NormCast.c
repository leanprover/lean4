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
extern lean_object* l_Lean_Meta_instInhabitedConfigWithKey___private__1;
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
lean_object* v___x_132_; uint8_t v_foApprox_133_; uint8_t v_ctxApprox_134_; uint8_t v_quasiPatternApprox_135_; uint8_t v_constApprox_136_; uint8_t v_isDefEqStuckEx_137_; uint8_t v_unificationHints_138_; uint8_t v_proofIrrelevance_139_; uint8_t v_assignSyntheticOpaque_140_; uint8_t v_offsetCnstrs_141_; uint8_t v_etaStruct_142_; uint8_t v_univApprox_143_; uint8_t v_iota_144_; uint8_t v_beta_145_; uint8_t v_proj_146_; uint8_t v_zeta_147_; uint8_t v_zetaDelta_148_; uint8_t v_zetaUnused_149_; uint8_t v_zetaHave_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_291_; 
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
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_132_);
if (v_isSharedCheck_291_ == 0)
{
v___x_152_ = v___x_132_;
v_isShared_153_ = v_isSharedCheck_291_;
goto v_resetjp_151_;
}
else
{
lean_dec(v___x_132_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_291_;
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
lean_inc(v_zetaDeltaSet_157_);
v_lctx_158_ = lean_ctor_get(v_a_127_, 2);
lean_inc_ref(v_lctx_158_);
v_localInstances_159_ = lean_ctor_get(v_a_127_, 3);
lean_inc_ref(v_localInstances_159_);
v_defEqCtx_x3f_160_ = lean_ctor_get(v_a_127_, 4);
lean_inc(v_defEqCtx_x3f_160_);
v_synthPendingDepth_161_ = lean_ctor_get(v_a_127_, 5);
lean_inc(v_synthPendingDepth_161_);
v_canUnfold_x3f_162_ = lean_ctor_get(v_a_127_, 6);
lean_inc(v_canUnfold_x3f_162_);
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
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 0, v_foApprox_133_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 1, v_ctxApprox_134_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 2, v_quasiPatternApprox_135_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 3, v_constApprox_136_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 4, v_isDefEqStuckEx_137_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 5, v_unificationHints_138_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 6, v_proofIrrelevance_139_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 7, v_assignSyntheticOpaque_140_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 8, v_offsetCnstrs_141_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 10, v_etaStruct_142_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 11, v_univApprox_143_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 12, v_iota_144_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 13, v_beta_145_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 14, v_proj_146_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 15, v_zeta_147_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 16, v_zetaDelta_148_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 17, v_zetaUnused_149_);
lean_ctor_set_uint8(v_reuseFailAlloc_282_, 18, v_zetaHave_150_);
v_config_168_ = v_reuseFailAlloc_282_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
uint64_t v___x_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_274_; 
lean_ctor_set_uint8(v_config_168_, 9, v___x_166_);
v___x_169_ = l_Lean_Meta_Context_configKey(v_a_127_);
v_isSharedCheck_274_ = !lean_is_exclusive(v_a_127_);
if (v_isSharedCheck_274_ == 0)
{
lean_object* v_unused_275_; lean_object* v_unused_276_; lean_object* v_unused_277_; lean_object* v_unused_278_; lean_object* v_unused_279_; lean_object* v_unused_280_; lean_object* v_unused_281_; 
v_unused_275_ = lean_ctor_get(v_a_127_, 6);
lean_dec(v_unused_275_);
v_unused_276_ = lean_ctor_get(v_a_127_, 5);
lean_dec(v_unused_276_);
v_unused_277_ = lean_ctor_get(v_a_127_, 4);
lean_dec(v_unused_277_);
v_unused_278_ = lean_ctor_get(v_a_127_, 3);
lean_dec(v_unused_278_);
v_unused_279_ = lean_ctor_get(v_a_127_, 2);
lean_dec(v_unused_279_);
v_unused_280_ = lean_ctor_get(v_a_127_, 1);
lean_dec(v_unused_280_);
v_unused_281_ = lean_ctor_get(v_a_127_, 0);
lean_dec(v_unused_281_);
v___x_171_ = v_a_127_;
v_isShared_172_ = v_isSharedCheck_274_;
goto v_resetjp_170_;
}
else
{
lean_dec(v_a_127_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_274_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
uint64_t v___x_173_; uint64_t v___x_174_; uint64_t v___x_175_; uint64_t v___x_176_; uint64_t v_key_177_; lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_173_ = 2ULL;
v___x_174_ = lean_uint64_shift_right(v___x_169_, v___x_173_);
v___x_175_ = lean_uint64_shift_left(v___x_174_, v___x_173_);
v___x_176_ = lean_uint64_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__0, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__0_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__0);
v_key_177_ = lean_uint64_lor(v___x_175_, v___x_176_);
v___x_178_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_178_, 0, v_config_168_);
lean_ctor_set_uint64(v___x_178_, sizeof(void*)*1, v_key_177_);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 0, v___x_178_);
v___x_180_ = v___x_171_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_178_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_zetaDeltaSet_157_);
lean_ctor_set(v_reuseFailAlloc_273_, 2, v_lctx_158_);
lean_ctor_set(v_reuseFailAlloc_273_, 3, v_localInstances_159_);
lean_ctor_set(v_reuseFailAlloc_273_, 4, v_defEqCtx_x3f_160_);
lean_ctor_set(v_reuseFailAlloc_273_, 5, v_synthPendingDepth_161_);
lean_ctor_set(v_reuseFailAlloc_273_, 6, v_canUnfold_x3f_162_);
lean_ctor_set_uint8(v_reuseFailAlloc_273_, sizeof(void*)*7, v_trackZetaDelta_156_);
lean_ctor_set_uint8(v_reuseFailAlloc_273_, sizeof(void*)*7 + 1, v_univApprox_163_);
lean_ctor_set_uint8(v_reuseFailAlloc_273_, sizeof(void*)*7 + 2, v_inTypeClassResolution_164_);
lean_ctor_set_uint8(v_reuseFailAlloc_273_, sizeof(void*)*7 + 3, v_cacheInferType_165_);
v___x_180_ = v_reuseFailAlloc_273_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_181_ = lean_box(0);
v___x_182_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__1));
v___x_183_ = lean_unsigned_to_nat(1u);
v___x_184_ = lean_mk_empty_array_with_capacity(v___x_183_);
v___x_185_ = lean_array_push(v___x_184_, v_s_124_);
v___x_186_ = l_Lean_Meta_Simp_mkContext___redArg(v___x_182_, v___x_185_, v_a_155_, v___x_180_, v_a_129_, v_a_130_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_187_; lean_object* v___x_188_; 
v_a_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_a_187_);
lean_dec_ref(v___x_186_);
v___x_188_ = l_Lean_Meta_Simp_mkDefaultMethods(v_a_129_, v_a_130_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_256_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_256_ == 0)
{
v___x_191_ = v___x_188_;
v_isShared_192_ = v_isSharedCheck_256_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_188_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_256_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v_a_196_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_193_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__11, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__11_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__11);
v___x_194_ = lean_st_mk_ref(v___x_193_);
v___x_201_ = l_Lean_Meta_Simp_Methods_toMethodsRefImpl(v_a_189_);
lean_dec(v_a_189_);
lean_inc(v_a_130_);
lean_inc_ref(v_a_129_);
lean_inc(v_a_128_);
lean_inc_ref(v___x_180_);
lean_inc(v___x_194_);
lean_inc(v_a_187_);
lean_inc(v___x_201_);
v___x_202_ = lean_simp(v_a_125_, v___x_201_, v_a_187_, v___x_194_, v___x_180_, v_a_128_, v_a_129_, v_a_130_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; lean_object* v___x_204_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_a_203_);
lean_dec_ref(v___x_202_);
lean_inc(v_a_130_);
lean_inc_ref(v_a_129_);
lean_inc(v_a_128_);
lean_inc_ref(v___x_180_);
lean_inc(v___x_194_);
lean_inc_ref(v_b_126_);
v___x_204_ = lean_simp(v_b_126_, v___x_201_, v_a_187_, v___x_194_, v___x_180_, v_a_128_, v_a_129_, v_a_130_);
if (lean_obj_tag(v___x_204_) == 0)
{
lean_object* v_a_205_; lean_object* v_expr_206_; lean_object* v_expr_207_; lean_object* v___x_208_; 
v_a_205_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_a_205_);
lean_dec_ref(v___x_204_);
v_expr_206_ = lean_ctor_get(v_a_203_, 0);
v_expr_207_ = lean_ctor_get(v_a_205_, 0);
lean_inc(v_a_130_);
lean_inc_ref(v_a_129_);
lean_inc(v_a_128_);
lean_inc_ref(v___x_180_);
lean_inc_ref(v_expr_207_);
lean_inc_ref(v_expr_206_);
v___x_208_ = l_Lean_Meta_isExprDefEq(v_expr_206_, v_expr_207_, v___x_180_, v_a_128_, v_a_129_, v_a_130_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; uint8_t v___x_210_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_a_209_);
lean_dec_ref(v___x_208_);
v___x_210_ = lean_unbox(v_a_209_);
lean_dec(v_a_209_);
if (v___x_210_ == 0)
{
lean_dec(v_a_205_);
lean_dec(v_a_203_);
lean_dec_ref(v___x_180_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec(v_a_128_);
lean_dec_ref(v_b_126_);
v_a_196_ = v___x_181_;
goto v___jp_195_;
}
else
{
lean_object* v___x_211_; 
lean_inc(v_a_130_);
lean_inc_ref(v_a_129_);
lean_inc(v_a_128_);
lean_inc_ref(v___x_180_);
v___x_211_ = l_Lean_Meta_Simp_Result_mkEqSymm(v_b_126_, v_a_205_, v___x_180_, v_a_128_, v_a_129_, v_a_130_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_213_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
lean_dec_ref(v___x_211_);
v___x_213_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_203_, v_a_212_, v___x_180_, v_a_128_, v_a_129_, v_a_130_);
if (lean_obj_tag(v___x_213_) == 0)
{
lean_object* v_a_214_; lean_object* v___x_215_; 
v_a_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_a_214_);
lean_dec_ref(v___x_213_);
v___x_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_215_, 0, v_a_214_);
v_a_196_ = v___x_215_;
goto v___jp_195_;
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
lean_dec(v___x_194_);
lean_del_object(v___x_191_);
v_a_216_ = lean_ctor_get(v___x_213_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_213_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_213_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_213_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
else
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_231_; 
lean_dec(v_a_203_);
lean_dec(v___x_194_);
lean_del_object(v___x_191_);
lean_dec_ref(v___x_180_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec(v_a_128_);
v_a_224_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_231_ == 0)
{
v___x_226_ = v___x_211_;
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_211_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_227_ == 0)
{
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_224_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
}
else
{
lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_239_; 
lean_dec(v_a_205_);
lean_dec(v_a_203_);
lean_dec(v___x_194_);
lean_del_object(v___x_191_);
lean_dec_ref(v___x_180_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec(v_a_128_);
lean_dec_ref(v_b_126_);
v_a_232_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_239_ == 0)
{
v___x_234_ = v___x_208_;
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_208_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_239_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_237_; 
if (v_isShared_235_ == 0)
{
v___x_237_ = v___x_234_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v_a_232_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
lean_dec(v_a_203_);
lean_dec(v___x_194_);
lean_del_object(v___x_191_);
lean_dec_ref(v___x_180_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec(v_a_128_);
lean_dec_ref(v_b_126_);
v_a_240_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_204_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_204_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
else
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_255_; 
lean_dec(v___x_201_);
lean_dec(v___x_194_);
lean_del_object(v___x_191_);
lean_dec(v_a_187_);
lean_dec_ref(v___x_180_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec(v_a_128_);
lean_dec_ref(v_b_126_);
v_a_248_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_255_ == 0)
{
v___x_250_ = v___x_202_;
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_202_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_248_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
v___jp_195_:
{
lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_197_ = lean_st_ref_get(v___x_194_);
lean_dec(v___x_194_);
lean_dec(v___x_197_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 0, v_a_196_);
v___x_199_ = v___x_191_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_196_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
else
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
lean_dec(v_a_187_);
lean_dec_ref(v___x_180_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec(v_a_128_);
lean_dec_ref(v_b_126_);
lean_dec_ref(v_a_125_);
v_a_257_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v___x_188_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_188_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_a_257_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
else
{
lean_object* v_a_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_272_; 
lean_dec_ref(v___x_180_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec(v_a_128_);
lean_dec_ref(v_b_126_);
lean_dec_ref(v_a_125_);
v_a_265_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_272_ == 0)
{
v___x_267_ = v___x_186_;
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_a_265_);
lean_dec(v___x_186_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_272_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_270_; 
if (v_isShared_268_ == 0)
{
v___x_270_ = v___x_267_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_a_265_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
lean_del_object(v___x_152_);
lean_dec(v_a_130_);
lean_dec_ref(v_a_129_);
lean_dec(v_a_128_);
lean_dec_ref(v_a_127_);
lean_dec_ref(v_b_126_);
lean_dec_ref(v_a_125_);
lean_dec_ref(v_s_124_);
v_a_283_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_154_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_154_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsing___boxed(lean_object* v_s_292_, lean_object* v_a_293_, lean_object* v_b_294_, lean_object* v_a_295_, lean_object* v_a_296_, lean_object* v_a_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Elab_Tactic_NormCast_proveEqUsing(v_s_292_, v_a_293_, v_b_294_, v_a_295_, v_a_296_, v_a_297_, v_a_298_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(lean_object* v_cls_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_options_307_; uint8_t v_hasTrace_308_; 
v_options_307_ = lean_ctor_get(v___y_305_, 2);
v_hasTrace_308_ = lean_ctor_get_uint8(v_options_307_, sizeof(void*)*1);
if (v_hasTrace_308_ == 0)
{
lean_object* v___x_309_; lean_object* v___x_310_; 
lean_dec(v_cls_304_);
v___x_309_ = lean_box(v_hasTrace_308_);
v___x_310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
return v___x_310_;
}
else
{
lean_object* v_inheritedTraceOptions_311_; lean_object* v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v_inheritedTraceOptions_311_ = lean_ctor_get(v___y_305_, 13);
v___x_312_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__1));
v___x_313_ = l_Lean_Name_append(v___x_312_, v_cls_304_);
v___x_314_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_311_, v_options_307_, v___x_313_);
lean_dec(v___x_313_);
v___x_315_ = lean_box(v___x_314_);
v___x_316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___boxed(lean_object* v_cls_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v_cls_317_, v___y_318_);
lean_dec_ref(v___y_318_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0(lean_object* v_cls_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v_cls_321_, v___y_324_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___boxed(lean_object* v_cls_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0(v_cls_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
return v_res_334_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = lean_unsigned_to_nat(32u);
v___x_336_ = lean_mk_empty_array_with_capacity(v___x_335_);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_338_ = ((size_t)5ULL);
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_unsigned_to_nat(32u);
v___x_341_ = lean_mk_empty_array_with_capacity(v___x_340_);
v___x_342_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__0);
v___x_343_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___x_341_);
lean_ctor_set(v___x_343_, 2, v___x_339_);
lean_ctor_set(v___x_343_, 3, v___x_339_);
lean_ctor_set_usize(v___x_343_, 4, v___x_338_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg(lean_object* v___y_344_){
_start:
{
lean_object* v___x_346_; lean_object* v_traceState_347_; lean_object* v_traces_348_; lean_object* v___x_349_; lean_object* v_traceState_350_; lean_object* v_env_351_; lean_object* v_nextMacroScope_352_; lean_object* v_ngen_353_; lean_object* v_auxDeclNGen_354_; lean_object* v_cache_355_; lean_object* v_messages_356_; lean_object* v_infoState_357_; lean_object* v_snapshotTasks_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_377_; 
v___x_346_ = lean_st_ref_get(v___y_344_);
v_traceState_347_ = lean_ctor_get(v___x_346_, 4);
lean_inc_ref(v_traceState_347_);
lean_dec(v___x_346_);
v_traces_348_ = lean_ctor_get(v_traceState_347_, 0);
lean_inc_ref(v_traces_348_);
lean_dec_ref(v_traceState_347_);
v___x_349_ = lean_st_ref_take(v___y_344_);
v_traceState_350_ = lean_ctor_get(v___x_349_, 4);
v_env_351_ = lean_ctor_get(v___x_349_, 0);
v_nextMacroScope_352_ = lean_ctor_get(v___x_349_, 1);
v_ngen_353_ = lean_ctor_get(v___x_349_, 2);
v_auxDeclNGen_354_ = lean_ctor_get(v___x_349_, 3);
v_cache_355_ = lean_ctor_get(v___x_349_, 5);
v_messages_356_ = lean_ctor_get(v___x_349_, 6);
v_infoState_357_ = lean_ctor_get(v___x_349_, 7);
v_snapshotTasks_358_ = lean_ctor_get(v___x_349_, 8);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_377_ == 0)
{
v___x_360_ = v___x_349_;
v_isShared_361_ = v_isSharedCheck_377_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_snapshotTasks_358_);
lean_inc(v_infoState_357_);
lean_inc(v_messages_356_);
lean_inc(v_cache_355_);
lean_inc(v_traceState_350_);
lean_inc(v_auxDeclNGen_354_);
lean_inc(v_ngen_353_);
lean_inc(v_nextMacroScope_352_);
lean_inc(v_env_351_);
lean_dec(v___x_349_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_377_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
uint64_t v_tid_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_375_; 
v_tid_362_ = lean_ctor_get_uint64(v_traceState_350_, sizeof(void*)*1);
v_isSharedCheck_375_ = !lean_is_exclusive(v_traceState_350_);
if (v_isSharedCheck_375_ == 0)
{
lean_object* v_unused_376_; 
v_unused_376_ = lean_ctor_get(v_traceState_350_, 0);
lean_dec(v_unused_376_);
v___x_364_ = v_traceState_350_;
v_isShared_365_ = v_isSharedCheck_375_;
goto v_resetjp_363_;
}
else
{
lean_dec(v_traceState_350_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_375_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_366_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__1);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 0, v___x_366_);
v___x_368_ = v___x_364_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v___x_366_);
lean_ctor_set_uint64(v_reuseFailAlloc_374_, sizeof(void*)*1, v_tid_362_);
v___x_368_ = v_reuseFailAlloc_374_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_370_; 
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 4, v___x_368_);
v___x_370_ = v___x_360_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_env_351_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_nextMacroScope_352_);
lean_ctor_set(v_reuseFailAlloc_373_, 2, v_ngen_353_);
lean_ctor_set(v_reuseFailAlloc_373_, 3, v_auxDeclNGen_354_);
lean_ctor_set(v_reuseFailAlloc_373_, 4, v___x_368_);
lean_ctor_set(v_reuseFailAlloc_373_, 5, v_cache_355_);
lean_ctor_set(v_reuseFailAlloc_373_, 6, v_messages_356_);
lean_ctor_set(v_reuseFailAlloc_373_, 7, v_infoState_357_);
lean_ctor_set(v_reuseFailAlloc_373_, 8, v_snapshotTasks_358_);
v___x_370_ = v_reuseFailAlloc_373_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = lean_st_ref_set(v___y_344_, v___x_370_);
v___x_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_372_, 0, v_traces_348_);
return v___x_372_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___boxed(lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg(v___y_378_);
lean_dec(v___y_378_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg(v___y_384_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___boxed(lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v___y_387_, v___y_388_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
lean_dec_ref(v___y_387_);
return v_res_392_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(lean_object* v_opts_393_, lean_object* v_opt_394_){
_start:
{
lean_object* v_name_395_; lean_object* v_defValue_396_; lean_object* v_map_397_; lean_object* v___x_398_; 
v_name_395_ = lean_ctor_get(v_opt_394_, 0);
v_defValue_396_ = lean_ctor_get(v_opt_394_, 1);
v_map_397_ = lean_ctor_get(v_opts_393_, 0);
v___x_398_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_397_, v_name_395_);
if (lean_obj_tag(v___x_398_) == 0)
{
uint8_t v___x_399_; 
v___x_399_ = lean_unbox(v_defValue_396_);
return v___x_399_;
}
else
{
lean_object* v_val_400_; 
v_val_400_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_val_400_);
lean_dec_ref(v___x_398_);
if (lean_obj_tag(v_val_400_) == 1)
{
uint8_t v_v_401_; 
v_v_401_ = lean_ctor_get_uint8(v_val_400_, 0);
lean_dec_ref(v_val_400_);
return v_v_401_;
}
else
{
uint8_t v___x_402_; 
lean_dec(v_val_400_);
v___x_402_ = lean_unbox(v_defValue_396_);
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___boxed(lean_object* v_opts_403_, lean_object* v_opt_404_){
_start:
{
uint8_t v_res_405_; lean_object* v_r_406_; 
v_res_405_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_opts_403_, v_opt_404_);
lean_dec_ref(v_opt_404_);
lean_dec_ref(v_opts_403_);
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__1(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__0));
v___x_409_ = l_Lean_stringToMessageData(v___x_408_);
return v___x_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0(lean_object* v_a_410_, lean_object* v_b_411_, lean_object* v_x_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_Meta_mkEq(v_a_410_, v_b_411_, v___y_413_, v___y_414_, v___y_415_, v___y_416_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_429_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_429_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_429_ == 0)
{
v___x_421_ = v___x_418_;
v_isShared_422_ = v_isSharedCheck_429_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_a_419_);
lean_dec(v___x_418_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_429_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_423_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__1, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__1);
v___x_424_ = l_Lean_MessageData_ofExpr(v_a_419_);
v___x_425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_423_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 0, v___x_425_);
v___x_427_ = v___x_421_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_428_; 
v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_428_, 0, v___x_425_);
v___x_427_ = v_reuseFailAlloc_428_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
return v___x_427_;
}
}
}
else
{
lean_object* v_a_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_437_; 
v_a_430_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_437_ == 0)
{
v___x_432_ = v___x_418_;
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_a_430_);
lean_dec(v___x_418_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_437_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_435_; 
if (v_isShared_433_ == 0)
{
v___x_435_ = v___x_432_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_430_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___boxed(lean_object* v_a_438_, lean_object* v_b_439_, lean_object* v_x_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0(v_a_438_, v_b_439_, v_x_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
lean_dec_ref(v_x_440_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5___redArg(lean_object* v_x_447_){
_start:
{
if (lean_obj_tag(v_x_447_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_451_; uint8_t v_isShared_452_; uint8_t v_isSharedCheck_456_; 
v_a_449_ = lean_ctor_get(v_x_447_, 0);
v_isSharedCheck_456_ = !lean_is_exclusive(v_x_447_);
if (v_isSharedCheck_456_ == 0)
{
v___x_451_ = v_x_447_;
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
else
{
lean_inc(v_a_449_);
lean_dec(v_x_447_);
v___x_451_ = lean_box(0);
v_isShared_452_ = v_isSharedCheck_456_;
goto v_resetjp_450_;
}
v_resetjp_450_:
{
lean_object* v___x_454_; 
if (v_isShared_452_ == 0)
{
lean_ctor_set_tag(v___x_451_, 1);
v___x_454_ = v___x_451_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_455_; 
v_reuseFailAlloc_455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_455_, 0, v_a_449_);
v___x_454_ = v_reuseFailAlloc_455_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
return v___x_454_;
}
}
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
v_a_457_ = lean_ctor_get(v_x_447_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v_x_447_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v_x_447_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v_x_447_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
lean_ctor_set_tag(v___x_459_, 0);
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5___redArg___boxed(lean_object* v_x_465_, lean_object* v___y_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5___redArg(v_x_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__6(lean_object* v_opts_468_, lean_object* v_opt_469_){
_start:
{
lean_object* v_name_470_; lean_object* v_defValue_471_; lean_object* v_map_472_; lean_object* v___x_473_; 
v_name_470_ = lean_ctor_get(v_opt_469_, 0);
v_defValue_471_ = lean_ctor_get(v_opt_469_, 1);
v_map_472_ = lean_ctor_get(v_opts_468_, 0);
v___x_473_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_472_, v_name_470_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_inc(v_defValue_471_);
return v_defValue_471_;
}
else
{
lean_object* v_val_474_; 
v_val_474_ = lean_ctor_get(v___x_473_, 0);
lean_inc(v_val_474_);
lean_dec_ref(v___x_473_);
if (lean_obj_tag(v_val_474_) == 3)
{
lean_object* v_v_475_; 
v_v_475_ = lean_ctor_get(v_val_474_, 0);
lean_inc(v_v_475_);
lean_dec_ref(v_val_474_);
return v_v_475_;
}
else
{
lean_dec(v_val_474_);
lean_inc(v_defValue_471_);
return v_defValue_471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__6___boxed(lean_object* v_opts_476_, lean_object* v_opt_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__6(v_opts_476_, v_opt_477_);
lean_dec_ref(v_opt_477_);
lean_dec_ref(v_opts_476_);
return v_res_478_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__3(lean_object* v_e_479_){
_start:
{
if (lean_obj_tag(v_e_479_) == 0)
{
uint8_t v___x_480_; 
v___x_480_ = 2;
return v___x_480_;
}
else
{
lean_object* v_a_481_; 
v_a_481_ = lean_ctor_get(v_e_479_, 0);
if (lean_obj_tag(v_a_481_) == 0)
{
uint8_t v___x_482_; 
v___x_482_ = 1;
return v___x_482_;
}
else
{
uint8_t v___x_483_; 
v___x_483_ = 0;
return v___x_483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__3___boxed(lean_object* v_e_484_){
_start:
{
uint8_t v_res_485_; lean_object* v_r_486_; 
v_res_485_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__3(v_e_484_);
lean_dec_ref(v_e_484_);
v_r_486_ = lean_box(v_res_485_);
return v_r_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__6(lean_object* v_msgData_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v___x_493_; lean_object* v_env_494_; lean_object* v___x_495_; lean_object* v_mctx_496_; lean_object* v_lctx_497_; lean_object* v_options_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_493_ = lean_st_ref_get(v___y_491_);
v_env_494_ = lean_ctor_get(v___x_493_, 0);
lean_inc_ref(v_env_494_);
lean_dec(v___x_493_);
v___x_495_ = lean_st_ref_get(v___y_489_);
v_mctx_496_ = lean_ctor_get(v___x_495_, 0);
lean_inc_ref(v_mctx_496_);
lean_dec(v___x_495_);
v_lctx_497_ = lean_ctor_get(v___y_488_, 2);
v_options_498_ = lean_ctor_get(v___y_490_, 2);
lean_inc_ref(v_options_498_);
lean_inc_ref(v_lctx_497_);
v___x_499_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_499_, 0, v_env_494_);
lean_ctor_set(v___x_499_, 1, v_mctx_496_);
lean_ctor_set(v___x_499_, 2, v_lctx_497_);
lean_ctor_set(v___x_499_, 3, v_options_498_);
v___x_500_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
lean_ctor_set(v___x_500_, 1, v_msgData_487_);
v___x_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__6___boxed(lean_object* v_msgData_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__6(v_msgData_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__5(size_t v_sz_509_, size_t v_i_510_, lean_object* v_bs_511_){
_start:
{
uint8_t v___x_512_; 
v___x_512_ = lean_usize_dec_lt(v_i_510_, v_sz_509_);
if (v___x_512_ == 0)
{
return v_bs_511_;
}
else
{
lean_object* v_v_513_; lean_object* v_msg_514_; lean_object* v___x_515_; lean_object* v_bs_x27_516_; size_t v___x_517_; size_t v___x_518_; lean_object* v___x_519_; 
v_v_513_ = lean_array_uget_borrowed(v_bs_511_, v_i_510_);
v_msg_514_ = lean_ctor_get(v_v_513_, 1);
lean_inc_ref(v_msg_514_);
v___x_515_ = lean_unsigned_to_nat(0u);
v_bs_x27_516_ = lean_array_uset(v_bs_511_, v_i_510_, v___x_515_);
v___x_517_ = ((size_t)1ULL);
v___x_518_ = lean_usize_add(v_i_510_, v___x_517_);
v___x_519_ = lean_array_uset(v_bs_x27_516_, v_i_510_, v_msg_514_);
v_i_510_ = v___x_518_;
v_bs_511_ = v___x_519_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__5___boxed(lean_object* v_sz_521_, lean_object* v_i_522_, lean_object* v_bs_523_){
_start:
{
size_t v_sz_boxed_524_; size_t v_i_boxed_525_; lean_object* v_res_526_; 
v_sz_boxed_524_ = lean_unbox_usize(v_sz_521_);
lean_dec(v_sz_521_);
v_i_boxed_525_ = lean_unbox_usize(v_i_522_);
lean_dec(v_i_522_);
v_res_526_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__5(v_sz_boxed_524_, v_i_boxed_525_, v_bs_523_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4(lean_object* v_oldTraces_527_, lean_object* v_data_528_, lean_object* v_ref_529_, lean_object* v_msg_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
lean_object* v_fileName_536_; lean_object* v_fileMap_537_; lean_object* v_options_538_; lean_object* v_currRecDepth_539_; lean_object* v_maxRecDepth_540_; lean_object* v_ref_541_; lean_object* v_currNamespace_542_; lean_object* v_openDecls_543_; lean_object* v_initHeartbeats_544_; lean_object* v_maxHeartbeats_545_; lean_object* v_quotContext_546_; lean_object* v_currMacroScope_547_; uint8_t v_diag_548_; lean_object* v_cancelTk_x3f_549_; uint8_t v_suppressElabErrors_550_; lean_object* v_inheritedTraceOptions_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_606_; 
v_fileName_536_ = lean_ctor_get(v___y_533_, 0);
v_fileMap_537_ = lean_ctor_get(v___y_533_, 1);
v_options_538_ = lean_ctor_get(v___y_533_, 2);
v_currRecDepth_539_ = lean_ctor_get(v___y_533_, 3);
v_maxRecDepth_540_ = lean_ctor_get(v___y_533_, 4);
v_ref_541_ = lean_ctor_get(v___y_533_, 5);
v_currNamespace_542_ = lean_ctor_get(v___y_533_, 6);
v_openDecls_543_ = lean_ctor_get(v___y_533_, 7);
v_initHeartbeats_544_ = lean_ctor_get(v___y_533_, 8);
v_maxHeartbeats_545_ = lean_ctor_get(v___y_533_, 9);
v_quotContext_546_ = lean_ctor_get(v___y_533_, 10);
v_currMacroScope_547_ = lean_ctor_get(v___y_533_, 11);
v_diag_548_ = lean_ctor_get_uint8(v___y_533_, sizeof(void*)*14);
v_cancelTk_x3f_549_ = lean_ctor_get(v___y_533_, 12);
v_suppressElabErrors_550_ = lean_ctor_get_uint8(v___y_533_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_551_ = lean_ctor_get(v___y_533_, 13);
v_isSharedCheck_606_ = !lean_is_exclusive(v___y_533_);
if (v_isSharedCheck_606_ == 0)
{
v___x_553_ = v___y_533_;
v_isShared_554_ = v_isSharedCheck_606_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_inheritedTraceOptions_551_);
lean_inc(v_cancelTk_x3f_549_);
lean_inc(v_currMacroScope_547_);
lean_inc(v_quotContext_546_);
lean_inc(v_maxHeartbeats_545_);
lean_inc(v_initHeartbeats_544_);
lean_inc(v_openDecls_543_);
lean_inc(v_currNamespace_542_);
lean_inc(v_ref_541_);
lean_inc(v_maxRecDepth_540_);
lean_inc(v_currRecDepth_539_);
lean_inc(v_options_538_);
lean_inc(v_fileMap_537_);
lean_inc(v_fileName_536_);
lean_dec(v___y_533_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_606_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; lean_object* v_traceState_556_; lean_object* v_traces_557_; lean_object* v_ref_558_; lean_object* v___x_560_; 
v___x_555_ = lean_st_ref_get(v___y_534_);
v_traceState_556_ = lean_ctor_get(v___x_555_, 4);
lean_inc_ref(v_traceState_556_);
lean_dec(v___x_555_);
v_traces_557_ = lean_ctor_get(v_traceState_556_, 0);
lean_inc_ref(v_traces_557_);
lean_dec_ref(v_traceState_556_);
v_ref_558_ = l_Lean_replaceRef(v_ref_529_, v_ref_541_);
lean_dec(v_ref_541_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 5, v_ref_558_);
v___x_560_ = v___x_553_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_fileName_536_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_fileMap_537_);
lean_ctor_set(v_reuseFailAlloc_605_, 2, v_options_538_);
lean_ctor_set(v_reuseFailAlloc_605_, 3, v_currRecDepth_539_);
lean_ctor_set(v_reuseFailAlloc_605_, 4, v_maxRecDepth_540_);
lean_ctor_set(v_reuseFailAlloc_605_, 5, v_ref_558_);
lean_ctor_set(v_reuseFailAlloc_605_, 6, v_currNamespace_542_);
lean_ctor_set(v_reuseFailAlloc_605_, 7, v_openDecls_543_);
lean_ctor_set(v_reuseFailAlloc_605_, 8, v_initHeartbeats_544_);
lean_ctor_set(v_reuseFailAlloc_605_, 9, v_maxHeartbeats_545_);
lean_ctor_set(v_reuseFailAlloc_605_, 10, v_quotContext_546_);
lean_ctor_set(v_reuseFailAlloc_605_, 11, v_currMacroScope_547_);
lean_ctor_set(v_reuseFailAlloc_605_, 12, v_cancelTk_x3f_549_);
lean_ctor_set(v_reuseFailAlloc_605_, 13, v_inheritedTraceOptions_551_);
lean_ctor_set_uint8(v_reuseFailAlloc_605_, sizeof(void*)*14, v_diag_548_);
lean_ctor_set_uint8(v_reuseFailAlloc_605_, sizeof(void*)*14 + 1, v_suppressElabErrors_550_);
v___x_560_ = v_reuseFailAlloc_605_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_561_; size_t v_sz_562_; size_t v___x_563_; lean_object* v___x_564_; lean_object* v_msg_565_; lean_object* v___x_566_; lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_604_; 
v___x_561_ = l_Lean_PersistentArray_toArray___redArg(v_traces_557_);
lean_dec_ref(v_traces_557_);
v_sz_562_ = lean_array_size(v___x_561_);
v___x_563_ = ((size_t)0ULL);
v___x_564_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__5(v_sz_562_, v___x_563_, v___x_561_);
v_msg_565_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_565_, 0, v_data_528_);
lean_ctor_set(v_msg_565_, 1, v_msg_530_);
lean_ctor_set(v_msg_565_, 2, v___x_564_);
v___x_566_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__6(v_msg_565_, v___y_531_, v___y_532_, v___x_560_, v___y_534_);
lean_dec_ref(v___x_560_);
v_a_567_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_604_ == 0)
{
v___x_569_ = v___x_566_;
v_isShared_570_ = v_isSharedCheck_604_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_566_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_604_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; lean_object* v_traceState_572_; lean_object* v_env_573_; lean_object* v_nextMacroScope_574_; lean_object* v_ngen_575_; lean_object* v_auxDeclNGen_576_; lean_object* v_cache_577_; lean_object* v_messages_578_; lean_object* v_infoState_579_; lean_object* v_snapshotTasks_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_603_; 
v___x_571_ = lean_st_ref_take(v___y_534_);
v_traceState_572_ = lean_ctor_get(v___x_571_, 4);
v_env_573_ = lean_ctor_get(v___x_571_, 0);
v_nextMacroScope_574_ = lean_ctor_get(v___x_571_, 1);
v_ngen_575_ = lean_ctor_get(v___x_571_, 2);
v_auxDeclNGen_576_ = lean_ctor_get(v___x_571_, 3);
v_cache_577_ = lean_ctor_get(v___x_571_, 5);
v_messages_578_ = lean_ctor_get(v___x_571_, 6);
v_infoState_579_ = lean_ctor_get(v___x_571_, 7);
v_snapshotTasks_580_ = lean_ctor_get(v___x_571_, 8);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_571_);
if (v_isSharedCheck_603_ == 0)
{
v___x_582_ = v___x_571_;
v_isShared_583_ = v_isSharedCheck_603_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_snapshotTasks_580_);
lean_inc(v_infoState_579_);
lean_inc(v_messages_578_);
lean_inc(v_cache_577_);
lean_inc(v_traceState_572_);
lean_inc(v_auxDeclNGen_576_);
lean_inc(v_ngen_575_);
lean_inc(v_nextMacroScope_574_);
lean_inc(v_env_573_);
lean_dec(v___x_571_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_603_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
uint64_t v_tid_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_601_; 
v_tid_584_ = lean_ctor_get_uint64(v_traceState_572_, sizeof(void*)*1);
v_isSharedCheck_601_ = !lean_is_exclusive(v_traceState_572_);
if (v_isSharedCheck_601_ == 0)
{
lean_object* v_unused_602_; 
v_unused_602_ = lean_ctor_get(v_traceState_572_, 0);
lean_dec(v_unused_602_);
v___x_586_ = v_traceState_572_;
v_isShared_587_ = v_isSharedCheck_601_;
goto v_resetjp_585_;
}
else
{
lean_dec(v_traceState_572_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_601_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_591_; 
v___x_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_588_, 0, v_ref_529_);
lean_ctor_set(v___x_588_, 1, v_a_567_);
v___x_589_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_527_, v___x_588_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 0, v___x_589_);
v___x_591_ = v___x_586_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_589_);
lean_ctor_set_uint64(v_reuseFailAlloc_600_, sizeof(void*)*1, v_tid_584_);
v___x_591_ = v_reuseFailAlloc_600_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_593_; 
if (v_isShared_583_ == 0)
{
lean_ctor_set(v___x_582_, 4, v___x_591_);
v___x_593_ = v___x_582_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_env_573_);
lean_ctor_set(v_reuseFailAlloc_599_, 1, v_nextMacroScope_574_);
lean_ctor_set(v_reuseFailAlloc_599_, 2, v_ngen_575_);
lean_ctor_set(v_reuseFailAlloc_599_, 3, v_auxDeclNGen_576_);
lean_ctor_set(v_reuseFailAlloc_599_, 4, v___x_591_);
lean_ctor_set(v_reuseFailAlloc_599_, 5, v_cache_577_);
lean_ctor_set(v_reuseFailAlloc_599_, 6, v_messages_578_);
lean_ctor_set(v_reuseFailAlloc_599_, 7, v_infoState_579_);
lean_ctor_set(v_reuseFailAlloc_599_, 8, v_snapshotTasks_580_);
v___x_593_ = v_reuseFailAlloc_599_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_594_ = lean_st_ref_set(v___y_534_, v___x_593_);
v___x_595_ = lean_box(0);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_595_);
v___x_597_ = v___x_569_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4___boxed(lean_object* v_oldTraces_607_, lean_object* v_data_608_, lean_object* v_ref_609_, lean_object* v_msg_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4(v_oldTraces_607_, v_data_608_, v_ref_609_, v_msg_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
lean_dec(v___y_614_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
return v_res_616_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__0));
v___x_619_ = l_Lean_stringToMessageData(v___x_618_);
return v___x_619_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2(void){
_start:
{
lean_object* v___x_620_; double v___x_621_; 
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_float_of_nat(v___x_620_);
return v___x_621_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__4(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__3));
v___x_624_ = l_Lean_stringToMessageData(v___x_623_);
return v___x_624_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__5(void){
_start:
{
lean_object* v___x_625_; double v___x_626_; 
v___x_625_ = lean_unsigned_to_nat(1000u);
v___x_626_ = lean_float_of_nat(v___x_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3(lean_object* v_cls_627_, uint8_t v_collapsed_628_, lean_object* v_tag_629_, lean_object* v_opts_630_, uint8_t v_clsEnabled_631_, lean_object* v_oldTraces_632_, lean_object* v_msg_633_, lean_object* v_resStartStop_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_fst_640_; lean_object* v_snd_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_739_; 
v_fst_640_ = lean_ctor_get(v_resStartStop_634_, 0);
v_snd_641_ = lean_ctor_get(v_resStartStop_634_, 1);
v_isSharedCheck_739_ = !lean_is_exclusive(v_resStartStop_634_);
if (v_isSharedCheck_739_ == 0)
{
v___x_643_ = v_resStartStop_634_;
v_isShared_644_ = v_isSharedCheck_739_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_snd_641_);
lean_inc(v_fst_640_);
lean_dec(v_resStartStop_634_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_739_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v_data_648_; lean_object* v_fst_659_; lean_object* v_snd_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_738_; 
v_fst_659_ = lean_ctor_get(v_snd_641_, 0);
v_snd_660_ = lean_ctor_get(v_snd_641_, 1);
v_isSharedCheck_738_ = !lean_is_exclusive(v_snd_641_);
if (v_isSharedCheck_738_ == 0)
{
v___x_662_ = v_snd_641_;
v_isShared_663_ = v_isSharedCheck_738_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_snd_660_);
lean_inc(v_fst_659_);
lean_dec(v_snd_641_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_738_;
goto v_resetjp_661_;
}
v___jp_645_:
{
lean_object* v___x_649_; 
v___x_649_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4(v_oldTraces_632_, v_data_648_, v___y_646_, v___y_647_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
lean_dec(v___y_638_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v___x_650_; 
lean_dec_ref(v___x_649_);
v___x_650_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5___redArg(v_fst_640_);
return v___x_650_;
}
else
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_dec(v_fst_640_);
v_a_651_ = lean_ctor_get(v___x_649_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_649_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_649_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_649_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
v_resetjp_661_:
{
lean_object* v___x_664_; uint8_t v___x_665_; lean_object* v___y_667_; lean_object* v_a_668_; uint8_t v___y_692_; double v___y_723_; 
v___x_664_ = l_Lean_trace_profiler;
v___x_665_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_opts_630_, v___x_664_);
if (v___x_665_ == 0)
{
v___y_692_ = v___x_665_;
goto v___jp_691_;
}
else
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = l_Lean_trace_profiler_useHeartbeats;
v___x_729_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_opts_630_, v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; lean_object* v___x_731_; double v___x_732_; double v___x_733_; double v___x_734_; 
v___x_730_ = l_Lean_trace_profiler_threshold;
v___x_731_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__6(v_opts_630_, v___x_730_);
v___x_732_ = lean_float_of_nat(v___x_731_);
v___x_733_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__5);
v___x_734_ = lean_float_div(v___x_732_, v___x_733_);
v___y_723_ = v___x_734_;
goto v___jp_722_;
}
else
{
lean_object* v___x_735_; lean_object* v___x_736_; double v___x_737_; 
v___x_735_ = l_Lean_trace_profiler_threshold;
v___x_736_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__6(v_opts_630_, v___x_735_);
v___x_737_ = lean_float_of_nat(v___x_736_);
v___y_723_ = v___x_737_;
goto v___jp_722_;
}
}
v___jp_666_:
{
uint8_t v_result_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v_result_669_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__3(v_fst_640_);
v___x_670_ = l_Lean_TraceResult_toEmoji(v_result_669_);
v___x_671_ = l_Lean_stringToMessageData(v___x_670_);
v___x_672_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1);
if (v_isShared_663_ == 0)
{
lean_ctor_set_tag(v___x_662_, 7);
lean_ctor_set(v___x_662_, 1, v___x_672_);
lean_ctor_set(v___x_662_, 0, v___x_671_);
v___x_674_ = v___x_662_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v___x_672_);
v___x_674_ = v_reuseFailAlloc_685_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v_m_676_; 
if (v_isShared_644_ == 0)
{
lean_ctor_set_tag(v___x_643_, 7);
lean_ctor_set(v___x_643_, 1, v_a_668_);
lean_ctor_set(v___x_643_, 0, v___x_674_);
v_m_676_ = v___x_643_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_684_, 1, v_a_668_);
v_m_676_ = v_reuseFailAlloc_684_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_677_; lean_object* v___x_678_; double v___x_679_; lean_object* v_data_680_; 
v___x_677_ = lean_box(v_result_669_);
v___x_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_678_, 0, v___x_677_);
v___x_679_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2);
lean_inc_ref(v_tag_629_);
lean_inc_ref(v___x_678_);
lean_inc(v_cls_627_);
v_data_680_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_680_, 0, v_cls_627_);
lean_ctor_set(v_data_680_, 1, v___x_678_);
lean_ctor_set(v_data_680_, 2, v_tag_629_);
lean_ctor_set_float(v_data_680_, sizeof(void*)*3, v___x_679_);
lean_ctor_set_float(v_data_680_, sizeof(void*)*3 + 8, v___x_679_);
lean_ctor_set_uint8(v_data_680_, sizeof(void*)*3 + 16, v_collapsed_628_);
if (v___x_665_ == 0)
{
lean_dec_ref(v___x_678_);
lean_dec(v_snd_660_);
lean_dec(v_fst_659_);
lean_dec_ref(v_tag_629_);
lean_dec(v_cls_627_);
v___y_646_ = v___y_667_;
v___y_647_ = v_m_676_;
v_data_648_ = v_data_680_;
goto v___jp_645_;
}
else
{
lean_object* v_data_681_; double v___x_682_; double v___x_683_; 
lean_dec_ref(v_data_680_);
v_data_681_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_681_, 0, v_cls_627_);
lean_ctor_set(v_data_681_, 1, v___x_678_);
lean_ctor_set(v_data_681_, 2, v_tag_629_);
v___x_682_ = lean_unbox_float(v_fst_659_);
lean_dec(v_fst_659_);
lean_ctor_set_float(v_data_681_, sizeof(void*)*3, v___x_682_);
v___x_683_ = lean_unbox_float(v_snd_660_);
lean_dec(v_snd_660_);
lean_ctor_set_float(v_data_681_, sizeof(void*)*3 + 8, v___x_683_);
lean_ctor_set_uint8(v_data_681_, sizeof(void*)*3 + 16, v_collapsed_628_);
v___y_646_ = v___y_667_;
v___y_647_ = v_m_676_;
v_data_648_ = v_data_681_;
goto v___jp_645_;
}
}
}
}
v___jp_686_:
{
lean_object* v_ref_687_; lean_object* v___x_688_; 
v_ref_687_ = lean_ctor_get(v___y_637_, 5);
lean_inc(v___y_638_);
lean_inc_ref(v___y_637_);
lean_inc(v___y_636_);
lean_inc_ref(v___y_635_);
lean_inc(v_fst_640_);
v___x_688_ = lean_apply_6(v_msg_633_, v_fst_640_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, lean_box(0));
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_a_689_);
lean_dec_ref(v___x_688_);
lean_inc(v_ref_687_);
v___y_667_ = v_ref_687_;
v_a_668_ = v_a_689_;
goto v___jp_666_;
}
else
{
lean_object* v___x_690_; 
lean_dec_ref(v___x_688_);
v___x_690_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__4);
lean_inc(v_ref_687_);
v___y_667_ = v_ref_687_;
v_a_668_ = v___x_690_;
goto v___jp_666_;
}
}
v___jp_691_:
{
if (v_clsEnabled_631_ == 0)
{
if (v___y_692_ == 0)
{
lean_object* v___x_693_; lean_object* v_traceState_694_; lean_object* v_env_695_; lean_object* v_nextMacroScope_696_; lean_object* v_ngen_697_; lean_object* v_auxDeclNGen_698_; lean_object* v_cache_699_; lean_object* v_messages_700_; lean_object* v_infoState_701_; lean_object* v_snapshotTasks_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_721_; 
lean_del_object(v___x_662_);
lean_dec(v_snd_660_);
lean_dec(v_fst_659_);
lean_del_object(v___x_643_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec_ref(v_msg_633_);
lean_dec_ref(v_tag_629_);
lean_dec(v_cls_627_);
v___x_693_ = lean_st_ref_take(v___y_638_);
v_traceState_694_ = lean_ctor_get(v___x_693_, 4);
v_env_695_ = lean_ctor_get(v___x_693_, 0);
v_nextMacroScope_696_ = lean_ctor_get(v___x_693_, 1);
v_ngen_697_ = lean_ctor_get(v___x_693_, 2);
v_auxDeclNGen_698_ = lean_ctor_get(v___x_693_, 3);
v_cache_699_ = lean_ctor_get(v___x_693_, 5);
v_messages_700_ = lean_ctor_get(v___x_693_, 6);
v_infoState_701_ = lean_ctor_get(v___x_693_, 7);
v_snapshotTasks_702_ = lean_ctor_get(v___x_693_, 8);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_721_ == 0)
{
v___x_704_ = v___x_693_;
v_isShared_705_ = v_isSharedCheck_721_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_snapshotTasks_702_);
lean_inc(v_infoState_701_);
lean_inc(v_messages_700_);
lean_inc(v_cache_699_);
lean_inc(v_traceState_694_);
lean_inc(v_auxDeclNGen_698_);
lean_inc(v_ngen_697_);
lean_inc(v_nextMacroScope_696_);
lean_inc(v_env_695_);
lean_dec(v___x_693_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_721_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
uint64_t v_tid_706_; lean_object* v_traces_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_720_; 
v_tid_706_ = lean_ctor_get_uint64(v_traceState_694_, sizeof(void*)*1);
v_traces_707_ = lean_ctor_get(v_traceState_694_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v_traceState_694_);
if (v_isSharedCheck_720_ == 0)
{
v___x_709_ = v_traceState_694_;
v_isShared_710_ = v_isSharedCheck_720_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_traces_707_);
lean_dec(v_traceState_694_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_720_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_711_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_632_, v_traces_707_);
lean_dec_ref(v_traces_707_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_711_);
v___x_713_ = v___x_709_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_711_);
lean_ctor_set_uint64(v_reuseFailAlloc_719_, sizeof(void*)*1, v_tid_706_);
v___x_713_ = v_reuseFailAlloc_719_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_715_; 
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 4, v___x_713_);
v___x_715_ = v___x_704_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_env_695_);
lean_ctor_set(v_reuseFailAlloc_718_, 1, v_nextMacroScope_696_);
lean_ctor_set(v_reuseFailAlloc_718_, 2, v_ngen_697_);
lean_ctor_set(v_reuseFailAlloc_718_, 3, v_auxDeclNGen_698_);
lean_ctor_set(v_reuseFailAlloc_718_, 4, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_718_, 5, v_cache_699_);
lean_ctor_set(v_reuseFailAlloc_718_, 6, v_messages_700_);
lean_ctor_set(v_reuseFailAlloc_718_, 7, v_infoState_701_);
lean_ctor_set(v_reuseFailAlloc_718_, 8, v_snapshotTasks_702_);
v___x_715_ = v_reuseFailAlloc_718_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_716_ = lean_st_ref_set(v___y_638_, v___x_715_);
lean_dec(v___y_638_);
v___x_717_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5___redArg(v_fst_640_);
return v___x_717_;
}
}
}
}
}
else
{
goto v___jp_686_;
}
}
else
{
goto v___jp_686_;
}
}
v___jp_722_:
{
double v___x_724_; double v___x_725_; double v___x_726_; uint8_t v___x_727_; 
v___x_724_ = lean_unbox_float(v_snd_660_);
v___x_725_ = lean_unbox_float(v_fst_659_);
v___x_726_ = lean_float_sub(v___x_724_, v___x_725_);
v___x_727_ = lean_float_decLt(v___y_723_, v___x_726_);
v___y_692_ = v___x_727_;
goto v___jp_691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___boxed(lean_object* v_cls_740_, lean_object* v_collapsed_741_, lean_object* v_tag_742_, lean_object* v_opts_743_, lean_object* v_clsEnabled_744_, lean_object* v_oldTraces_745_, lean_object* v_msg_746_, lean_object* v_resStartStop_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
uint8_t v_collapsed_boxed_753_; uint8_t v_clsEnabled_boxed_754_; lean_object* v_res_755_; 
v_collapsed_boxed_753_ = lean_unbox(v_collapsed_741_);
v_clsEnabled_boxed_754_ = lean_unbox(v_clsEnabled_744_);
v_res_755_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3(v_cls_740_, v_collapsed_boxed_753_, v_tag_742_, v_opts_743_, v_clsEnabled_boxed_754_, v_oldTraces_745_, v_msg_746_, v_resStartStop_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec_ref(v_opts_743_);
return v_res_755_;
}
}
static double _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1(void){
_start:
{
lean_object* v___x_757_; double v___x_758_; 
v___x_757_ = lean_unsigned_to_nat(1000000000u);
v___x_758_ = lean_float_of_nat(v___x_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(lean_object* v_a_759_, lean_object* v_b_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_){
_start:
{
lean_object* v___x_766_; lean_object* v_options_767_; uint8_t v_hasTrace_768_; 
v___x_766_ = l_Lean_Meta_NormCast_normCastExt;
v_options_767_ = lean_ctor_get(v_a_763_, 2);
v_hasTrace_768_ = lean_ctor_get_uint8(v_options_767_, sizeof(void*)*1);
if (v_hasTrace_768_ == 0)
{
lean_object* v_down_769_; lean_object* v___x_770_; 
v_down_769_ = lean_ctor_get(v___x_766_, 1);
lean_inc_ref(v_down_769_);
v___x_770_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_down_769_, v_a_764_);
lean_dec_ref(v_down_769_);
if (lean_obj_tag(v___x_770_) == 0)
{
lean_object* v_a_771_; lean_object* v___x_772_; 
v_a_771_ = lean_ctor_get(v___x_770_, 0);
lean_inc(v_a_771_);
lean_dec_ref(v___x_770_);
v___x_772_ = l_Lean_Elab_Tactic_NormCast_proveEqUsing(v_a_771_, v_a_759_, v_b_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
return v___x_772_;
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
lean_dec_ref(v_b_760_);
lean_dec_ref(v_a_759_);
v_a_773_ = lean_ctor_get(v___x_770_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_770_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_770_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_770_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
else
{
lean_object* v_down_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_878_; 
v_down_781_ = lean_ctor_get(v___x_766_, 1);
lean_inc_ref(v_down_781_);
v___x_782_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__2_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_));
v___x_783_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___x_782_, v_a_763_);
v_a_784_ = lean_ctor_get(v___x_783_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_783_);
if (v_isSharedCheck_878_ == 0)
{
v___x_786_ = v___x_783_;
v_isShared_787_ = v_isSharedCheck_878_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_783_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_878_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___f_788_; lean_object* v___x_789_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v_a_793_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v_a_809_; lean_object* v___y_814_; lean_object* v___y_815_; lean_object* v_a_816_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v_a_829_; uint8_t v___x_864_; 
lean_inc_ref(v_b_760_);
lean_inc_ref(v_a_759_);
v___f_788_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___boxed), 8, 2);
lean_closure_set(v___f_788_, 0, v_a_759_);
lean_closure_set(v___f_788_, 1, v_b_760_);
v___x_789_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_864_ = lean_unbox(v_a_784_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_865_ = l_Lean_trace_profiler;
v___x_866_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_767_, v___x_865_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; 
lean_dec_ref(v___f_788_);
lean_del_object(v___x_786_);
lean_dec(v_a_784_);
v___x_867_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_down_781_, v_a_764_);
lean_dec_ref(v_down_781_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_869_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref(v___x_867_);
v___x_869_ = l_Lean_Elab_Tactic_NormCast_proveEqUsing(v_a_868_, v_a_759_, v_b_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
return v___x_869_;
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
lean_dec_ref(v_b_760_);
lean_dec_ref(v_a_759_);
v_a_870_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_867_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_867_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
else
{
lean_inc_ref(v_options_767_);
goto v___jp_831_;
}
}
else
{
lean_inc_ref(v_options_767_);
goto v___jp_831_;
}
v___jp_790_:
{
lean_object* v___x_794_; double v___x_795_; double v___x_796_; double v___x_797_; double v___x_798_; double v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; lean_object* v___x_805_; 
v___x_794_ = lean_io_mono_nanos_now();
v___x_795_ = lean_float_of_nat(v___y_792_);
v___x_796_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1);
v___x_797_ = lean_float_div(v___x_795_, v___x_796_);
v___x_798_ = lean_float_of_nat(v___x_794_);
v___x_799_ = lean_float_div(v___x_798_, v___x_796_);
v___x_800_ = lean_box_float(v___x_797_);
v___x_801_ = lean_box_float(v___x_799_);
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_800_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v_a_793_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
v___x_804_ = lean_unbox(v_a_784_);
lean_dec(v_a_784_);
v___x_805_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3(v___x_782_, v_hasTrace_768_, v___x_789_, v_options_767_, v___x_804_, v___y_791_, v___f_788_, v___x_803_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
lean_dec_ref(v_options_767_);
return v___x_805_;
}
v___jp_806_:
{
lean_object* v___x_811_; 
if (v_isShared_787_ == 0)
{
lean_ctor_set(v___x_786_, 0, v_a_809_);
v___x_811_ = v___x_786_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
v___y_791_ = v___y_807_;
v___y_792_ = v___y_808_;
v_a_793_ = v___x_811_;
goto v___jp_790_;
}
}
v___jp_813_:
{
lean_object* v___x_817_; double v___x_818_; double v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; uint8_t v___x_824_; lean_object* v___x_825_; 
v___x_817_ = lean_io_get_num_heartbeats();
v___x_818_ = lean_float_of_nat(v___y_814_);
v___x_819_ = lean_float_of_nat(v___x_817_);
v___x_820_ = lean_box_float(v___x_818_);
v___x_821_ = lean_box_float(v___x_819_);
v___x_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_820_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_823_, 0, v_a_816_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
v___x_824_ = lean_unbox(v_a_784_);
lean_dec(v_a_784_);
v___x_825_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3(v___x_782_, v_hasTrace_768_, v___x_789_, v_options_767_, v___x_824_, v___y_815_, v___f_788_, v___x_823_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
lean_dec_ref(v_options_767_);
return v___x_825_;
}
v___jp_826_:
{
lean_object* v___x_830_; 
v___x_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_830_, 0, v_a_829_);
v___y_814_ = v___y_827_;
v___y_815_ = v___y_828_;
v_a_816_ = v___x_830_;
goto v___jp_813_;
}
v___jp_831_:
{
lean_object* v___x_832_; lean_object* v_a_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_832_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg(v_a_764_);
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref(v___x_832_);
v___x_834_ = l_Lean_trace_profiler_useHeartbeats;
v___x_835_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_767_, v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_836_ = lean_io_mono_nanos_now();
v___x_837_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_down_781_, v_a_764_);
lean_dec_ref(v_down_781_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v___x_839_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref(v___x_837_);
lean_inc(v_a_764_);
lean_inc_ref(v_a_763_);
lean_inc(v_a_762_);
lean_inc_ref(v_a_761_);
v___x_839_ = l_Lean_Elab_Tactic_NormCast_proveEqUsing(v_a_838_, v_a_759_, v_b_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_del_object(v___x_786_);
v_a_840_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_839_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_839_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
lean_ctor_set_tag(v___x_842_, 1);
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
v___y_791_ = v_a_833_;
v___y_792_ = v___x_836_;
v_a_793_ = v___x_845_;
goto v___jp_790_;
}
}
}
else
{
lean_object* v_a_848_; 
v_a_848_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_848_);
lean_dec_ref(v___x_839_);
v___y_807_ = v_a_833_;
v___y_808_ = v___x_836_;
v_a_809_ = v_a_848_;
goto v___jp_806_;
}
}
else
{
lean_object* v_a_849_; 
lean_dec_ref(v_b_760_);
lean_dec_ref(v_a_759_);
v_a_849_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_849_);
lean_dec_ref(v___x_837_);
v___y_807_ = v_a_833_;
v___y_808_ = v___x_836_;
v_a_809_ = v_a_849_;
goto v___jp_806_;
}
}
else
{
lean_object* v___x_850_; lean_object* v___x_851_; 
lean_del_object(v___x_786_);
v___x_850_ = lean_io_get_num_heartbeats();
v___x_851_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_down_781_, v_a_764_);
lean_dec_ref(v_down_781_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_853_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_852_);
lean_dec_ref(v___x_851_);
lean_inc(v_a_764_);
lean_inc_ref(v_a_763_);
lean_inc(v_a_762_);
lean_inc_ref(v_a_761_);
v___x_853_ = l_Lean_Elab_Tactic_NormCast_proveEqUsing(v_a_852_, v_a_759_, v_b_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
lean_ctor_set_tag(v___x_856_, 1);
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
v___y_814_ = v___x_850_;
v___y_815_ = v_a_833_;
v_a_816_ = v___x_859_;
goto v___jp_813_;
}
}
}
else
{
lean_object* v_a_862_; 
v_a_862_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_862_);
lean_dec_ref(v___x_853_);
v___y_827_ = v___x_850_;
v___y_828_ = v_a_833_;
v_a_829_ = v_a_862_;
goto v___jp_826_;
}
}
else
{
lean_object* v_a_863_; 
lean_dec_ref(v_b_760_);
lean_dec_ref(v_a_759_);
v_a_863_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_863_);
lean_dec_ref(v___x_851_);
v___y_827_ = v___x_850_;
v___y_828_ = v_a_833_;
v_a_829_ = v_a_863_;
goto v___jp_826_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___boxed(lean_object* v_a_879_, lean_object* v_b_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_a_879_, v_b_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5(lean_object* v_00_u03b1_887_, lean_object* v_x_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5___redArg(v_x_888_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5___boxed(lean_object* v_00_u03b1_895_, lean_object* v_x_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5(v_00_u03b1_895_, v_x_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(lean_object* v_msg_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_ref_909_; lean_object* v___x_910_; lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_919_; 
v_ref_909_ = lean_ctor_get(v___y_906_, 5);
v___x_910_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__6(v_msg_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
v_a_911_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_919_ == 0)
{
v___x_913_ = v___x_910_;
v_isShared_914_ = v_isSharedCheck_919_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_910_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_919_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_915_; lean_object* v___x_917_; 
lean_inc(v_ref_909_);
v___x_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_915_, 0, v_ref_909_);
lean_ctor_set(v___x_915_, 1, v_a_911_);
if (v_isShared_914_ == 0)
{
lean_ctor_set_tag(v___x_913_, 1);
lean_ctor_set(v___x_913_, 0, v___x_915_);
v___x_917_ = v___x_913_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v___x_915_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg___boxed(lean_object* v_msg_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v_msg_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
return v_res_926_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_mkCoe___closed__0));
v___x_929_ = l_Lean_stringToMessageData(v___x_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_mkCoe(lean_object* v_e_930_, lean_object* v_ty_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v___x_937_; 
lean_inc(v_a_935_);
lean_inc_ref(v_a_934_);
lean_inc(v_a_933_);
lean_inc_ref(v_a_932_);
v___x_937_ = l_Lean_Meta_coerce_x3f(v_e_930_, v_ty_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_948_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_948_ == 0)
{
v___x_940_ = v___x_937_;
v_isShared_941_ = v_isSharedCheck_948_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_937_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_948_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
if (lean_obj_tag(v_a_938_) == 1)
{
lean_object* v_a_942_; lean_object* v___x_944_; 
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
v_a_942_ = lean_ctor_get(v_a_938_, 0);
lean_inc(v_a_942_);
lean_dec_ref(v_a_938_);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v_a_942_);
v___x_944_ = v___x_940_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_942_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
else
{
lean_object* v___x_946_; lean_object* v___x_947_; 
lean_del_object(v___x_940_);
lean_dec(v_a_938_);
v___x_946_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_947_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_946_, v_a_932_, v_a_933_, v_a_934_, v_a_935_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
return v___x_947_;
}
}
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
lean_dec(v_a_933_);
lean_dec_ref(v_a_932_);
v_a_949_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_937_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_937_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_mkCoe___boxed(lean_object* v_e_957_, lean_object* v_ty_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_e_957_, v_ty_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0(lean_object* v_00_u03b1_965_, lean_object* v_msg_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
lean_object* v___x_972_; 
v___x_972_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v_msg_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___boxed(lean_object* v_00_u03b1_973_, lean_object* v_msg_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0(v_00_u03b1_973_, v_msg_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(lean_object* v_e_981_, lean_object* v_a_982_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_Expr_getAppFn(v_e_981_);
if (lean_obj_tag(v___x_987_) == 4)
{
lean_object* v_declName_988_; lean_object* v___x_989_; 
v_declName_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_declName_988_);
lean_dec_ref(v___x_987_);
v___x_989_ = l_Lean_Meta_getCoeFnInfo_x3f___redArg(v_declName_988_, v_a_982_);
lean_dec(v_declName_988_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_1013_; 
v_a_990_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_992_ = v___x_989_;
v_isShared_993_ = v_isSharedCheck_1013_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_989_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_1013_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
if (lean_obj_tag(v_a_990_) == 1)
{
lean_object* v_val_994_; lean_object* v___x_996_; uint8_t v_isShared_997_; uint8_t v_isSharedCheck_1012_; 
v_val_994_ = lean_ctor_get(v_a_990_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_a_990_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_996_ = v_a_990_;
v_isShared_997_ = v_isSharedCheck_1012_;
goto v_resetjp_995_;
}
else
{
lean_inc(v_val_994_);
lean_dec(v_a_990_);
v___x_996_ = lean_box(0);
v_isShared_997_ = v_isSharedCheck_1012_;
goto v_resetjp_995_;
}
v_resetjp_995_:
{
lean_object* v_numArgs_998_; lean_object* v_coercee_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v_numArgs_998_ = lean_ctor_get(v_val_994_, 0);
lean_inc(v_numArgs_998_);
v_coercee_999_ = lean_ctor_get(v_val_994_, 1);
lean_inc(v_coercee_999_);
lean_dec(v_val_994_);
v___x_1000_ = l_Lean_Expr_getAppNumArgs(v_e_981_);
v___x_1001_ = lean_nat_dec_eq(v___x_1000_, v_numArgs_998_);
lean_dec(v_numArgs_998_);
if (v___x_1001_ == 0)
{
lean_dec(v___x_1000_);
lean_dec(v_coercee_999_);
lean_del_object(v___x_996_);
lean_del_object(v___x_992_);
goto v___jp_984_;
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1007_; 
v___x_1002_ = lean_nat_sub(v___x_1000_, v_coercee_999_);
lean_dec(v_coercee_999_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_unsigned_to_nat(1u);
v___x_1004_ = lean_nat_sub(v___x_1002_, v___x_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = l_Lean_Expr_getRevArg_x21(v_e_981_, v___x_1004_);
if (v_isShared_997_ == 0)
{
lean_ctor_set(v___x_996_, 0, v___x_1005_);
v___x_1007_ = v___x_996_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1009_; 
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_1007_);
v___x_1009_ = v___x_992_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
else
{
lean_del_object(v___x_992_);
lean_dec(v_a_990_);
goto v___jp_984_;
}
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
v_a_1014_ = lean_ctor_get(v___x_989_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_989_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_989_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_989_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
else
{
lean_dec_ref(v___x_987_);
goto v___jp_984_;
}
v___jp_984_:
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_box(0);
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
return v___x_986_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg___boxed(lean_object* v_e_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_e_1022_, v_a_1023_);
lean_dec(v_a_1023_);
lean_dec_ref(v_e_1022_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f(lean_object* v_e_1026_, lean_object* v_a_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_e_1026_, v_a_1030_);
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___boxed(lean_object* v_e_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f(v_e_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_);
lean_dec(v_a_1037_);
lean_dec_ref(v_a_1036_);
lean_dec(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec_ref(v_e_1033_);
return v_res_1039_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__6(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1049_ = lean_box(0);
v___x_1050_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__5));
v___x_1051_ = l_Lean_mkConst(v___x_1050_, v___x_1049_);
return v___x_1051_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__7(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1052_ = lean_unsigned_to_nat(0u);
v___x_1053_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__6, &l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__6_once, _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__6);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v___x_1052_);
return v___x_1054_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__8(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__7, &l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__7_once, _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__7);
v___x_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(lean_object* v_e_1057_){
_start:
{
lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1058_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__2));
v___x_1059_ = l_Lean_Expr_isConstOf(v_e_1057_, v___x_1058_);
if (v___x_1059_ == 0)
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Lean_Expr_consumeMData(v_e_1057_);
if (lean_obj_tag(v___x_1060_) == 5)
{
lean_object* v_fn_1061_; 
v_fn_1061_ = lean_ctor_get(v___x_1060_, 0);
lean_inc_ref(v_fn_1061_);
lean_dec_ref(v___x_1060_);
if (lean_obj_tag(v_fn_1061_) == 5)
{
lean_object* v_fn_1062_; 
v_fn_1062_ = lean_ctor_get(v_fn_1061_, 0);
lean_inc_ref(v_fn_1062_);
if (lean_obj_tag(v_fn_1062_) == 5)
{
lean_object* v_fn_1063_; 
v_fn_1063_ = lean_ctor_get(v_fn_1062_, 0);
if (lean_obj_tag(v_fn_1063_) == 4)
{
lean_object* v_declName_1064_; 
v_declName_1064_ = lean_ctor_get(v_fn_1063_, 0);
lean_inc(v_declName_1064_);
if (lean_obj_tag(v_declName_1064_) == 1)
{
lean_object* v_pre_1065_; 
v_pre_1065_ = lean_ctor_get(v_declName_1064_, 0);
lean_inc(v_pre_1065_);
if (lean_obj_tag(v_pre_1065_) == 1)
{
lean_object* v_pre_1066_; 
v_pre_1066_ = lean_ctor_get(v_pre_1065_, 0);
if (lean_obj_tag(v_pre_1066_) == 0)
{
lean_object* v_arg_1067_; lean_object* v_arg_1068_; lean_object* v_str_1069_; lean_object* v_str_1070_; lean_object* v___x_1071_; uint8_t v___x_1072_; 
v_arg_1067_ = lean_ctor_get(v_fn_1061_, 1);
lean_inc_ref(v_arg_1067_);
lean_dec_ref(v_fn_1061_);
v_arg_1068_ = lean_ctor_get(v_fn_1062_, 1);
lean_inc_ref(v_arg_1068_);
lean_dec_ref(v_fn_1062_);
v_str_1069_ = lean_ctor_get(v_declName_1064_, 1);
lean_inc_ref(v_str_1069_);
lean_dec_ref(v_declName_1064_);
v_str_1070_ = lean_ctor_get(v_pre_1065_, 1);
lean_inc_ref(v_str_1070_);
lean_dec_ref(v_pre_1065_);
v___x_1071_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__3));
v___x_1072_ = lean_string_dec_eq(v_str_1070_, v___x_1071_);
lean_dec_ref(v_str_1070_);
if (v___x_1072_ == 0)
{
lean_object* v___x_1073_; 
lean_dec_ref(v_str_1069_);
lean_dec_ref(v_arg_1068_);
lean_dec_ref(v_arg_1067_);
v___x_1073_ = lean_box(0);
return v___x_1073_;
}
else
{
lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1074_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__4));
v___x_1075_ = lean_string_dec_eq(v_str_1069_, v___x_1074_);
lean_dec_ref(v_str_1069_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; 
lean_dec_ref(v_arg_1068_);
lean_dec_ref(v_arg_1067_);
v___x_1076_ = lean_box(0);
return v___x_1076_;
}
else
{
if (lean_obj_tag(v_arg_1067_) == 9)
{
lean_object* v_a_1077_; 
v_a_1077_ = lean_ctor_get(v_arg_1067_, 0);
lean_inc_ref(v_a_1077_);
lean_dec_ref(v_arg_1067_);
if (lean_obj_tag(v_a_1077_) == 0)
{
lean_object* v_val_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1086_; 
v_val_1078_ = lean_ctor_get(v_a_1077_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_a_1077_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1080_ = v_a_1077_;
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_val_1078_);
lean_dec(v_a_1077_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v___x_1084_; 
v___x_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1082_, 0, v_arg_1068_);
lean_ctor_set(v___x_1082_, 1, v_val_1078_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set_tag(v___x_1080_, 1);
lean_ctor_set(v___x_1080_, 0, v___x_1082_);
v___x_1084_ = v___x_1080_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
else
{
lean_object* v___x_1087_; 
lean_dec_ref(v_a_1077_);
lean_dec_ref(v_arg_1068_);
v___x_1087_ = lean_box(0);
return v___x_1087_;
}
}
else
{
lean_object* v___x_1088_; 
lean_dec_ref(v_arg_1068_);
lean_dec_ref(v_arg_1067_);
v___x_1088_ = lean_box(0);
return v___x_1088_;
}
}
}
}
else
{
lean_object* v___x_1089_; 
lean_dec_ref(v_pre_1065_);
lean_dec_ref(v_declName_1064_);
lean_dec_ref(v_fn_1062_);
lean_dec_ref(v_fn_1061_);
v___x_1089_ = lean_box(0);
return v___x_1089_;
}
}
else
{
lean_object* v___x_1090_; 
lean_dec_ref(v_declName_1064_);
lean_dec(v_pre_1065_);
lean_dec_ref(v_fn_1062_);
lean_dec_ref(v_fn_1061_);
v___x_1090_ = lean_box(0);
return v___x_1090_;
}
}
else
{
lean_object* v___x_1091_; 
lean_dec(v_declName_1064_);
lean_dec_ref(v_fn_1062_);
lean_dec_ref(v_fn_1061_);
v___x_1091_ = lean_box(0);
return v___x_1091_;
}
}
else
{
lean_object* v___x_1092_; 
lean_dec_ref(v_fn_1062_);
lean_dec_ref(v_fn_1061_);
v___x_1092_ = lean_box(0);
return v___x_1092_;
}
}
else
{
lean_object* v___x_1093_; 
lean_dec_ref(v_fn_1061_);
lean_dec_ref(v_fn_1062_);
v___x_1093_ = lean_box(0);
return v___x_1093_;
}
}
else
{
lean_object* v___x_1094_; 
lean_dec_ref(v_fn_1061_);
v___x_1094_ = lean_box(0);
return v___x_1094_;
}
}
else
{
lean_object* v___x_1095_; 
lean_dec_ref(v___x_1060_);
v___x_1095_ = lean_box(0);
return v___x_1095_;
}
}
else
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__8, &l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__8);
return v___x_1096_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___boxed(lean_object* v_e_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_e_1097_);
lean_dec_ref(v_e_1097_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(lean_object* v_x_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
v___x_1105_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1106_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1105_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1106_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1106_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1106_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0___boxed(lean_object* v_x_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v_x_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v_x_1115_);
return v_res_1121_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; 
v___x_1123_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___closed__0));
v___x_1124_ = l_Lean_stringToMessageData(v___x_1123_);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4(lean_object* v___x_1125_, lean_object* v_expr_1126_, lean_object* v_x_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_){
_start:
{
if (lean_obj_tag(v_x_1127_) == 0)
{
lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
v_isSharedCheck_1139_ = !lean_is_exclusive(v_x_1127_);
if (v_isSharedCheck_1139_ == 0)
{
lean_object* v_unused_1140_; 
v_unused_1140_ = lean_ctor_get(v_x_1127_, 0);
lean_dec(v_unused_1140_);
v___x_1134_ = v_x_1127_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_dec(v_x_1127_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 0, v___x_1125_);
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1125_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
else
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1157_; 
v_a_1141_ = lean_ctor_get(v_x_1127_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_x_1127_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1143_ = v_x_1127_;
v_isShared_1144_ = v_isSharedCheck_1157_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v_x_1127_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1157_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v_expr_1145_; uint8_t v___x_1146_; 
v_expr_1145_ = lean_ctor_get(v_a_1141_, 0);
lean_inc_ref(v_expr_1145_);
lean_dec(v_a_1141_);
v___x_1146_ = lean_expr_eqv(v_expr_1145_, v_expr_1126_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1147_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___closed__1, &l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___closed__1);
v___x_1148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1125_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = l_Lean_MessageData_ofExpr(v_expr_1145_);
v___x_1150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1148_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set_tag(v___x_1143_, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1150_);
v___x_1152_ = v___x_1143_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
else
{
lean_object* v___x_1155_; 
lean_dec_ref(v_expr_1145_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set_tag(v___x_1143_, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1125_);
v___x_1155_ = v___x_1143_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1125_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___boxed(lean_object* v___x_1158_, lean_object* v_expr_1159_, lean_object* v_x_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_){
_start:
{
lean_object* v_res_1166_; 
v_res_1166_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4(v___x_1158_, v_expr_1159_, v_x_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1163_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec_ref(v_expr_1159_);
return v_res_1166_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0_spec__0(lean_object* v_e_1167_){
_start:
{
if (lean_obj_tag(v_e_1167_) == 0)
{
uint8_t v___x_1168_; 
v___x_1168_ = 2;
return v___x_1168_;
}
else
{
uint8_t v___x_1169_; 
v___x_1169_ = 0;
return v___x_1169_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0_spec__0___boxed(lean_object* v_e_1170_){
_start:
{
uint8_t v_res_1171_; lean_object* v_r_1172_; 
v_res_1171_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0_spec__0(v_e_1170_);
lean_dec_ref(v_e_1170_);
v_r_1172_ = lean_box(v_res_1171_);
return v_r_1172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(lean_object* v_cls_1173_, uint8_t v_collapsed_1174_, lean_object* v_tag_1175_, lean_object* v_opts_1176_, uint8_t v_clsEnabled_1177_, lean_object* v_oldTraces_1178_, lean_object* v_msg_1179_, lean_object* v_resStartStop_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_){
_start:
{
lean_object* v_fst_1186_; lean_object* v_snd_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1285_; 
v_fst_1186_ = lean_ctor_get(v_resStartStop_1180_, 0);
v_snd_1187_ = lean_ctor_get(v_resStartStop_1180_, 1);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_resStartStop_1180_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1189_ = v_resStartStop_1180_;
v_isShared_1190_ = v_isSharedCheck_1285_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_snd_1187_);
lean_inc(v_fst_1186_);
lean_dec(v_resStartStop_1180_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1285_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v_data_1194_; lean_object* v_fst_1205_; lean_object* v_snd_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1284_; 
v_fst_1205_ = lean_ctor_get(v_snd_1187_, 0);
v_snd_1206_ = lean_ctor_get(v_snd_1187_, 1);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_snd_1187_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1208_ = v_snd_1187_;
v_isShared_1209_ = v_isSharedCheck_1284_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_snd_1206_);
lean_inc(v_fst_1205_);
lean_dec(v_snd_1187_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1284_;
goto v_resetjp_1207_;
}
v___jp_1191_:
{
lean_object* v___x_1195_; 
v___x_1195_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4(v_oldTraces_1178_, v_data_1194_, v___y_1192_, v___y_1193_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_);
lean_dec(v___y_1184_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v___x_1196_; 
lean_dec_ref(v___x_1195_);
v___x_1196_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5___redArg(v_fst_1186_);
return v___x_1196_;
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_dec(v_fst_1186_);
v_a_1197_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1195_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1195_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; uint8_t v___x_1211_; lean_object* v___y_1213_; lean_object* v_a_1214_; uint8_t v___y_1238_; double v___y_1269_; 
v___x_1210_ = l_Lean_trace_profiler;
v___x_1211_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_opts_1176_, v___x_1210_);
if (v___x_1211_ == 0)
{
v___y_1238_ = v___x_1211_;
goto v___jp_1237_;
}
else
{
lean_object* v___x_1274_; uint8_t v___x_1275_; 
v___x_1274_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1275_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_opts_1176_, v___x_1274_);
if (v___x_1275_ == 0)
{
lean_object* v___x_1276_; lean_object* v___x_1277_; double v___x_1278_; double v___x_1279_; double v___x_1280_; 
v___x_1276_ = l_Lean_trace_profiler_threshold;
v___x_1277_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__6(v_opts_1176_, v___x_1276_);
v___x_1278_ = lean_float_of_nat(v___x_1277_);
v___x_1279_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__5);
v___x_1280_ = lean_float_div(v___x_1278_, v___x_1279_);
v___y_1269_ = v___x_1280_;
goto v___jp_1268_;
}
else
{
lean_object* v___x_1281_; lean_object* v___x_1282_; double v___x_1283_; 
v___x_1281_ = l_Lean_trace_profiler_threshold;
v___x_1282_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__6(v_opts_1176_, v___x_1281_);
v___x_1283_ = lean_float_of_nat(v___x_1282_);
v___y_1269_ = v___x_1283_;
goto v___jp_1268_;
}
}
v___jp_1212_:
{
uint8_t v_result_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1220_; 
v_result_1215_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0_spec__0(v_fst_1186_);
v___x_1216_ = l_Lean_TraceResult_toEmoji(v_result_1215_);
v___x_1217_ = l_Lean_stringToMessageData(v___x_1216_);
v___x_1218_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1);
if (v_isShared_1209_ == 0)
{
lean_ctor_set_tag(v___x_1208_, 7);
lean_ctor_set(v___x_1208_, 1, v___x_1218_);
lean_ctor_set(v___x_1208_, 0, v___x_1217_);
v___x_1220_ = v___x_1208_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1217_);
lean_ctor_set(v_reuseFailAlloc_1231_, 1, v___x_1218_);
v___x_1220_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v_m_1222_; 
if (v_isShared_1190_ == 0)
{
lean_ctor_set_tag(v___x_1189_, 7);
lean_ctor_set(v___x_1189_, 1, v_a_1214_);
lean_ctor_set(v___x_1189_, 0, v___x_1220_);
v_m_1222_ = v___x_1189_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1220_);
lean_ctor_set(v_reuseFailAlloc_1230_, 1, v_a_1214_);
v_m_1222_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; double v___x_1225_; lean_object* v_data_1226_; 
v___x_1223_ = lean_box(v_result_1215_);
v___x_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
v___x_1225_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2);
lean_inc_ref(v_tag_1175_);
lean_inc_ref(v___x_1224_);
lean_inc(v_cls_1173_);
v_data_1226_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1226_, 0, v_cls_1173_);
lean_ctor_set(v_data_1226_, 1, v___x_1224_);
lean_ctor_set(v_data_1226_, 2, v_tag_1175_);
lean_ctor_set_float(v_data_1226_, sizeof(void*)*3, v___x_1225_);
lean_ctor_set_float(v_data_1226_, sizeof(void*)*3 + 8, v___x_1225_);
lean_ctor_set_uint8(v_data_1226_, sizeof(void*)*3 + 16, v_collapsed_1174_);
if (v___x_1211_ == 0)
{
lean_dec_ref(v___x_1224_);
lean_dec(v_snd_1206_);
lean_dec(v_fst_1205_);
lean_dec_ref(v_tag_1175_);
lean_dec(v_cls_1173_);
v___y_1192_ = v___y_1213_;
v___y_1193_ = v_m_1222_;
v_data_1194_ = v_data_1226_;
goto v___jp_1191_;
}
else
{
lean_object* v_data_1227_; double v___x_1228_; double v___x_1229_; 
lean_dec_ref(v_data_1226_);
v_data_1227_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1227_, 0, v_cls_1173_);
lean_ctor_set(v_data_1227_, 1, v___x_1224_);
lean_ctor_set(v_data_1227_, 2, v_tag_1175_);
v___x_1228_ = lean_unbox_float(v_fst_1205_);
lean_dec(v_fst_1205_);
lean_ctor_set_float(v_data_1227_, sizeof(void*)*3, v___x_1228_);
v___x_1229_ = lean_unbox_float(v_snd_1206_);
lean_dec(v_snd_1206_);
lean_ctor_set_float(v_data_1227_, sizeof(void*)*3 + 8, v___x_1229_);
lean_ctor_set_uint8(v_data_1227_, sizeof(void*)*3 + 16, v_collapsed_1174_);
v___y_1192_ = v___y_1213_;
v___y_1193_ = v_m_1222_;
v_data_1194_ = v_data_1227_;
goto v___jp_1191_;
}
}
}
}
v___jp_1232_:
{
lean_object* v_ref_1233_; lean_object* v___x_1234_; 
v_ref_1233_ = lean_ctor_get(v___y_1183_, 5);
lean_inc(v___y_1184_);
lean_inc_ref(v___y_1183_);
lean_inc(v___y_1182_);
lean_inc_ref(v___y_1181_);
lean_inc(v_fst_1186_);
v___x_1234_ = lean_apply_6(v_msg_1179_, v_fst_1186_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, lean_box(0));
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
lean_dec_ref(v___x_1234_);
lean_inc(v_ref_1233_);
v___y_1213_ = v_ref_1233_;
v_a_1214_ = v_a_1235_;
goto v___jp_1212_;
}
else
{
lean_object* v___x_1236_; 
lean_dec_ref(v___x_1234_);
v___x_1236_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__4);
lean_inc(v_ref_1233_);
v___y_1213_ = v_ref_1233_;
v_a_1214_ = v___x_1236_;
goto v___jp_1212_;
}
}
v___jp_1237_:
{
if (v_clsEnabled_1177_ == 0)
{
if (v___y_1238_ == 0)
{
lean_object* v___x_1239_; lean_object* v_traceState_1240_; lean_object* v_env_1241_; lean_object* v_nextMacroScope_1242_; lean_object* v_ngen_1243_; lean_object* v_auxDeclNGen_1244_; lean_object* v_cache_1245_; lean_object* v_messages_1246_; lean_object* v_infoState_1247_; lean_object* v_snapshotTasks_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1267_; 
lean_del_object(v___x_1208_);
lean_dec(v_snd_1206_);
lean_dec(v_fst_1205_);
lean_del_object(v___x_1189_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v___y_1181_);
lean_dec_ref(v_msg_1179_);
lean_dec_ref(v_tag_1175_);
lean_dec(v_cls_1173_);
v___x_1239_ = lean_st_ref_take(v___y_1184_);
v_traceState_1240_ = lean_ctor_get(v___x_1239_, 4);
v_env_1241_ = lean_ctor_get(v___x_1239_, 0);
v_nextMacroScope_1242_ = lean_ctor_get(v___x_1239_, 1);
v_ngen_1243_ = lean_ctor_get(v___x_1239_, 2);
v_auxDeclNGen_1244_ = lean_ctor_get(v___x_1239_, 3);
v_cache_1245_ = lean_ctor_get(v___x_1239_, 5);
v_messages_1246_ = lean_ctor_get(v___x_1239_, 6);
v_infoState_1247_ = lean_ctor_get(v___x_1239_, 7);
v_snapshotTasks_1248_ = lean_ctor_get(v___x_1239_, 8);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1250_ = v___x_1239_;
v_isShared_1251_ = v_isSharedCheck_1267_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_snapshotTasks_1248_);
lean_inc(v_infoState_1247_);
lean_inc(v_messages_1246_);
lean_inc(v_cache_1245_);
lean_inc(v_traceState_1240_);
lean_inc(v_auxDeclNGen_1244_);
lean_inc(v_ngen_1243_);
lean_inc(v_nextMacroScope_1242_);
lean_inc(v_env_1241_);
lean_dec(v___x_1239_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1267_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
uint64_t v_tid_1252_; lean_object* v_traces_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1266_; 
v_tid_1252_ = lean_ctor_get_uint64(v_traceState_1240_, sizeof(void*)*1);
v_traces_1253_ = lean_ctor_get(v_traceState_1240_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_traceState_1240_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1255_ = v_traceState_1240_;
v_isShared_1256_ = v_isSharedCheck_1266_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_traces_1253_);
lean_dec(v_traceState_1240_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1266_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1257_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1178_, v_traces_1253_);
lean_dec_ref(v_traces_1253_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 0, v___x_1257_);
v___x_1259_ = v___x_1255_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1257_);
lean_ctor_set_uint64(v_reuseFailAlloc_1265_, sizeof(void*)*1, v_tid_1252_);
v___x_1259_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1261_; 
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 4, v___x_1259_);
v___x_1261_ = v___x_1250_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_env_1241_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_nextMacroScope_1242_);
lean_ctor_set(v_reuseFailAlloc_1264_, 2, v_ngen_1243_);
lean_ctor_set(v_reuseFailAlloc_1264_, 3, v_auxDeclNGen_1244_);
lean_ctor_set(v_reuseFailAlloc_1264_, 4, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1264_, 5, v_cache_1245_);
lean_ctor_set(v_reuseFailAlloc_1264_, 6, v_messages_1246_);
lean_ctor_set(v_reuseFailAlloc_1264_, 7, v_infoState_1247_);
lean_ctor_set(v_reuseFailAlloc_1264_, 8, v_snapshotTasks_1248_);
v___x_1261_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = lean_st_ref_set(v___y_1184_, v___x_1261_);
lean_dec(v___y_1184_);
v___x_1263_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__5___redArg(v_fst_1186_);
return v___x_1263_;
}
}
}
}
}
else
{
goto v___jp_1232_;
}
}
else
{
goto v___jp_1232_;
}
}
v___jp_1268_:
{
double v___x_1270_; double v___x_1271_; double v___x_1272_; uint8_t v___x_1273_; 
v___x_1270_ = lean_unbox_float(v_snd_1206_);
v___x_1271_ = lean_unbox_float(v_fst_1205_);
v___x_1272_ = lean_float_sub(v___x_1270_, v___x_1271_);
v___x_1273_ = lean_float_decLt(v___y_1269_, v___x_1272_);
v___y_1238_ = v___x_1273_;
goto v___jp_1237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0___boxed(lean_object* v_cls_1286_, lean_object* v_collapsed_1287_, lean_object* v_tag_1288_, lean_object* v_opts_1289_, lean_object* v_clsEnabled_1290_, lean_object* v_oldTraces_1291_, lean_object* v_msg_1292_, lean_object* v_resStartStop_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_){
_start:
{
uint8_t v_collapsed_boxed_1299_; uint8_t v_clsEnabled_boxed_1300_; lean_object* v_res_1301_; 
v_collapsed_boxed_1299_ = lean_unbox(v_collapsed_1287_);
v_clsEnabled_boxed_1300_ = lean_unbox(v_clsEnabled_1290_);
v_res_1301_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v_cls_1286_, v_collapsed_boxed_1299_, v_tag_1288_, v_opts_1289_, v_clsEnabled_boxed_1300_, v_oldTraces_1291_, v_msg_1292_, v_resStartStop_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_);
lean_dec_ref(v_opts_1289_);
return v_res_1301_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___closed__1(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_splittingProcedure___closed__0));
v___x_1304_ = l_Lean_stringToMessageData(v___x_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure(lean_object* v_expr_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_){
_start:
{
lean_object* v___y_1312_; uint8_t v___y_1313_; uint8_t v___y_1314_; uint8_t v___y_1320_; lean_object* v_a_1321_; lean_object* v___y_1325_; uint8_t v___y_1326_; uint8_t v___y_1327_; uint8_t v___y_1333_; lean_object* v_a_1334_; uint8_t v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; uint8_t v___y_1345_; lean_object* v_a_1346_; uint8_t v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___y_1363_; lean_object* v___y_1364_; lean_object* v___y_1365_; uint8_t v___y_1366_; lean_object* v_a_1367_; uint8_t v___y_1370_; lean_object* v___y_1371_; lean_object* v___y_1372_; lean_object* v___y_1373_; lean_object* v___y_1374_; lean_object* v___y_1375_; lean_object* v___y_1376_; uint8_t v___y_1377_; lean_object* v_a_1378_; uint8_t v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; uint8_t v___y_1389_; uint8_t v___y_1390_; uint8_t v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; uint8_t v___y_1401_; lean_object* v_a_1402_; uint8_t v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; uint8_t v___y_1413_; lean_object* v_a_1414_; lean_object* v___y_1417_; uint8_t v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; uint8_t v___y_1424_; lean_object* v_a_1425_; lean_object* v___y_1435_; uint8_t v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; uint8_t v___y_1442_; lean_object* v_a_1443_; lean_object* v___y_1446_; uint8_t v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; lean_object* v___y_1452_; uint8_t v___y_1453_; lean_object* v_a_1454_; lean_object* v___y_1457_; uint8_t v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___y_1462_; lean_object* v___y_1463_; lean_object* v___y_1464_; uint8_t v___y_1465_; uint8_t v___y_1466_; lean_object* v___y_1470_; uint8_t v___y_1471_; lean_object* v___y_1472_; lean_object* v___y_1473_; lean_object* v___y_1474_; lean_object* v___y_1475_; lean_object* v___y_1476_; uint8_t v___y_1477_; lean_object* v_a_1478_; lean_object* v___y_1482_; uint8_t v___y_1483_; lean_object* v___y_1484_; lean_object* v___y_1485_; lean_object* v___y_1486_; lean_object* v___y_1487_; lean_object* v___y_1488_; uint8_t v___y_1489_; lean_object* v_a_1490_; lean_object* v_a_1493_; lean_object* v_a_1503_; 
if (lean_obj_tag(v_expr_1305_) == 5)
{
lean_object* v_fn_1517_; 
v_fn_1517_ = lean_ctor_get(v_expr_1305_, 0);
if (lean_obj_tag(v_fn_1517_) == 5)
{
lean_object* v_arg_1518_; lean_object* v_fn_1519_; lean_object* v_arg_1520_; lean_object* v___x_1521_; 
v_arg_1518_ = lean_ctor_get(v_expr_1305_, 1);
v_fn_1519_ = lean_ctor_get(v_fn_1517_, 0);
v_arg_1520_ = lean_ctor_get(v_fn_1517_, 1);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_fn_1519_);
v___x_1521_ = lean_infer_type(v_fn_1519_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_2373_; 
v_a_1522_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_1524_ = v___x_1521_;
v_isShared_1525_ = v_isSharedCheck_2373_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1521_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_2373_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
if (lean_obj_tag(v_a_1522_) == 7)
{
lean_object* v_body_1533_; 
v_body_1533_ = lean_ctor_get(v_a_1522_, 2);
lean_inc_ref(v_body_1533_);
if (lean_obj_tag(v_body_1533_) == 7)
{
lean_object* v_binderType_1534_; lean_object* v_binderType_1535_; lean_object* v_body_1536_; uint8_t v___y_1538_; lean_object* v___y_1539_; uint8_t v___y_1540_; uint8_t v___y_1579_; lean_object* v_a_1580_; uint8_t v___y_1584_; lean_object* v___y_1585_; uint8_t v___y_1586_; uint8_t v___y_1623_; lean_object* v_a_1624_; uint8_t v___y_1628_; lean_object* v___y_1629_; uint8_t v___y_1632_; lean_object* v___y_1633_; lean_object* v___y_1634_; lean_object* v___y_1635_; uint8_t v___y_1636_; uint8_t v___y_1654_; lean_object* v___y_1655_; lean_object* v___y_1656_; lean_object* v_a_1657_; uint8_t v___y_1661_; lean_object* v___y_1662_; lean_object* v___y_1663_; lean_object* v___y_1664_; lean_object* v___y_1667_; uint8_t v___y_1668_; lean_object* v___y_1669_; lean_object* v___y_1670_; lean_object* v___y_1671_; lean_object* v___y_1672_; lean_object* v___y_1673_; lean_object* v___y_1674_; uint8_t v___y_1675_; uint8_t v___y_1676_; lean_object* v___y_1715_; uint8_t v___y_1716_; lean_object* v___y_1717_; lean_object* v___y_1718_; lean_object* v___y_1719_; lean_object* v___y_1720_; lean_object* v___y_1721_; uint8_t v___y_1722_; lean_object* v_a_1723_; lean_object* v___y_1727_; uint8_t v___y_1728_; lean_object* v___y_1729_; lean_object* v___y_1730_; lean_object* v___y_1731_; lean_object* v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; uint8_t v___y_1735_; uint8_t v___y_1736_; lean_object* v___y_1773_; uint8_t v___y_1774_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___y_1779_; uint8_t v___y_1780_; lean_object* v_a_1781_; lean_object* v___y_1785_; uint8_t v___y_1786_; lean_object* v___y_1787_; lean_object* v___y_1788_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; uint8_t v___y_1792_; lean_object* v___y_1793_; lean_object* v___y_1797_; uint8_t v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; uint8_t v___y_1806_; lean_object* v___y_1807_; uint8_t v___y_1808_; lean_object* v___y_1826_; uint8_t v___y_1827_; lean_object* v___y_1828_; lean_object* v___y_1829_; lean_object* v___y_1830_; lean_object* v___y_1831_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1834_; uint8_t v___y_1835_; lean_object* v_a_1836_; lean_object* v___y_1840_; uint8_t v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; uint8_t v___y_1849_; lean_object* v___y_1850_; uint8_t v___y_1854_; lean_object* v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; uint8_t v___y_1862_; uint8_t v___y_1863_; uint8_t v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; uint8_t v___y_1909_; lean_object* v_a_1910_; uint8_t v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; uint8_t v___y_1921_; lean_object* v___y_1922_; uint8_t v___y_1923_; uint8_t v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; uint8_t v___y_1967_; lean_object* v_a_1968_; uint8_t v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; uint8_t v___y_1979_; lean_object* v___y_1980_; lean_object* v___y_1984_; uint8_t v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; uint8_t v___y_1994_; uint8_t v___y_1995_; uint8_t v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; uint8_t v___y_2022_; lean_object* v_a_2023_; uint8_t v___y_2027_; lean_object* v___y_2028_; lean_object* v___y_2029_; lean_object* v___y_2030_; lean_object* v___y_2031_; lean_object* v___y_2032_; lean_object* v___y_2033_; lean_object* v___y_2034_; lean_object* v___y_2035_; uint8_t v___y_2036_; lean_object* v___y_2037_; uint8_t v___y_2041_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; uint8_t v___y_2046_; uint8_t v___y_2128_; lean_object* v___y_2129_; uint8_t v___y_2130_; uint8_t v___y_2169_; lean_object* v_a_2170_; uint8_t v___y_2174_; lean_object* v___y_2175_; uint8_t v___y_2176_; uint8_t v___y_2213_; lean_object* v_a_2214_; uint8_t v___y_2218_; lean_object* v___y_2219_; lean_object* v___y_2222_; uint8_t v___y_2223_; lean_object* v___y_2224_; lean_object* v___y_2225_; uint8_t v___y_2226_; lean_object* v___y_2244_; uint8_t v___y_2245_; lean_object* v___y_2246_; lean_object* v_a_2247_; lean_object* v___y_2251_; uint8_t v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; uint8_t v___y_2257_; uint8_t v___x_2371_; 
lean_del_object(v___x_1524_);
v_binderType_1534_ = lean_ctor_get(v_a_1522_, 1);
lean_inc_ref(v_binderType_1534_);
lean_dec_ref(v_a_1522_);
v_binderType_1535_ = lean_ctor_get(v_body_1533_, 1);
lean_inc_ref(v_binderType_1535_);
v_body_1536_ = lean_ctor_get(v_body_1533_, 2);
lean_inc_ref(v_body_1536_);
lean_dec_ref(v_body_1533_);
v___x_2371_ = l_Lean_Expr_hasLooseBVars(v_binderType_1535_);
if (v___x_2371_ == 0)
{
uint8_t v___x_2372_; 
v___x_2372_ = l_Lean_Expr_hasLooseBVars(v_body_1536_);
lean_dec_ref(v_body_1536_);
v___y_2257_ = v___x_2372_;
goto v___jp_2256_;
}
else
{
lean_dec_ref(v_body_1536_);
v___y_2257_ = v___x_2371_;
goto v___jp_2256_;
}
v___jp_1537_:
{
if (v___y_1540_ == 0)
{
lean_object* v___x_1541_; 
lean_dec_ref(v___y_1539_);
v___x_1541_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1520_);
if (lean_obj_tag(v___x_1541_) == 1)
{
lean_object* v_val_1542_; lean_object* v_snd_1543_; lean_object* v___x_1544_; 
v_val_1542_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_val_1542_);
lean_dec_ref(v___x_1541_);
v_snd_1543_ = lean_ctor_get(v_val_1542_, 1);
lean_inc(v_snd_1543_);
lean_dec(v_val_1542_);
v___x_1544_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1518_, v_a_1309_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref(v___x_1544_);
if (lean_obj_tag(v_a_1545_) == 1)
{
lean_object* v_val_1546_; lean_object* v___x_1547_; 
v_val_1546_ = lean_ctor_get(v_a_1545_, 0);
lean_inc(v_val_1546_);
lean_dec_ref(v_a_1545_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1547_ = lean_infer_type(v_val_1546_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1549_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1548_);
lean_dec_ref(v___x_1547_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1549_ = l_Lean_Meta_mkNumeral(v_a_1548_, v_snd_1543_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1551_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1550_);
lean_dec_ref(v___x_1549_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1551_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1550_, v_binderType_1534_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1551_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1553_; 
v_a_1552_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1552_);
lean_dec_ref(v___x_1551_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_arg_1520_);
v___x_1553_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1520_, v_a_1552_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref(v___x_1553_);
if (lean_obj_tag(v_a_1554_) == 1)
{
lean_object* v_val_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; 
v_val_1555_ = lean_ctor_get(v_a_1554_, 0);
lean_inc(v_val_1555_);
lean_dec_ref(v_a_1554_);
v___x_1556_ = lean_box(0);
lean_inc_ref(v_fn_1519_);
v___x_1557_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1557_, 0, v_fn_1519_);
lean_ctor_set(v___x_1557_, 1, v___x_1556_);
lean_ctor_set_uint8(v___x_1557_, sizeof(void*)*2, v___y_1538_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1558_ = l_Lean_Meta_Simp_mkCongr(v___x_1557_, v_val_1555_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1560_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1559_);
lean_dec_ref(v___x_1558_);
lean_inc_ref(v_arg_1518_);
v___x_1560_ = l_Lean_Meta_Simp_mkCongrFun(v_a_1559_, v_arg_1518_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1560_) == 0)
{
lean_dec_ref(v_expr_1305_);
return v___x_1560_;
}
else
{
lean_object* v_a_1561_; 
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref(v___x_1560_);
v___y_1333_ = v___y_1538_;
v_a_1334_ = v_a_1561_;
goto v___jp_1332_;
}
}
else
{
lean_object* v_a_1562_; 
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v_a_1562_ = lean_ctor_get(v___x_1558_, 0);
lean_inc(v_a_1562_);
lean_dec_ref(v___x_1558_);
v___y_1333_ = v___y_1538_;
v_a_1334_ = v_a_1562_;
goto v___jp_1332_;
}
}
else
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v_a_1565_; 
lean_dec(v_a_1554_);
v___x_1563_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1564_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1563_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref(v___x_1564_);
v___y_1333_ = v___y_1538_;
v_a_1334_ = v_a_1565_;
goto v___jp_1332_;
}
}
else
{
lean_object* v_a_1566_; 
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v_a_1566_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1566_);
lean_dec_ref(v___x_1553_);
v___y_1333_ = v___y_1538_;
v_a_1334_ = v_a_1566_;
goto v___jp_1332_;
}
}
else
{
lean_object* v_a_1567_; 
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v_a_1567_ = lean_ctor_get(v___x_1551_, 0);
lean_inc(v_a_1567_);
lean_dec_ref(v___x_1551_);
v___y_1333_ = v___y_1538_;
v_a_1334_ = v_a_1567_;
goto v___jp_1332_;
}
}
else
{
lean_object* v_a_1568_; 
lean_dec_ref(v_binderType_1534_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v_a_1568_ = lean_ctor_get(v___x_1549_, 0);
lean_inc(v_a_1568_);
lean_dec_ref(v___x_1549_);
v___y_1333_ = v___y_1538_;
v_a_1334_ = v_a_1568_;
goto v___jp_1332_;
}
}
else
{
lean_object* v_a_1569_; 
lean_dec(v_snd_1543_);
lean_dec_ref(v_binderType_1534_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v_a_1569_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_a_1569_);
lean_dec_ref(v___x_1547_);
v___y_1333_ = v___y_1538_;
v_a_1334_ = v_a_1569_;
goto v___jp_1332_;
}
}
else
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v_a_1572_; 
lean_dec(v_a_1545_);
lean_dec(v_snd_1543_);
lean_dec_ref(v_binderType_1534_);
v___x_1570_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1571_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1570_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1572_);
lean_dec_ref(v___x_1571_);
v___y_1333_ = v___y_1538_;
v_a_1334_ = v_a_1572_;
goto v___jp_1332_;
}
}
else
{
lean_object* v_a_1573_; 
lean_dec(v_snd_1543_);
lean_dec_ref(v_binderType_1534_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v_a_1573_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1573_);
lean_dec_ref(v___x_1544_);
v___y_1333_ = v___y_1538_;
v_a_1334_ = v_a_1573_;
goto v___jp_1332_;
}
}
else
{
lean_object* v___x_1574_; 
lean_dec_ref(v_binderType_1534_);
v___x_1574_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1541_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec(v___x_1541_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v_a_1575_; 
lean_dec_ref(v_expr_1305_);
v_a_1575_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1575_);
lean_dec_ref(v___x_1574_);
v_a_1503_ = v_a_1575_;
goto v___jp_1502_;
}
else
{
lean_object* v_a_1576_; 
v_a_1576_ = lean_ctor_get(v___x_1574_, 0);
lean_inc(v_a_1576_);
lean_dec_ref(v___x_1574_);
v___y_1333_ = v___y_1538_;
v_a_1334_ = v_a_1576_;
goto v___jp_1332_;
}
}
}
else
{
lean_object* v___x_1577_; 
lean_dec_ref(v_binderType_1534_);
lean_dec_ref(v_expr_1305_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v___x_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1577_, 0, v___y_1539_);
return v___x_1577_;
}
}
v___jp_1578_:
{
uint8_t v___x_1581_; 
v___x_1581_ = l_Lean_Exception_isInterrupt(v_a_1580_);
if (v___x_1581_ == 0)
{
uint8_t v___x_1582_; 
lean_inc_ref(v_a_1580_);
v___x_1582_ = l_Lean_Exception_isRuntime(v_a_1580_);
v___y_1538_ = v___y_1579_;
v___y_1539_ = v_a_1580_;
v___y_1540_ = v___x_1582_;
goto v___jp_1537_;
}
else
{
v___y_1538_ = v___y_1579_;
v___y_1539_ = v_a_1580_;
v___y_1540_ = v___x_1581_;
goto v___jp_1537_;
}
}
v___jp_1583_:
{
if (v___y_1586_ == 0)
{
lean_object* v___x_1587_; 
lean_dec_ref(v___y_1585_);
v___x_1587_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1518_);
if (lean_obj_tag(v___x_1587_) == 1)
{
lean_object* v_val_1588_; lean_object* v_snd_1589_; lean_object* v___x_1590_; 
v_val_1588_ = lean_ctor_get(v___x_1587_, 0);
lean_inc(v_val_1588_);
lean_dec_ref(v___x_1587_);
v_snd_1589_ = lean_ctor_get(v_val_1588_, 1);
lean_inc(v_snd_1589_);
lean_dec(v_val_1588_);
v___x_1590_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1520_, v_a_1309_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref(v___x_1590_);
if (lean_obj_tag(v_a_1591_) == 1)
{
lean_object* v_val_1592_; lean_object* v___x_1593_; 
v_val_1592_ = lean_ctor_get(v_a_1591_, 0);
lean_inc(v_val_1592_);
lean_dec_ref(v_a_1591_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1593_ = lean_infer_type(v_val_1592_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v___x_1595_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1594_);
lean_dec_ref(v___x_1593_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1595_ = l_Lean_Meta_mkNumeral(v_a_1594_, v_snd_1589_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1595_) == 0)
{
lean_object* v_a_1596_; lean_object* v___x_1597_; 
v_a_1596_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1596_);
lean_dec_ref(v___x_1595_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_binderType_1534_);
v___x_1597_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1596_, v_binderType_1534_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v___x_1599_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1598_);
lean_dec_ref(v___x_1597_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_arg_1518_);
v___x_1599_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1518_, v_a_1598_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1599_) == 0)
{
lean_object* v_a_1600_; 
v_a_1600_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1600_);
lean_dec_ref(v___x_1599_);
if (lean_obj_tag(v_a_1600_) == 1)
{
lean_object* v_val_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; 
v_val_1601_ = lean_ctor_get(v_a_1600_, 0);
lean_inc(v_val_1601_);
lean_dec_ref(v_a_1600_);
lean_inc_ref(v_arg_1520_);
lean_inc_ref(v_fn_1519_);
v___x_1602_ = l_Lean_Expr_app___override(v_fn_1519_, v_arg_1520_);
v___x_1603_ = lean_box(0);
v___x_1604_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1604_, 0, v___x_1602_);
lean_ctor_set(v___x_1604_, 1, v___x_1603_);
lean_ctor_set_uint8(v___x_1604_, sizeof(void*)*2, v___y_1584_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1605_ = l_Lean_Meta_Simp_mkCongr(v___x_1604_, v_val_1601_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_dec_ref(v_binderType_1534_);
lean_dec_ref(v_expr_1305_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
return v___x_1605_;
}
else
{
lean_object* v_a_1606_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_a_1606_);
lean_dec_ref(v___x_1605_);
v___y_1579_ = v___y_1584_;
v_a_1580_ = v_a_1606_;
goto v___jp_1578_;
}
}
else
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v_a_1609_; 
lean_dec(v_a_1600_);
v___x_1607_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1608_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1607_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_a_1609_);
lean_dec_ref(v___x_1608_);
v___y_1579_ = v___y_1584_;
v_a_1580_ = v_a_1609_;
goto v___jp_1578_;
}
}
else
{
lean_object* v_a_1610_; 
v_a_1610_ = lean_ctor_get(v___x_1599_, 0);
lean_inc(v_a_1610_);
lean_dec_ref(v___x_1599_);
v___y_1579_ = v___y_1584_;
v_a_1580_ = v_a_1610_;
goto v___jp_1578_;
}
}
else
{
lean_object* v_a_1611_; 
v_a_1611_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1611_);
lean_dec_ref(v___x_1597_);
v___y_1579_ = v___y_1584_;
v_a_1580_ = v_a_1611_;
goto v___jp_1578_;
}
}
else
{
lean_object* v_a_1612_; 
v_a_1612_ = lean_ctor_get(v___x_1595_, 0);
lean_inc(v_a_1612_);
lean_dec_ref(v___x_1595_);
v___y_1579_ = v___y_1584_;
v_a_1580_ = v_a_1612_;
goto v___jp_1578_;
}
}
else
{
lean_object* v_a_1613_; 
lean_dec(v_snd_1589_);
v_a_1613_ = lean_ctor_get(v___x_1593_, 0);
lean_inc(v_a_1613_);
lean_dec_ref(v___x_1593_);
v___y_1579_ = v___y_1584_;
v_a_1580_ = v_a_1613_;
goto v___jp_1578_;
}
}
else
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v_a_1616_; 
lean_dec(v_a_1591_);
lean_dec(v_snd_1589_);
v___x_1614_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1615_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1614_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_a_1616_);
lean_dec_ref(v___x_1615_);
v___y_1579_ = v___y_1584_;
v_a_1580_ = v_a_1616_;
goto v___jp_1578_;
}
}
else
{
lean_object* v_a_1617_; 
lean_dec(v_snd_1589_);
v_a_1617_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1617_);
lean_dec_ref(v___x_1590_);
v___y_1579_ = v___y_1584_;
v_a_1580_ = v_a_1617_;
goto v___jp_1578_;
}
}
else
{
lean_object* v___x_1618_; 
v___x_1618_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1587_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v___x_1587_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; 
lean_dec_ref(v_binderType_1534_);
lean_dec_ref(v_expr_1305_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1619_);
lean_dec_ref(v___x_1618_);
v_a_1503_ = v_a_1619_;
goto v___jp_1502_;
}
else
{
lean_object* v_a_1620_; 
v_a_1620_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1620_);
lean_dec_ref(v___x_1618_);
v___y_1579_ = v___y_1584_;
v_a_1580_ = v_a_1620_;
goto v___jp_1578_;
}
}
}
else
{
lean_object* v___x_1621_; 
lean_dec_ref(v_binderType_1534_);
lean_dec_ref(v_expr_1305_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v___x_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1621_, 0, v___y_1585_);
return v___x_1621_;
}
}
v___jp_1622_:
{
uint8_t v___x_1625_; 
v___x_1625_ = l_Lean_Exception_isInterrupt(v_a_1624_);
if (v___x_1625_ == 0)
{
uint8_t v___x_1626_; 
lean_inc_ref(v_a_1624_);
v___x_1626_ = l_Lean_Exception_isRuntime(v_a_1624_);
v___y_1584_ = v___y_1623_;
v___y_1585_ = v_a_1624_;
v___y_1586_ = v___x_1626_;
goto v___jp_1583_;
}
else
{
v___y_1584_ = v___y_1623_;
v___y_1585_ = v_a_1624_;
v___y_1586_ = v___x_1625_;
goto v___jp_1583_;
}
}
v___jp_1627_:
{
if (lean_obj_tag(v___y_1629_) == 0)
{
lean_dec_ref(v_binderType_1534_);
lean_dec_ref(v_expr_1305_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
return v___y_1629_;
}
else
{
lean_object* v_a_1630_; 
v_a_1630_ = lean_ctor_get(v___y_1629_, 0);
lean_inc(v_a_1630_);
lean_dec_ref(v___y_1629_);
v___y_1623_ = v___y_1628_;
v_a_1624_ = v_a_1630_;
goto v___jp_1622_;
}
}
v___jp_1631_:
{
if (v___y_1636_ == 0)
{
lean_object* v___x_1637_; 
lean_dec_ref(v___y_1633_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1637_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v___y_1635_, v___y_1634_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1639_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1638_);
lean_dec_ref(v___x_1637_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_binderType_1534_);
v___x_1639_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1638_, v_binderType_1534_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_object* v_a_1640_; lean_object* v___x_1641_; 
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1640_);
lean_dec_ref(v___x_1639_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_arg_1518_);
v___x_1641_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1518_, v_a_1640_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1642_);
lean_dec_ref(v___x_1641_);
if (lean_obj_tag(v_a_1642_) == 1)
{
lean_object* v_val_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v_val_1643_ = lean_ctor_get(v_a_1642_, 0);
lean_inc(v_val_1643_);
lean_dec_ref(v_a_1642_);
lean_inc_ref(v_arg_1520_);
lean_inc_ref(v_fn_1519_);
v___x_1644_ = l_Lean_Expr_app___override(v_fn_1519_, v_arg_1520_);
v___x_1645_ = lean_box(0);
v___x_1646_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1646_, 0, v___x_1644_);
lean_ctor_set(v___x_1646_, 1, v___x_1645_);
lean_ctor_set_uint8(v___x_1646_, sizeof(void*)*2, v___y_1632_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1647_ = l_Lean_Meta_Simp_mkCongr(v___x_1646_, v_val_1643_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1628_ = v___y_1632_;
v___y_1629_ = v___x_1647_;
goto v___jp_1627_;
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
lean_dec(v_a_1642_);
v___x_1648_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1649_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1648_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1628_ = v___y_1632_;
v___y_1629_ = v___x_1649_;
goto v___jp_1627_;
}
}
else
{
lean_object* v_a_1650_; 
v_a_1650_ = lean_ctor_get(v___x_1641_, 0);
lean_inc(v_a_1650_);
lean_dec_ref(v___x_1641_);
v___y_1623_ = v___y_1632_;
v_a_1624_ = v_a_1650_;
goto v___jp_1622_;
}
}
else
{
lean_object* v_a_1651_; 
v_a_1651_ = lean_ctor_get(v___x_1639_, 0);
lean_inc(v_a_1651_);
lean_dec_ref(v___x_1639_);
v___y_1623_ = v___y_1632_;
v_a_1624_ = v_a_1651_;
goto v___jp_1622_;
}
}
else
{
lean_object* v_a_1652_; 
v_a_1652_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_a_1652_);
lean_dec_ref(v___x_1637_);
v___y_1623_ = v___y_1632_;
v_a_1624_ = v_a_1652_;
goto v___jp_1622_;
}
}
else
{
lean_dec_ref(v___y_1635_);
lean_dec_ref(v___y_1634_);
v___y_1623_ = v___y_1632_;
v_a_1624_ = v___y_1633_;
goto v___jp_1622_;
}
}
v___jp_1653_:
{
uint8_t v___x_1658_; 
v___x_1658_ = l_Lean_Exception_isInterrupt(v_a_1657_);
if (v___x_1658_ == 0)
{
uint8_t v___x_1659_; 
lean_inc_ref(v_a_1657_);
v___x_1659_ = l_Lean_Exception_isRuntime(v_a_1657_);
v___y_1632_ = v___y_1654_;
v___y_1633_ = v_a_1657_;
v___y_1634_ = v___y_1655_;
v___y_1635_ = v___y_1656_;
v___y_1636_ = v___x_1659_;
goto v___jp_1631_;
}
else
{
v___y_1632_ = v___y_1654_;
v___y_1633_ = v_a_1657_;
v___y_1634_ = v___y_1655_;
v___y_1635_ = v___y_1656_;
v___y_1636_ = v___x_1658_;
goto v___jp_1631_;
}
}
v___jp_1660_:
{
if (lean_obj_tag(v___y_1664_) == 0)
{
lean_dec_ref(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec_ref(v_binderType_1534_);
lean_dec_ref(v_expr_1305_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
return v___y_1664_;
}
else
{
lean_object* v_a_1665_; 
v_a_1665_ = lean_ctor_get(v___y_1664_, 0);
lean_inc(v_a_1665_);
lean_dec_ref(v___y_1664_);
v___y_1654_ = v___y_1661_;
v___y_1655_ = v___y_1662_;
v___y_1656_ = v___y_1663_;
v_a_1657_ = v_a_1665_;
goto v___jp_1653_;
}
}
v___jp_1666_:
{
if (v___y_1676_ == 0)
{
lean_object* v___x_1677_; 
lean_dec_ref(v___y_1669_);
v___x_1677_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1520_);
if (lean_obj_tag(v___x_1677_) == 1)
{
lean_object* v_val_1678_; lean_object* v_snd_1679_; lean_object* v___x_1680_; 
v_val_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_val_1678_);
lean_dec_ref(v___x_1677_);
v_snd_1679_ = lean_ctor_get(v_val_1678_, 1);
lean_inc(v_snd_1679_);
lean_dec(v_val_1678_);
v___x_1680_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1518_, v_a_1309_);
if (lean_obj_tag(v___x_1680_) == 0)
{
lean_object* v_a_1681_; 
v_a_1681_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1681_);
lean_dec_ref(v___x_1680_);
if (lean_obj_tag(v_a_1681_) == 1)
{
lean_object* v_val_1682_; lean_object* v___x_1683_; 
v_val_1682_ = lean_ctor_get(v_a_1681_, 0);
lean_inc(v_val_1682_);
lean_dec_ref(v_a_1681_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1683_ = lean_infer_type(v_val_1682_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_object* v_a_1684_; lean_object* v___x_1685_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1684_);
lean_dec_ref(v___x_1683_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1685_ = l_Lean_Meta_mkNumeral(v_a_1684_, v_snd_1679_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1687_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_a_1686_);
lean_dec_ref(v___x_1685_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1687_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1686_, v_binderType_1534_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1689_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1688_);
lean_dec_ref(v___x_1687_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_arg_1520_);
v___x_1689_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1520_, v_a_1688_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1690_);
lean_dec_ref(v___x_1689_);
if (lean_obj_tag(v_a_1690_) == 1)
{
lean_object* v_val_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v_val_1691_ = lean_ctor_get(v_a_1690_, 0);
lean_inc(v_val_1691_);
lean_dec_ref(v_a_1690_);
v___x_1692_ = lean_box(0);
lean_inc_ref(v_fn_1519_);
v___x_1693_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1693_, 0, v_fn_1519_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
lean_ctor_set_uint8(v___x_1693_, sizeof(void*)*2, v___y_1668_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1694_ = l_Lean_Meta_Simp_mkCongr(v___x_1693_, v_val_1691_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; lean_object* v___x_1696_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1695_);
lean_dec_ref(v___x_1694_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_arg_1518_);
v___x_1696_ = l_Lean_Meta_Simp_mkCongrFun(v_a_1695_, v_arg_1518_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; 
lean_dec_ref(v_expr_1305_);
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1697_);
lean_dec_ref(v___x_1696_);
v___y_1446_ = v___y_1667_;
v___y_1447_ = v___y_1668_;
v___y_1448_ = v___y_1670_;
v___y_1449_ = v___y_1671_;
v___y_1450_ = v___y_1672_;
v___y_1451_ = v___y_1673_;
v___y_1452_ = v___y_1674_;
v___y_1453_ = v___y_1675_;
v_a_1454_ = v_a_1697_;
goto v___jp_1445_;
}
else
{
lean_object* v_a_1698_; 
v_a_1698_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1698_);
lean_dec_ref(v___x_1696_);
v___y_1470_ = v___y_1667_;
v___y_1471_ = v___y_1668_;
v___y_1472_ = v___y_1670_;
v___y_1473_ = v___y_1671_;
v___y_1474_ = v___y_1672_;
v___y_1475_ = v___y_1673_;
v___y_1476_ = v___y_1674_;
v___y_1477_ = v___y_1675_;
v_a_1478_ = v_a_1698_;
goto v___jp_1469_;
}
}
else
{
lean_object* v_a_1699_; 
v_a_1699_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1699_);
lean_dec_ref(v___x_1694_);
v___y_1470_ = v___y_1667_;
v___y_1471_ = v___y_1668_;
v___y_1472_ = v___y_1670_;
v___y_1473_ = v___y_1671_;
v___y_1474_ = v___y_1672_;
v___y_1475_ = v___y_1673_;
v___y_1476_ = v___y_1674_;
v___y_1477_ = v___y_1675_;
v_a_1478_ = v_a_1699_;
goto v___jp_1469_;
}
}
else
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v_a_1702_; 
lean_dec(v_a_1690_);
v___x_1700_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1701_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1700_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_a_1702_);
lean_dec_ref(v___x_1701_);
v___y_1470_ = v___y_1667_;
v___y_1471_ = v___y_1668_;
v___y_1472_ = v___y_1670_;
v___y_1473_ = v___y_1671_;
v___y_1474_ = v___y_1672_;
v___y_1475_ = v___y_1673_;
v___y_1476_ = v___y_1674_;
v___y_1477_ = v___y_1675_;
v_a_1478_ = v_a_1702_;
goto v___jp_1469_;
}
}
else
{
lean_object* v_a_1703_; 
v_a_1703_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1703_);
lean_dec_ref(v___x_1689_);
v___y_1470_ = v___y_1667_;
v___y_1471_ = v___y_1668_;
v___y_1472_ = v___y_1670_;
v___y_1473_ = v___y_1671_;
v___y_1474_ = v___y_1672_;
v___y_1475_ = v___y_1673_;
v___y_1476_ = v___y_1674_;
v___y_1477_ = v___y_1675_;
v_a_1478_ = v_a_1703_;
goto v___jp_1469_;
}
}
else
{
lean_object* v_a_1704_; 
v_a_1704_ = lean_ctor_get(v___x_1687_, 0);
lean_inc(v_a_1704_);
lean_dec_ref(v___x_1687_);
v___y_1470_ = v___y_1667_;
v___y_1471_ = v___y_1668_;
v___y_1472_ = v___y_1670_;
v___y_1473_ = v___y_1671_;
v___y_1474_ = v___y_1672_;
v___y_1475_ = v___y_1673_;
v___y_1476_ = v___y_1674_;
v___y_1477_ = v___y_1675_;
v_a_1478_ = v_a_1704_;
goto v___jp_1469_;
}
}
else
{
lean_object* v_a_1705_; 
lean_dec_ref(v_binderType_1534_);
v_a_1705_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_a_1705_);
lean_dec_ref(v___x_1685_);
v___y_1470_ = v___y_1667_;
v___y_1471_ = v___y_1668_;
v___y_1472_ = v___y_1670_;
v___y_1473_ = v___y_1671_;
v___y_1474_ = v___y_1672_;
v___y_1475_ = v___y_1673_;
v___y_1476_ = v___y_1674_;
v___y_1477_ = v___y_1675_;
v_a_1478_ = v_a_1705_;
goto v___jp_1469_;
}
}
else
{
lean_object* v_a_1706_; 
lean_dec(v_snd_1679_);
lean_dec_ref(v_binderType_1534_);
v_a_1706_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1706_);
lean_dec_ref(v___x_1683_);
v___y_1470_ = v___y_1667_;
v___y_1471_ = v___y_1668_;
v___y_1472_ = v___y_1670_;
v___y_1473_ = v___y_1671_;
v___y_1474_ = v___y_1672_;
v___y_1475_ = v___y_1673_;
v___y_1476_ = v___y_1674_;
v___y_1477_ = v___y_1675_;
v_a_1478_ = v_a_1706_;
goto v___jp_1469_;
}
}
else
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v_a_1709_; 
lean_dec(v_a_1681_);
lean_dec(v_snd_1679_);
lean_dec_ref(v_binderType_1534_);
v___x_1707_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1708_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1707_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
lean_inc(v_a_1709_);
lean_dec_ref(v___x_1708_);
v___y_1470_ = v___y_1667_;
v___y_1471_ = v___y_1668_;
v___y_1472_ = v___y_1670_;
v___y_1473_ = v___y_1671_;
v___y_1474_ = v___y_1672_;
v___y_1475_ = v___y_1673_;
v___y_1476_ = v___y_1674_;
v___y_1477_ = v___y_1675_;
v_a_1478_ = v_a_1709_;
goto v___jp_1469_;
}
}
else
{
lean_object* v_a_1710_; 
lean_dec(v_snd_1679_);
lean_dec_ref(v_binderType_1534_);
v_a_1710_ = lean_ctor_get(v___x_1680_, 0);
lean_inc(v_a_1710_);
lean_dec_ref(v___x_1680_);
v___y_1470_ = v___y_1667_;
v___y_1471_ = v___y_1668_;
v___y_1472_ = v___y_1670_;
v___y_1473_ = v___y_1671_;
v___y_1474_ = v___y_1672_;
v___y_1475_ = v___y_1673_;
v___y_1476_ = v___y_1674_;
v___y_1477_ = v___y_1675_;
v_a_1478_ = v_a_1710_;
goto v___jp_1469_;
}
}
else
{
lean_object* v___x_1711_; 
lean_dec_ref(v_binderType_1534_);
v___x_1711_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1677_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v___x_1677_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; 
lean_dec_ref(v_expr_1305_);
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_a_1712_);
lean_dec_ref(v___x_1711_);
v___y_1482_ = v___y_1667_;
v___y_1483_ = v___y_1668_;
v___y_1484_ = v___y_1670_;
v___y_1485_ = v___y_1671_;
v___y_1486_ = v___y_1672_;
v___y_1487_ = v___y_1673_;
v___y_1488_ = v___y_1674_;
v___y_1489_ = v___y_1675_;
v_a_1490_ = v_a_1712_;
goto v___jp_1481_;
}
else
{
lean_object* v_a_1713_; 
v_a_1713_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_a_1713_);
lean_dec_ref(v___x_1711_);
v___y_1470_ = v___y_1667_;
v___y_1471_ = v___y_1668_;
v___y_1472_ = v___y_1670_;
v___y_1473_ = v___y_1671_;
v___y_1474_ = v___y_1672_;
v___y_1475_ = v___y_1673_;
v___y_1476_ = v___y_1674_;
v___y_1477_ = v___y_1675_;
v_a_1478_ = v_a_1713_;
goto v___jp_1469_;
}
}
}
else
{
lean_dec_ref(v_binderType_1534_);
lean_dec_ref(v_expr_1305_);
v___y_1435_ = v___y_1667_;
v___y_1436_ = v___y_1668_;
v___y_1437_ = v___y_1670_;
v___y_1438_ = v___y_1671_;
v___y_1439_ = v___y_1672_;
v___y_1440_ = v___y_1673_;
v___y_1441_ = v___y_1674_;
v___y_1442_ = v___y_1675_;
v_a_1443_ = v___y_1669_;
goto v___jp_1434_;
}
}
v___jp_1714_:
{
uint8_t v___x_1724_; 
v___x_1724_ = l_Lean_Exception_isInterrupt(v_a_1723_);
if (v___x_1724_ == 0)
{
uint8_t v___x_1725_; 
lean_inc_ref(v_a_1723_);
v___x_1725_ = l_Lean_Exception_isRuntime(v_a_1723_);
v___y_1667_ = v___y_1715_;
v___y_1668_ = v___y_1716_;
v___y_1669_ = v_a_1723_;
v___y_1670_ = v___y_1717_;
v___y_1671_ = v___y_1718_;
v___y_1672_ = v___y_1719_;
v___y_1673_ = v___y_1720_;
v___y_1674_ = v___y_1721_;
v___y_1675_ = v___y_1722_;
v___y_1676_ = v___x_1725_;
goto v___jp_1666_;
}
else
{
v___y_1667_ = v___y_1715_;
v___y_1668_ = v___y_1716_;
v___y_1669_ = v_a_1723_;
v___y_1670_ = v___y_1717_;
v___y_1671_ = v___y_1718_;
v___y_1672_ = v___y_1719_;
v___y_1673_ = v___y_1720_;
v___y_1674_ = v___y_1721_;
v___y_1675_ = v___y_1722_;
v___y_1676_ = v___x_1724_;
goto v___jp_1666_;
}
}
v___jp_1726_:
{
if (v___y_1736_ == 0)
{
lean_object* v___x_1737_; 
lean_dec_ref(v___y_1730_);
v___x_1737_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1518_);
if (lean_obj_tag(v___x_1737_) == 1)
{
lean_object* v_val_1738_; lean_object* v_snd_1739_; lean_object* v___x_1740_; 
v_val_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_val_1738_);
lean_dec_ref(v___x_1737_);
v_snd_1739_ = lean_ctor_get(v_val_1738_, 1);
lean_inc(v_snd_1739_);
lean_dec(v_val_1738_);
v___x_1740_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1520_, v_a_1309_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
lean_dec_ref(v___x_1740_);
if (lean_obj_tag(v_a_1741_) == 1)
{
lean_object* v_val_1742_; lean_object* v___x_1743_; 
v_val_1742_ = lean_ctor_get(v_a_1741_, 0);
lean_inc(v_val_1742_);
lean_dec_ref(v_a_1741_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1743_ = lean_infer_type(v_val_1742_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v_a_1744_; lean_object* v___x_1745_; 
v_a_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_a_1744_);
lean_dec_ref(v___x_1743_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1745_ = l_Lean_Meta_mkNumeral(v_a_1744_, v_snd_1739_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1745_) == 0)
{
lean_object* v_a_1746_; lean_object* v___x_1747_; 
v_a_1746_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1746_);
lean_dec_ref(v___x_1745_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_binderType_1534_);
v___x_1747_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1746_, v_binderType_1534_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_a_1748_; lean_object* v___x_1749_; 
v_a_1748_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_a_1748_);
lean_dec_ref(v___x_1747_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_arg_1518_);
v___x_1749_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1518_, v_a_1748_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref(v___x_1749_);
if (lean_obj_tag(v_a_1750_) == 1)
{
lean_object* v_val_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v_val_1751_ = lean_ctor_get(v_a_1750_, 0);
lean_inc(v_val_1751_);
lean_dec_ref(v_a_1750_);
lean_inc_ref(v_arg_1520_);
lean_inc_ref(v_fn_1519_);
v___x_1752_ = l_Lean_Expr_app___override(v_fn_1519_, v_arg_1520_);
v___x_1753_ = lean_box(0);
v___x_1754_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1754_, 0, v___x_1752_);
lean_ctor_set(v___x_1754_, 1, v___x_1753_);
lean_ctor_set_uint8(v___x_1754_, sizeof(void*)*2, v___y_1728_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1755_ = l_Lean_Meta_Simp_mkCongr(v___x_1754_, v_val_1751_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1755_) == 0)
{
lean_object* v_a_1756_; 
lean_dec_ref(v_binderType_1534_);
lean_dec_ref(v_expr_1305_);
v_a_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1756_);
lean_dec_ref(v___x_1755_);
v___y_1446_ = v___y_1727_;
v___y_1447_ = v___y_1728_;
v___y_1448_ = v___y_1729_;
v___y_1449_ = v___y_1731_;
v___y_1450_ = v___y_1732_;
v___y_1451_ = v___y_1733_;
v___y_1452_ = v___y_1734_;
v___y_1453_ = v___y_1735_;
v_a_1454_ = v_a_1756_;
goto v___jp_1445_;
}
else
{
lean_object* v_a_1757_; 
v_a_1757_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_a_1757_);
lean_dec_ref(v___x_1755_);
v___y_1715_ = v___y_1727_;
v___y_1716_ = v___y_1728_;
v___y_1717_ = v___y_1729_;
v___y_1718_ = v___y_1731_;
v___y_1719_ = v___y_1732_;
v___y_1720_ = v___y_1733_;
v___y_1721_ = v___y_1734_;
v___y_1722_ = v___y_1735_;
v_a_1723_ = v_a_1757_;
goto v___jp_1714_;
}
}
else
{
lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v_a_1760_; 
lean_dec(v_a_1750_);
v___x_1758_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1759_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1758_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1760_);
lean_dec_ref(v___x_1759_);
v___y_1715_ = v___y_1727_;
v___y_1716_ = v___y_1728_;
v___y_1717_ = v___y_1729_;
v___y_1718_ = v___y_1731_;
v___y_1719_ = v___y_1732_;
v___y_1720_ = v___y_1733_;
v___y_1721_ = v___y_1734_;
v___y_1722_ = v___y_1735_;
v_a_1723_ = v_a_1760_;
goto v___jp_1714_;
}
}
else
{
lean_object* v_a_1761_; 
v_a_1761_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1761_);
lean_dec_ref(v___x_1749_);
v___y_1715_ = v___y_1727_;
v___y_1716_ = v___y_1728_;
v___y_1717_ = v___y_1729_;
v___y_1718_ = v___y_1731_;
v___y_1719_ = v___y_1732_;
v___y_1720_ = v___y_1733_;
v___y_1721_ = v___y_1734_;
v___y_1722_ = v___y_1735_;
v_a_1723_ = v_a_1761_;
goto v___jp_1714_;
}
}
else
{
lean_object* v_a_1762_; 
v_a_1762_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_a_1762_);
lean_dec_ref(v___x_1747_);
v___y_1715_ = v___y_1727_;
v___y_1716_ = v___y_1728_;
v___y_1717_ = v___y_1729_;
v___y_1718_ = v___y_1731_;
v___y_1719_ = v___y_1732_;
v___y_1720_ = v___y_1733_;
v___y_1721_ = v___y_1734_;
v___y_1722_ = v___y_1735_;
v_a_1723_ = v_a_1762_;
goto v___jp_1714_;
}
}
else
{
lean_object* v_a_1763_; 
v_a_1763_ = lean_ctor_get(v___x_1745_, 0);
lean_inc(v_a_1763_);
lean_dec_ref(v___x_1745_);
v___y_1715_ = v___y_1727_;
v___y_1716_ = v___y_1728_;
v___y_1717_ = v___y_1729_;
v___y_1718_ = v___y_1731_;
v___y_1719_ = v___y_1732_;
v___y_1720_ = v___y_1733_;
v___y_1721_ = v___y_1734_;
v___y_1722_ = v___y_1735_;
v_a_1723_ = v_a_1763_;
goto v___jp_1714_;
}
}
else
{
lean_object* v_a_1764_; 
lean_dec(v_snd_1739_);
v_a_1764_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_a_1764_);
lean_dec_ref(v___x_1743_);
v___y_1715_ = v___y_1727_;
v___y_1716_ = v___y_1728_;
v___y_1717_ = v___y_1729_;
v___y_1718_ = v___y_1731_;
v___y_1719_ = v___y_1732_;
v___y_1720_ = v___y_1733_;
v___y_1721_ = v___y_1734_;
v___y_1722_ = v___y_1735_;
v_a_1723_ = v_a_1764_;
goto v___jp_1714_;
}
}
else
{
lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v_a_1767_; 
lean_dec(v_a_1741_);
lean_dec(v_snd_1739_);
v___x_1765_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1766_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1765_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref(v___x_1766_);
v___y_1715_ = v___y_1727_;
v___y_1716_ = v___y_1728_;
v___y_1717_ = v___y_1729_;
v___y_1718_ = v___y_1731_;
v___y_1719_ = v___y_1732_;
v___y_1720_ = v___y_1733_;
v___y_1721_ = v___y_1734_;
v___y_1722_ = v___y_1735_;
v_a_1723_ = v_a_1767_;
goto v___jp_1714_;
}
}
else
{
lean_object* v_a_1768_; 
lean_dec(v_snd_1739_);
v_a_1768_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1768_);
lean_dec_ref(v___x_1740_);
v___y_1715_ = v___y_1727_;
v___y_1716_ = v___y_1728_;
v___y_1717_ = v___y_1729_;
v___y_1718_ = v___y_1731_;
v___y_1719_ = v___y_1732_;
v___y_1720_ = v___y_1733_;
v___y_1721_ = v___y_1734_;
v___y_1722_ = v___y_1735_;
v_a_1723_ = v_a_1768_;
goto v___jp_1714_;
}
}
else
{
lean_object* v___x_1769_; 
v___x_1769_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1737_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v___x_1737_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; 
lean_dec_ref(v_binderType_1534_);
lean_dec_ref(v_expr_1305_);
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1770_);
lean_dec_ref(v___x_1769_);
v___y_1482_ = v___y_1727_;
v___y_1483_ = v___y_1728_;
v___y_1484_ = v___y_1729_;
v___y_1485_ = v___y_1731_;
v___y_1486_ = v___y_1732_;
v___y_1487_ = v___y_1733_;
v___y_1488_ = v___y_1734_;
v___y_1489_ = v___y_1735_;
v_a_1490_ = v_a_1770_;
goto v___jp_1481_;
}
else
{
lean_object* v_a_1771_; 
v_a_1771_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1771_);
lean_dec_ref(v___x_1769_);
v___y_1715_ = v___y_1727_;
v___y_1716_ = v___y_1728_;
v___y_1717_ = v___y_1729_;
v___y_1718_ = v___y_1731_;
v___y_1719_ = v___y_1732_;
v___y_1720_ = v___y_1733_;
v___y_1721_ = v___y_1734_;
v___y_1722_ = v___y_1735_;
v_a_1723_ = v_a_1771_;
goto v___jp_1714_;
}
}
}
else
{
lean_dec_ref(v_binderType_1534_);
lean_dec_ref(v_expr_1305_);
v___y_1435_ = v___y_1727_;
v___y_1436_ = v___y_1728_;
v___y_1437_ = v___y_1729_;
v___y_1438_ = v___y_1731_;
v___y_1439_ = v___y_1732_;
v___y_1440_ = v___y_1733_;
v___y_1441_ = v___y_1734_;
v___y_1442_ = v___y_1735_;
v_a_1443_ = v___y_1730_;
goto v___jp_1434_;
}
}
v___jp_1772_:
{
uint8_t v___x_1782_; 
v___x_1782_ = l_Lean_Exception_isInterrupt(v_a_1781_);
if (v___x_1782_ == 0)
{
uint8_t v___x_1783_; 
lean_inc_ref(v_a_1781_);
v___x_1783_ = l_Lean_Exception_isRuntime(v_a_1781_);
v___y_1727_ = v___y_1773_;
v___y_1728_ = v___y_1774_;
v___y_1729_ = v___y_1775_;
v___y_1730_ = v_a_1781_;
v___y_1731_ = v___y_1776_;
v___y_1732_ = v___y_1777_;
v___y_1733_ = v___y_1778_;
v___y_1734_ = v___y_1779_;
v___y_1735_ = v___y_1780_;
v___y_1736_ = v___x_1783_;
goto v___jp_1726_;
}
else
{
v___y_1727_ = v___y_1773_;
v___y_1728_ = v___y_1774_;
v___y_1729_ = v___y_1775_;
v___y_1730_ = v_a_1781_;
v___y_1731_ = v___y_1776_;
v___y_1732_ = v___y_1777_;
v___y_1733_ = v___y_1778_;
v___y_1734_ = v___y_1779_;
v___y_1735_ = v___y_1780_;
v___y_1736_ = v___x_1782_;
goto v___jp_1726_;
}
}
v___jp_1784_:
{
if (lean_obj_tag(v___y_1793_) == 0)
{
lean_object* v_a_1794_; 
lean_dec_ref(v_binderType_1534_);
lean_dec_ref(v_expr_1305_);
v_a_1794_ = lean_ctor_get(v___y_1793_, 0);
lean_inc(v_a_1794_);
lean_dec_ref(v___y_1793_);
v___y_1446_ = v___y_1785_;
v___y_1447_ = v___y_1786_;
v___y_1448_ = v___y_1787_;
v___y_1449_ = v___y_1788_;
v___y_1450_ = v___y_1789_;
v___y_1451_ = v___y_1790_;
v___y_1452_ = v___y_1791_;
v___y_1453_ = v___y_1792_;
v_a_1454_ = v_a_1794_;
goto v___jp_1445_;
}
else
{
lean_object* v_a_1795_; 
v_a_1795_ = lean_ctor_get(v___y_1793_, 0);
lean_inc(v_a_1795_);
lean_dec_ref(v___y_1793_);
v___y_1773_ = v___y_1785_;
v___y_1774_ = v___y_1786_;
v___y_1775_ = v___y_1787_;
v___y_1776_ = v___y_1788_;
v___y_1777_ = v___y_1789_;
v___y_1778_ = v___y_1790_;
v___y_1779_ = v___y_1791_;
v___y_1780_ = v___y_1792_;
v_a_1781_ = v_a_1795_;
goto v___jp_1772_;
}
}
v___jp_1796_:
{
if (v___y_1808_ == 0)
{
lean_object* v___x_1809_; 
lean_dec_ref(v___y_1799_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1809_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v___y_1807_, v___y_1804_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v___x_1811_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1810_);
lean_dec_ref(v___x_1809_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_binderType_1534_);
v___x_1811_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1810_, v_binderType_1534_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1813_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_a_1812_);
lean_dec_ref(v___x_1811_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_arg_1518_);
v___x_1813_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1518_, v_a_1812_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_a_1814_);
lean_dec_ref(v___x_1813_);
if (lean_obj_tag(v_a_1814_) == 1)
{
lean_object* v_val_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v_val_1815_ = lean_ctor_get(v_a_1814_, 0);
lean_inc(v_val_1815_);
lean_dec_ref(v_a_1814_);
lean_inc_ref(v_arg_1520_);
lean_inc_ref(v_fn_1519_);
v___x_1816_ = l_Lean_Expr_app___override(v_fn_1519_, v_arg_1520_);
v___x_1817_ = lean_box(0);
v___x_1818_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1818_, 0, v___x_1816_);
lean_ctor_set(v___x_1818_, 1, v___x_1817_);
lean_ctor_set_uint8(v___x_1818_, sizeof(void*)*2, v___y_1798_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1819_ = l_Lean_Meta_Simp_mkCongr(v___x_1818_, v_val_1815_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1785_ = v___y_1797_;
v___y_1786_ = v___y_1798_;
v___y_1787_ = v___y_1800_;
v___y_1788_ = v___y_1801_;
v___y_1789_ = v___y_1802_;
v___y_1790_ = v___y_1803_;
v___y_1791_ = v___y_1805_;
v___y_1792_ = v___y_1806_;
v___y_1793_ = v___x_1819_;
goto v___jp_1784_;
}
else
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
lean_dec(v_a_1814_);
v___x_1820_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1821_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1820_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1785_ = v___y_1797_;
v___y_1786_ = v___y_1798_;
v___y_1787_ = v___y_1800_;
v___y_1788_ = v___y_1801_;
v___y_1789_ = v___y_1802_;
v___y_1790_ = v___y_1803_;
v___y_1791_ = v___y_1805_;
v___y_1792_ = v___y_1806_;
v___y_1793_ = v___x_1821_;
goto v___jp_1784_;
}
}
else
{
lean_object* v_a_1822_; 
v_a_1822_ = lean_ctor_get(v___x_1813_, 0);
lean_inc(v_a_1822_);
lean_dec_ref(v___x_1813_);
v___y_1773_ = v___y_1797_;
v___y_1774_ = v___y_1798_;
v___y_1775_ = v___y_1800_;
v___y_1776_ = v___y_1801_;
v___y_1777_ = v___y_1802_;
v___y_1778_ = v___y_1803_;
v___y_1779_ = v___y_1805_;
v___y_1780_ = v___y_1806_;
v_a_1781_ = v_a_1822_;
goto v___jp_1772_;
}
}
else
{
lean_object* v_a_1823_; 
v_a_1823_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_a_1823_);
lean_dec_ref(v___x_1811_);
v___y_1773_ = v___y_1797_;
v___y_1774_ = v___y_1798_;
v___y_1775_ = v___y_1800_;
v___y_1776_ = v___y_1801_;
v___y_1777_ = v___y_1802_;
v___y_1778_ = v___y_1803_;
v___y_1779_ = v___y_1805_;
v___y_1780_ = v___y_1806_;
v_a_1781_ = v_a_1823_;
goto v___jp_1772_;
}
}
else
{
lean_object* v_a_1824_; 
v_a_1824_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1824_);
lean_dec_ref(v___x_1809_);
v___y_1773_ = v___y_1797_;
v___y_1774_ = v___y_1798_;
v___y_1775_ = v___y_1800_;
v___y_1776_ = v___y_1801_;
v___y_1777_ = v___y_1802_;
v___y_1778_ = v___y_1803_;
v___y_1779_ = v___y_1805_;
v___y_1780_ = v___y_1806_;
v_a_1781_ = v_a_1824_;
goto v___jp_1772_;
}
}
else
{
lean_dec_ref(v___y_1807_);
lean_dec_ref(v___y_1804_);
v___y_1773_ = v___y_1797_;
v___y_1774_ = v___y_1798_;
v___y_1775_ = v___y_1800_;
v___y_1776_ = v___y_1801_;
v___y_1777_ = v___y_1802_;
v___y_1778_ = v___y_1803_;
v___y_1779_ = v___y_1805_;
v___y_1780_ = v___y_1806_;
v_a_1781_ = v___y_1799_;
goto v___jp_1772_;
}
}
v___jp_1825_:
{
uint8_t v___x_1837_; 
v___x_1837_ = l_Lean_Exception_isInterrupt(v_a_1836_);
if (v___x_1837_ == 0)
{
uint8_t v___x_1838_; 
lean_inc_ref(v_a_1836_);
v___x_1838_ = l_Lean_Exception_isRuntime(v_a_1836_);
v___y_1797_ = v___y_1826_;
v___y_1798_ = v___y_1827_;
v___y_1799_ = v_a_1836_;
v___y_1800_ = v___y_1828_;
v___y_1801_ = v___y_1829_;
v___y_1802_ = v___y_1830_;
v___y_1803_ = v___y_1831_;
v___y_1804_ = v___y_1832_;
v___y_1805_ = v___y_1833_;
v___y_1806_ = v___y_1835_;
v___y_1807_ = v___y_1834_;
v___y_1808_ = v___x_1838_;
goto v___jp_1796_;
}
else
{
v___y_1797_ = v___y_1826_;
v___y_1798_ = v___y_1827_;
v___y_1799_ = v_a_1836_;
v___y_1800_ = v___y_1828_;
v___y_1801_ = v___y_1829_;
v___y_1802_ = v___y_1830_;
v___y_1803_ = v___y_1831_;
v___y_1804_ = v___y_1832_;
v___y_1805_ = v___y_1833_;
v___y_1806_ = v___y_1835_;
v___y_1807_ = v___y_1834_;
v___y_1808_ = v___x_1837_;
goto v___jp_1796_;
}
}
v___jp_1839_:
{
if (lean_obj_tag(v___y_1850_) == 0)
{
lean_object* v_a_1851_; 
lean_dec_ref(v___y_1848_);
lean_dec_ref(v___y_1846_);
lean_dec_ref(v_binderType_1534_);
lean_dec_ref(v_expr_1305_);
v_a_1851_ = lean_ctor_get(v___y_1850_, 0);
lean_inc(v_a_1851_);
lean_dec_ref(v___y_1850_);
v___y_1446_ = v___y_1840_;
v___y_1447_ = v___y_1841_;
v___y_1448_ = v___y_1842_;
v___y_1449_ = v___y_1843_;
v___y_1450_ = v___y_1844_;
v___y_1451_ = v___y_1845_;
v___y_1452_ = v___y_1847_;
v___y_1453_ = v___y_1849_;
v_a_1454_ = v_a_1851_;
goto v___jp_1445_;
}
else
{
lean_object* v_a_1852_; 
v_a_1852_ = lean_ctor_get(v___y_1850_, 0);
lean_inc(v_a_1852_);
lean_dec_ref(v___y_1850_);
v___y_1826_ = v___y_1840_;
v___y_1827_ = v___y_1841_;
v___y_1828_ = v___y_1842_;
v___y_1829_ = v___y_1843_;
v___y_1830_ = v___y_1844_;
v___y_1831_ = v___y_1845_;
v___y_1832_ = v___y_1846_;
v___y_1833_ = v___y_1847_;
v___y_1834_ = v___y_1848_;
v___y_1835_ = v___y_1849_;
v_a_1836_ = v_a_1852_;
goto v___jp_1825_;
}
}
v___jp_1853_:
{
if (v___y_1863_ == 0)
{
lean_object* v___x_1864_; 
lean_dec_ref(v___y_1859_);
v___x_1864_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1520_);
if (lean_obj_tag(v___x_1864_) == 1)
{
lean_object* v_val_1865_; lean_object* v_snd_1866_; lean_object* v___x_1867_; 
v_val_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_val_1865_);
lean_dec_ref(v___x_1864_);
v_snd_1866_ = lean_ctor_get(v_val_1865_, 1);
lean_inc(v_snd_1866_);
lean_dec(v_val_1865_);
v___x_1867_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1518_, v_a_1309_);
if (lean_obj_tag(v___x_1867_) == 0)
{
lean_object* v_a_1868_; 
v_a_1868_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_a_1868_);
lean_dec_ref(v___x_1867_);
if (lean_obj_tag(v_a_1868_) == 1)
{
lean_object* v_val_1869_; lean_object* v___x_1870_; 
v_val_1869_ = lean_ctor_get(v_a_1868_, 0);
lean_inc(v_val_1869_);
lean_dec_ref(v_a_1868_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1870_ = lean_infer_type(v_val_1869_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1872_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref(v___x_1870_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1872_ = l_Lean_Meta_mkNumeral(v_a_1871_, v_snd_1866_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___x_1874_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref(v___x_1872_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1874_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1873_, v_binderType_1534_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v___x_1876_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_a_1875_);
lean_dec_ref(v___x_1874_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_arg_1520_);
v___x_1876_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1520_, v_a_1875_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref(v___x_1876_);
if (lean_obj_tag(v_a_1877_) == 1)
{
lean_object* v_val_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v_val_1878_ = lean_ctor_get(v_a_1877_, 0);
lean_inc(v_val_1878_);
lean_dec_ref(v_a_1877_);
v___x_1879_ = lean_box(0);
lean_inc_ref(v_fn_1519_);
v___x_1880_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1880_, 0, v_fn_1519_);
lean_ctor_set(v___x_1880_, 1, v___x_1879_);
lean_ctor_set_uint8(v___x_1880_, sizeof(void*)*2, v___y_1854_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1881_ = l_Lean_Meta_Simp_mkCongr(v___x_1880_, v_val_1878_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; lean_object* v___x_1883_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1882_);
lean_dec_ref(v___x_1881_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_arg_1518_);
v___x_1883_ = l_Lean_Meta_Simp_mkCongrFun(v_a_1882_, v_arg_1518_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; 
lean_dec_ref(v_expr_1305_);
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref(v___x_1883_);
v___y_1370_ = v___y_1854_;
v___y_1371_ = v___y_1855_;
v___y_1372_ = v___y_1856_;
v___y_1373_ = v___y_1857_;
v___y_1374_ = v___y_1858_;
v___y_1375_ = v___y_1861_;
v___y_1376_ = v___y_1860_;
v___y_1377_ = v___y_1862_;
v_a_1378_ = v_a_1884_;
goto v___jp_1369_;
}
else
{
lean_object* v_a_1885_; 
v_a_1885_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1885_);
lean_dec_ref(v___x_1883_);
v___y_1394_ = v___y_1854_;
v___y_1395_ = v___y_1855_;
v___y_1396_ = v___y_1856_;
v___y_1397_ = v___y_1857_;
v___y_1398_ = v___y_1858_;
v___y_1399_ = v___y_1861_;
v___y_1400_ = v___y_1860_;
v___y_1401_ = v___y_1862_;
v_a_1402_ = v_a_1885_;
goto v___jp_1393_;
}
}
else
{
lean_object* v_a_1886_; 
v_a_1886_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1886_);
lean_dec_ref(v___x_1881_);
v___y_1394_ = v___y_1854_;
v___y_1395_ = v___y_1855_;
v___y_1396_ = v___y_1856_;
v___y_1397_ = v___y_1857_;
v___y_1398_ = v___y_1858_;
v___y_1399_ = v___y_1861_;
v___y_1400_ = v___y_1860_;
v___y_1401_ = v___y_1862_;
v_a_1402_ = v_a_1886_;
goto v___jp_1393_;
}
}
else
{
lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v_a_1889_; 
lean_dec(v_a_1877_);
v___x_1887_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1888_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1887_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref(v___x_1888_);
v___y_1394_ = v___y_1854_;
v___y_1395_ = v___y_1855_;
v___y_1396_ = v___y_1856_;
v___y_1397_ = v___y_1857_;
v___y_1398_ = v___y_1858_;
v___y_1399_ = v___y_1861_;
v___y_1400_ = v___y_1860_;
v___y_1401_ = v___y_1862_;
v_a_1402_ = v_a_1889_;
goto v___jp_1393_;
}
}
else
{
lean_object* v_a_1890_; 
v_a_1890_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1890_);
lean_dec_ref(v___x_1876_);
v___y_1394_ = v___y_1854_;
v___y_1395_ = v___y_1855_;
v___y_1396_ = v___y_1856_;
v___y_1397_ = v___y_1857_;
v___y_1398_ = v___y_1858_;
v___y_1399_ = v___y_1861_;
v___y_1400_ = v___y_1860_;
v___y_1401_ = v___y_1862_;
v_a_1402_ = v_a_1890_;
goto v___jp_1393_;
}
}
else
{
lean_object* v_a_1891_; 
v_a_1891_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_a_1891_);
lean_dec_ref(v___x_1874_);
v___y_1394_ = v___y_1854_;
v___y_1395_ = v___y_1855_;
v___y_1396_ = v___y_1856_;
v___y_1397_ = v___y_1857_;
v___y_1398_ = v___y_1858_;
v___y_1399_ = v___y_1861_;
v___y_1400_ = v___y_1860_;
v___y_1401_ = v___y_1862_;
v_a_1402_ = v_a_1891_;
goto v___jp_1393_;
}
}
else
{
lean_object* v_a_1892_; 
lean_dec_ref(v_binderType_1534_);
v_a_1892_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1892_);
lean_dec_ref(v___x_1872_);
v___y_1394_ = v___y_1854_;
v___y_1395_ = v___y_1855_;
v___y_1396_ = v___y_1856_;
v___y_1397_ = v___y_1857_;
v___y_1398_ = v___y_1858_;
v___y_1399_ = v___y_1861_;
v___y_1400_ = v___y_1860_;
v___y_1401_ = v___y_1862_;
v_a_1402_ = v_a_1892_;
goto v___jp_1393_;
}
}
else
{
lean_object* v_a_1893_; 
lean_dec(v_snd_1866_);
lean_dec_ref(v_binderType_1534_);
v_a_1893_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1893_);
lean_dec_ref(v___x_1870_);
v___y_1394_ = v___y_1854_;
v___y_1395_ = v___y_1855_;
v___y_1396_ = v___y_1856_;
v___y_1397_ = v___y_1857_;
v___y_1398_ = v___y_1858_;
v___y_1399_ = v___y_1861_;
v___y_1400_ = v___y_1860_;
v___y_1401_ = v___y_1862_;
v_a_1402_ = v_a_1893_;
goto v___jp_1393_;
}
}
else
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v_a_1896_; 
lean_dec(v_a_1868_);
lean_dec(v_snd_1866_);
lean_dec_ref(v_binderType_1534_);
v___x_1894_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1895_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1894_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref(v___x_1895_);
v___y_1394_ = v___y_1854_;
v___y_1395_ = v___y_1855_;
v___y_1396_ = v___y_1856_;
v___y_1397_ = v___y_1857_;
v___y_1398_ = v___y_1858_;
v___y_1399_ = v___y_1861_;
v___y_1400_ = v___y_1860_;
v___y_1401_ = v___y_1862_;
v_a_1402_ = v_a_1896_;
goto v___jp_1393_;
}
}
else
{
lean_object* v_a_1897_; 
lean_dec(v_snd_1866_);
lean_dec_ref(v_binderType_1534_);
v_a_1897_ = lean_ctor_get(v___x_1867_, 0);
lean_inc(v_a_1897_);
lean_dec_ref(v___x_1867_);
v___y_1394_ = v___y_1854_;
v___y_1395_ = v___y_1855_;
v___y_1396_ = v___y_1856_;
v___y_1397_ = v___y_1857_;
v___y_1398_ = v___y_1858_;
v___y_1399_ = v___y_1861_;
v___y_1400_ = v___y_1860_;
v___y_1401_ = v___y_1862_;
v_a_1402_ = v_a_1897_;
goto v___jp_1393_;
}
}
else
{
lean_object* v___x_1898_; 
lean_dec_ref(v_binderType_1534_);
v___x_1898_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1864_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v___x_1864_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; 
lean_dec_ref(v_expr_1305_);
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1899_);
lean_dec_ref(v___x_1898_);
v___y_1406_ = v___y_1854_;
v___y_1407_ = v___y_1855_;
v___y_1408_ = v___y_1856_;
v___y_1409_ = v___y_1857_;
v___y_1410_ = v___y_1858_;
v___y_1411_ = v___y_1860_;
v___y_1412_ = v___y_1861_;
v___y_1413_ = v___y_1862_;
v_a_1414_ = v_a_1899_;
goto v___jp_1405_;
}
else
{
lean_object* v_a_1900_; 
v_a_1900_ = lean_ctor_get(v___x_1898_, 0);
lean_inc(v_a_1900_);
lean_dec_ref(v___x_1898_);
v___y_1394_ = v___y_1854_;
v___y_1395_ = v___y_1855_;
v___y_1396_ = v___y_1856_;
v___y_1397_ = v___y_1857_;
v___y_1398_ = v___y_1858_;
v___y_1399_ = v___y_1861_;
v___y_1400_ = v___y_1860_;
v___y_1401_ = v___y_1862_;
v_a_1402_ = v_a_1900_;
goto v___jp_1393_;
}
}
}
else
{
lean_dec_ref(v_binderType_1534_);
lean_dec_ref(v_expr_1305_);
v___y_1359_ = v___y_1854_;
v___y_1360_ = v___y_1855_;
v___y_1361_ = v___y_1856_;
v___y_1362_ = v___y_1857_;
v___y_1363_ = v___y_1858_;
v___y_1364_ = v___y_1861_;
v___y_1365_ = v___y_1860_;
v___y_1366_ = v___y_1862_;
v_a_1367_ = v___y_1859_;
goto v___jp_1358_;
}
}
v___jp_1901_:
{
uint8_t v___x_1911_; 
v___x_1911_ = l_Lean_Exception_isInterrupt(v_a_1910_);
if (v___x_1911_ == 0)
{
uint8_t v___x_1912_; 
lean_inc_ref(v_a_1910_);
v___x_1912_ = l_Lean_Exception_isRuntime(v_a_1910_);
v___y_1854_ = v___y_1902_;
v___y_1855_ = v___y_1903_;
v___y_1856_ = v___y_1904_;
v___y_1857_ = v___y_1905_;
v___y_1858_ = v___y_1906_;
v___y_1859_ = v_a_1910_;
v___y_1860_ = v___y_1908_;
v___y_1861_ = v___y_1907_;
v___y_1862_ = v___y_1909_;
v___y_1863_ = v___x_1912_;
goto v___jp_1853_;
}
else
{
v___y_1854_ = v___y_1902_;
v___y_1855_ = v___y_1903_;
v___y_1856_ = v___y_1904_;
v___y_1857_ = v___y_1905_;
v___y_1858_ = v___y_1906_;
v___y_1859_ = v_a_1910_;
v___y_1860_ = v___y_1908_;
v___y_1861_ = v___y_1907_;
v___y_1862_ = v___y_1909_;
v___y_1863_ = v___x_1911_;
goto v___jp_1853_;
}
}
v___jp_1913_:
{
if (v___y_1923_ == 0)
{
lean_object* v___x_1924_; 
lean_dec_ref(v___y_1922_);
v___x_1924_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1518_);
if (lean_obj_tag(v___x_1924_) == 1)
{
lean_object* v_val_1925_; lean_object* v_snd_1926_; lean_object* v___x_1927_; 
v_val_1925_ = lean_ctor_get(v___x_1924_, 0);
lean_inc(v_val_1925_);
lean_dec_ref(v___x_1924_);
v_snd_1926_ = lean_ctor_get(v_val_1925_, 1);
lean_inc(v_snd_1926_);
lean_dec(v_val_1925_);
v___x_1927_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1520_, v_a_1309_);
if (lean_obj_tag(v___x_1927_) == 0)
{
lean_object* v_a_1928_; 
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref(v___x_1927_);
if (lean_obj_tag(v_a_1928_) == 1)
{
lean_object* v_val_1929_; lean_object* v___x_1930_; 
v_val_1929_ = lean_ctor_get(v_a_1928_, 0);
lean_inc(v_val_1929_);
lean_dec_ref(v_a_1928_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1930_ = lean_infer_type(v_val_1929_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1932_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_a_1931_);
lean_dec_ref(v___x_1930_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1932_ = l_Lean_Meta_mkNumeral(v_a_1931_, v_snd_1926_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1934_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref(v___x_1932_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_binderType_1534_);
v___x_1934_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1933_, v_binderType_1534_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1936_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref(v___x_1934_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_arg_1518_);
v___x_1936_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1518_, v_a_1935_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1936_) == 0)
{
lean_object* v_a_1937_; 
v_a_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_a_1937_);
lean_dec_ref(v___x_1936_);
if (lean_obj_tag(v_a_1937_) == 1)
{
lean_object* v_val_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v_val_1938_ = lean_ctor_get(v_a_1937_, 0);
lean_inc(v_val_1938_);
lean_dec_ref(v_a_1937_);
lean_inc_ref(v_arg_1520_);
lean_inc_ref(v_fn_1519_);
v___x_1939_ = l_Lean_Expr_app___override(v_fn_1519_, v_arg_1520_);
v___x_1940_ = lean_box(0);
v___x_1941_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1941_, 0, v___x_1939_);
lean_ctor_set(v___x_1941_, 1, v___x_1940_);
lean_ctor_set_uint8(v___x_1941_, sizeof(void*)*2, v___y_1914_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1942_ = l_Lean_Meta_Simp_mkCongr(v___x_1941_, v_val_1938_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; 
lean_dec_ref(v_binderType_1534_);
lean_dec_ref(v_expr_1305_);
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref(v___x_1942_);
v___y_1370_ = v___y_1914_;
v___y_1371_ = v___y_1915_;
v___y_1372_ = v___y_1916_;
v___y_1373_ = v___y_1917_;
v___y_1374_ = v___y_1918_;
v___y_1375_ = v___y_1920_;
v___y_1376_ = v___y_1919_;
v___y_1377_ = v___y_1921_;
v_a_1378_ = v_a_1943_;
goto v___jp_1369_;
}
else
{
lean_object* v_a_1944_; 
v_a_1944_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1944_);
lean_dec_ref(v___x_1942_);
v___y_1902_ = v___y_1914_;
v___y_1903_ = v___y_1915_;
v___y_1904_ = v___y_1916_;
v___y_1905_ = v___y_1917_;
v___y_1906_ = v___y_1918_;
v___y_1907_ = v___y_1920_;
v___y_1908_ = v___y_1919_;
v___y_1909_ = v___y_1921_;
v_a_1910_ = v_a_1944_;
goto v___jp_1901_;
}
}
else
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v_a_1947_; 
lean_dec(v_a_1937_);
v___x_1945_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1946_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1945_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref(v___x_1946_);
v___y_1902_ = v___y_1914_;
v___y_1903_ = v___y_1915_;
v___y_1904_ = v___y_1916_;
v___y_1905_ = v___y_1917_;
v___y_1906_ = v___y_1918_;
v___y_1907_ = v___y_1920_;
v___y_1908_ = v___y_1919_;
v___y_1909_ = v___y_1921_;
v_a_1910_ = v_a_1947_;
goto v___jp_1901_;
}
}
else
{
lean_object* v_a_1948_; 
v_a_1948_ = lean_ctor_get(v___x_1936_, 0);
lean_inc(v_a_1948_);
lean_dec_ref(v___x_1936_);
v___y_1902_ = v___y_1914_;
v___y_1903_ = v___y_1915_;
v___y_1904_ = v___y_1916_;
v___y_1905_ = v___y_1917_;
v___y_1906_ = v___y_1918_;
v___y_1907_ = v___y_1920_;
v___y_1908_ = v___y_1919_;
v___y_1909_ = v___y_1921_;
v_a_1910_ = v_a_1948_;
goto v___jp_1901_;
}
}
else
{
lean_object* v_a_1949_; 
v_a_1949_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1949_);
lean_dec_ref(v___x_1934_);
v___y_1902_ = v___y_1914_;
v___y_1903_ = v___y_1915_;
v___y_1904_ = v___y_1916_;
v___y_1905_ = v___y_1917_;
v___y_1906_ = v___y_1918_;
v___y_1907_ = v___y_1920_;
v___y_1908_ = v___y_1919_;
v___y_1909_ = v___y_1921_;
v_a_1910_ = v_a_1949_;
goto v___jp_1901_;
}
}
else
{
lean_object* v_a_1950_; 
v_a_1950_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1950_);
lean_dec_ref(v___x_1932_);
v___y_1902_ = v___y_1914_;
v___y_1903_ = v___y_1915_;
v___y_1904_ = v___y_1916_;
v___y_1905_ = v___y_1917_;
v___y_1906_ = v___y_1918_;
v___y_1907_ = v___y_1920_;
v___y_1908_ = v___y_1919_;
v___y_1909_ = v___y_1921_;
v_a_1910_ = v_a_1950_;
goto v___jp_1901_;
}
}
else
{
lean_object* v_a_1951_; 
lean_dec(v_snd_1926_);
v_a_1951_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_a_1951_);
lean_dec_ref(v___x_1930_);
v___y_1902_ = v___y_1914_;
v___y_1903_ = v___y_1915_;
v___y_1904_ = v___y_1916_;
v___y_1905_ = v___y_1917_;
v___y_1906_ = v___y_1918_;
v___y_1907_ = v___y_1920_;
v___y_1908_ = v___y_1919_;
v___y_1909_ = v___y_1921_;
v_a_1910_ = v_a_1951_;
goto v___jp_1901_;
}
}
else
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v_a_1954_; 
lean_dec(v_a_1928_);
lean_dec(v_snd_1926_);
v___x_1952_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1953_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1952_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
lean_dec_ref(v___x_1953_);
v___y_1902_ = v___y_1914_;
v___y_1903_ = v___y_1915_;
v___y_1904_ = v___y_1916_;
v___y_1905_ = v___y_1917_;
v___y_1906_ = v___y_1918_;
v___y_1907_ = v___y_1920_;
v___y_1908_ = v___y_1919_;
v___y_1909_ = v___y_1921_;
v_a_1910_ = v_a_1954_;
goto v___jp_1901_;
}
}
else
{
lean_object* v_a_1955_; 
lean_dec(v_snd_1926_);
v_a_1955_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1955_);
lean_dec_ref(v___x_1927_);
v___y_1902_ = v___y_1914_;
v___y_1903_ = v___y_1915_;
v___y_1904_ = v___y_1916_;
v___y_1905_ = v___y_1917_;
v___y_1906_ = v___y_1918_;
v___y_1907_ = v___y_1920_;
v___y_1908_ = v___y_1919_;
v___y_1909_ = v___y_1921_;
v_a_1910_ = v_a_1955_;
goto v___jp_1901_;
}
}
else
{
lean_object* v___x_1956_; 
v___x_1956_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1924_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v___x_1924_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; 
lean_dec_ref(v_binderType_1534_);
lean_dec_ref(v_expr_1305_);
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref(v___x_1956_);
v___y_1406_ = v___y_1914_;
v___y_1407_ = v___y_1915_;
v___y_1408_ = v___y_1916_;
v___y_1409_ = v___y_1917_;
v___y_1410_ = v___y_1918_;
v___y_1411_ = v___y_1919_;
v___y_1412_ = v___y_1920_;
v___y_1413_ = v___y_1921_;
v_a_1414_ = v_a_1957_;
goto v___jp_1405_;
}
else
{
lean_object* v_a_1958_; 
v_a_1958_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1958_);
lean_dec_ref(v___x_1956_);
v___y_1902_ = v___y_1914_;
v___y_1903_ = v___y_1915_;
v___y_1904_ = v___y_1916_;
v___y_1905_ = v___y_1917_;
v___y_1906_ = v___y_1918_;
v___y_1907_ = v___y_1920_;
v___y_1908_ = v___y_1919_;
v___y_1909_ = v___y_1921_;
v_a_1910_ = v_a_1958_;
goto v___jp_1901_;
}
}
}
else
{
lean_dec_ref(v_binderType_1534_);
lean_dec_ref(v_expr_1305_);
v___y_1359_ = v___y_1914_;
v___y_1360_ = v___y_1915_;
v___y_1361_ = v___y_1916_;
v___y_1362_ = v___y_1917_;
v___y_1363_ = v___y_1918_;
v___y_1364_ = v___y_1920_;
v___y_1365_ = v___y_1919_;
v___y_1366_ = v___y_1921_;
v_a_1367_ = v___y_1922_;
goto v___jp_1358_;
}
}
v___jp_1959_:
{
uint8_t v___x_1969_; 
v___x_1969_ = l_Lean_Exception_isInterrupt(v_a_1968_);
if (v___x_1969_ == 0)
{
uint8_t v___x_1970_; 
lean_inc_ref(v_a_1968_);
v___x_1970_ = l_Lean_Exception_isRuntime(v_a_1968_);
v___y_1914_ = v___y_1960_;
v___y_1915_ = v___y_1961_;
v___y_1916_ = v___y_1962_;
v___y_1917_ = v___y_1963_;
v___y_1918_ = v___y_1964_;
v___y_1919_ = v___y_1966_;
v___y_1920_ = v___y_1965_;
v___y_1921_ = v___y_1967_;
v___y_1922_ = v_a_1968_;
v___y_1923_ = v___x_1970_;
goto v___jp_1913_;
}
else
{
v___y_1914_ = v___y_1960_;
v___y_1915_ = v___y_1961_;
v___y_1916_ = v___y_1962_;
v___y_1917_ = v___y_1963_;
v___y_1918_ = v___y_1964_;
v___y_1919_ = v___y_1966_;
v___y_1920_ = v___y_1965_;
v___y_1921_ = v___y_1967_;
v___y_1922_ = v_a_1968_;
v___y_1923_ = v___x_1969_;
goto v___jp_1913_;
}
}
v___jp_1971_:
{
if (lean_obj_tag(v___y_1980_) == 0)
{
lean_object* v_a_1981_; 
lean_dec_ref(v_binderType_1534_);
lean_dec_ref(v_expr_1305_);
v_a_1981_ = lean_ctor_get(v___y_1980_, 0);
lean_inc(v_a_1981_);
lean_dec_ref(v___y_1980_);
v___y_1370_ = v___y_1972_;
v___y_1371_ = v___y_1973_;
v___y_1372_ = v___y_1974_;
v___y_1373_ = v___y_1975_;
v___y_1374_ = v___y_1976_;
v___y_1375_ = v___y_1978_;
v___y_1376_ = v___y_1977_;
v___y_1377_ = v___y_1979_;
v_a_1378_ = v_a_1981_;
goto v___jp_1369_;
}
else
{
lean_object* v_a_1982_; 
v_a_1982_ = lean_ctor_get(v___y_1980_, 0);
lean_inc(v_a_1982_);
lean_dec_ref(v___y_1980_);
v___y_1960_ = v___y_1972_;
v___y_1961_ = v___y_1973_;
v___y_1962_ = v___y_1974_;
v___y_1963_ = v___y_1975_;
v___y_1964_ = v___y_1976_;
v___y_1965_ = v___y_1978_;
v___y_1966_ = v___y_1977_;
v___y_1967_ = v___y_1979_;
v_a_1968_ = v_a_1982_;
goto v___jp_1959_;
}
}
v___jp_1983_:
{
if (v___y_1995_ == 0)
{
lean_object* v___x_1996_; 
lean_dec_ref(v___y_1984_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_1996_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v___y_1993_, v___y_1992_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v___x_1998_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref(v___x_1996_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_binderType_1534_);
v___x_1998_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1997_, v_binderType_1534_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2000_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref(v___x_1998_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_arg_1518_);
v___x_2000_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1518_, v_a_1999_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2001_);
lean_dec_ref(v___x_2000_);
if (lean_obj_tag(v_a_2001_) == 1)
{
lean_object* v_val_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
v_val_2002_ = lean_ctor_get(v_a_2001_, 0);
lean_inc(v_val_2002_);
lean_dec_ref(v_a_2001_);
lean_inc_ref(v_arg_1520_);
lean_inc_ref(v_fn_1519_);
v___x_2003_ = l_Lean_Expr_app___override(v_fn_1519_, v_arg_1520_);
v___x_2004_ = lean_box(0);
v___x_2005_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2005_, 0, v___x_2003_);
lean_ctor_set(v___x_2005_, 1, v___x_2004_);
lean_ctor_set_uint8(v___x_2005_, sizeof(void*)*2, v___y_1985_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_2006_ = l_Lean_Meta_Simp_mkCongr(v___x_2005_, v_val_2002_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1972_ = v___y_1985_;
v___y_1973_ = v___y_1986_;
v___y_1974_ = v___y_1987_;
v___y_1975_ = v___y_1988_;
v___y_1976_ = v___y_1989_;
v___y_1977_ = v___y_1991_;
v___y_1978_ = v___y_1990_;
v___y_1979_ = v___y_1994_;
v___y_1980_ = v___x_2006_;
goto v___jp_1971_;
}
else
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
lean_dec(v_a_2001_);
v___x_2007_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2008_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2007_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1972_ = v___y_1985_;
v___y_1973_ = v___y_1986_;
v___y_1974_ = v___y_1987_;
v___y_1975_ = v___y_1988_;
v___y_1976_ = v___y_1989_;
v___y_1977_ = v___y_1991_;
v___y_1978_ = v___y_1990_;
v___y_1979_ = v___y_1994_;
v___y_1980_ = v___x_2008_;
goto v___jp_1971_;
}
}
else
{
lean_object* v_a_2009_; 
v_a_2009_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2009_);
lean_dec_ref(v___x_2000_);
v___y_1960_ = v___y_1985_;
v___y_1961_ = v___y_1986_;
v___y_1962_ = v___y_1987_;
v___y_1963_ = v___y_1988_;
v___y_1964_ = v___y_1989_;
v___y_1965_ = v___y_1990_;
v___y_1966_ = v___y_1991_;
v___y_1967_ = v___y_1994_;
v_a_1968_ = v_a_2009_;
goto v___jp_1959_;
}
}
else
{
lean_object* v_a_2010_; 
v_a_2010_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_2010_);
lean_dec_ref(v___x_1998_);
v___y_1960_ = v___y_1985_;
v___y_1961_ = v___y_1986_;
v___y_1962_ = v___y_1987_;
v___y_1963_ = v___y_1988_;
v___y_1964_ = v___y_1989_;
v___y_1965_ = v___y_1990_;
v___y_1966_ = v___y_1991_;
v___y_1967_ = v___y_1994_;
v_a_1968_ = v_a_2010_;
goto v___jp_1959_;
}
}
else
{
lean_object* v_a_2011_; 
v_a_2011_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_2011_);
lean_dec_ref(v___x_1996_);
v___y_1960_ = v___y_1985_;
v___y_1961_ = v___y_1986_;
v___y_1962_ = v___y_1987_;
v___y_1963_ = v___y_1988_;
v___y_1964_ = v___y_1989_;
v___y_1965_ = v___y_1990_;
v___y_1966_ = v___y_1991_;
v___y_1967_ = v___y_1994_;
v_a_1968_ = v_a_2011_;
goto v___jp_1959_;
}
}
else
{
lean_dec_ref(v___y_1993_);
lean_dec_ref(v___y_1992_);
v___y_1960_ = v___y_1985_;
v___y_1961_ = v___y_1986_;
v___y_1962_ = v___y_1987_;
v___y_1963_ = v___y_1988_;
v___y_1964_ = v___y_1989_;
v___y_1965_ = v___y_1990_;
v___y_1966_ = v___y_1991_;
v___y_1967_ = v___y_1994_;
v_a_1968_ = v___y_1984_;
goto v___jp_1959_;
}
}
v___jp_2012_:
{
uint8_t v___x_2024_; 
v___x_2024_ = l_Lean_Exception_isInterrupt(v_a_2023_);
if (v___x_2024_ == 0)
{
uint8_t v___x_2025_; 
lean_inc_ref(v_a_2023_);
v___x_2025_ = l_Lean_Exception_isRuntime(v_a_2023_);
v___y_1984_ = v_a_2023_;
v___y_1985_ = v___y_2013_;
v___y_1986_ = v___y_2014_;
v___y_1987_ = v___y_2015_;
v___y_1988_ = v___y_2016_;
v___y_1989_ = v___y_2017_;
v___y_1990_ = v___y_2021_;
v___y_1991_ = v___y_2020_;
v___y_1992_ = v___y_2019_;
v___y_1993_ = v___y_2018_;
v___y_1994_ = v___y_2022_;
v___y_1995_ = v___x_2025_;
goto v___jp_1983_;
}
else
{
v___y_1984_ = v_a_2023_;
v___y_1985_ = v___y_2013_;
v___y_1986_ = v___y_2014_;
v___y_1987_ = v___y_2015_;
v___y_1988_ = v___y_2016_;
v___y_1989_ = v___y_2017_;
v___y_1990_ = v___y_2021_;
v___y_1991_ = v___y_2020_;
v___y_1992_ = v___y_2019_;
v___y_1993_ = v___y_2018_;
v___y_1994_ = v___y_2022_;
v___y_1995_ = v___x_2024_;
goto v___jp_1983_;
}
}
v___jp_2026_:
{
if (lean_obj_tag(v___y_2037_) == 0)
{
lean_object* v_a_2038_; 
lean_dec_ref(v___y_2033_);
lean_dec_ref(v___y_2032_);
lean_dec_ref(v_binderType_1534_);
lean_dec_ref(v_expr_1305_);
v_a_2038_ = lean_ctor_get(v___y_2037_, 0);
lean_inc(v_a_2038_);
lean_dec_ref(v___y_2037_);
v___y_1370_ = v___y_2027_;
v___y_1371_ = v___y_2028_;
v___y_1372_ = v___y_2029_;
v___y_1373_ = v___y_2030_;
v___y_1374_ = v___y_2031_;
v___y_1375_ = v___y_2035_;
v___y_1376_ = v___y_2034_;
v___y_1377_ = v___y_2036_;
v_a_1378_ = v_a_2038_;
goto v___jp_1369_;
}
else
{
lean_object* v_a_2039_; 
v_a_2039_ = lean_ctor_get(v___y_2037_, 0);
lean_inc(v_a_2039_);
lean_dec_ref(v___y_2037_);
v___y_2013_ = v___y_2027_;
v___y_2014_ = v___y_2028_;
v___y_2015_ = v___y_2029_;
v___y_2016_ = v___y_2030_;
v___y_2017_ = v___y_2031_;
v___y_2018_ = v___y_2033_;
v___y_2019_ = v___y_2032_;
v___y_2020_ = v___y_2034_;
v___y_2021_ = v___y_2035_;
v___y_2022_ = v___y_2036_;
v_a_2023_ = v_a_2039_;
goto v___jp_2012_;
}
}
v___jp_2040_:
{
lean_object* v___x_2047_; lean_object* v_a_2048_; lean_object* v___x_2049_; uint8_t v___x_2050_; 
v___x_2047_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg(v_a_1309_);
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref(v___x_2047_);
v___x_2049_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2050_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v___y_2042_, v___x_2049_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2051_ = lean_io_mono_nanos_now();
v___x_2052_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1520_, v_a_1309_);
if (lean_obj_tag(v___x_2052_) == 0)
{
lean_object* v_a_2053_; 
v_a_2053_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2053_);
lean_dec_ref(v___x_2052_);
if (lean_obj_tag(v_a_2053_) == 1)
{
lean_object* v_val_2054_; lean_object* v___x_2055_; 
v_val_2054_ = lean_ctor_get(v_a_2053_, 0);
lean_inc(v_val_2054_);
lean_dec_ref(v_a_2053_);
v___x_2055_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1518_, v_a_1309_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref(v___x_2055_);
if (lean_obj_tag(v_a_2056_) == 1)
{
lean_object* v_val_2057_; lean_object* v___x_2058_; 
v_val_2057_ = lean_ctor_get(v_a_2056_, 0);
lean_inc(v_val_2057_);
lean_dec_ref(v_a_2056_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc(v_val_2054_);
v___x_2058_ = lean_infer_type(v_val_2054_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2058_) == 0)
{
lean_object* v_a_2059_; lean_object* v___x_2060_; 
v_a_2059_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref(v___x_2058_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc(v_val_2057_);
v___x_2060_ = lean_infer_type(v_val_2057_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v___x_2062_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2061_);
lean_dec_ref(v___x_2060_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_2062_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_val_2054_, v_a_2061_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2064_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2063_);
lean_dec_ref(v___x_2062_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_binderType_1534_);
v___x_2064_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2063_, v_binderType_1534_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; lean_object* v___x_2066_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2065_);
lean_dec_ref(v___x_2064_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_arg_1520_);
v___x_2066_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1520_, v_a_2065_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v_a_2067_; 
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2067_);
lean_dec_ref(v___x_2066_);
if (lean_obj_tag(v_a_2067_) == 1)
{
lean_object* v_val_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v_val_2068_ = lean_ctor_get(v_a_2067_, 0);
lean_inc(v_val_2068_);
lean_dec_ref(v_a_2067_);
v___x_2069_ = lean_box(0);
lean_inc_ref(v_fn_1519_);
v___x_2070_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2070_, 0, v_fn_1519_);
lean_ctor_set(v___x_2070_, 1, v___x_2069_);
lean_ctor_set_uint8(v___x_2070_, sizeof(void*)*2, v___y_2041_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_2071_ = l_Lean_Meta_Simp_mkCongr(v___x_2070_, v_val_2068_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v___x_2073_; 
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2072_);
lean_dec_ref(v___x_2071_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_arg_1518_);
v___x_2073_ = l_Lean_Meta_Simp_mkCongrFun(v_a_2072_, v_arg_1518_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_2027_ = v___y_2041_;
v___y_2028_ = v___y_2042_;
v___y_2029_ = v___y_2043_;
v___y_2030_ = v___y_2044_;
v___y_2031_ = v___y_2045_;
v___y_2032_ = v_a_2059_;
v___y_2033_ = v_val_2057_;
v___y_2034_ = v_a_2048_;
v___y_2035_ = v___x_2051_;
v___y_2036_ = v___y_2046_;
v___y_2037_ = v___x_2073_;
goto v___jp_2026_;
}
else
{
v___y_2027_ = v___y_2041_;
v___y_2028_ = v___y_2042_;
v___y_2029_ = v___y_2043_;
v___y_2030_ = v___y_2044_;
v___y_2031_ = v___y_2045_;
v___y_2032_ = v_a_2059_;
v___y_2033_ = v_val_2057_;
v___y_2034_ = v_a_2048_;
v___y_2035_ = v___x_2051_;
v___y_2036_ = v___y_2046_;
v___y_2037_ = v___x_2071_;
goto v___jp_2026_;
}
}
else
{
lean_object* v___x_2074_; lean_object* v___x_2075_; 
lean_dec(v_a_2067_);
v___x_2074_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2075_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2074_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_2027_ = v___y_2041_;
v___y_2028_ = v___y_2042_;
v___y_2029_ = v___y_2043_;
v___y_2030_ = v___y_2044_;
v___y_2031_ = v___y_2045_;
v___y_2032_ = v_a_2059_;
v___y_2033_ = v_val_2057_;
v___y_2034_ = v_a_2048_;
v___y_2035_ = v___x_2051_;
v___y_2036_ = v___y_2046_;
v___y_2037_ = v___x_2075_;
goto v___jp_2026_;
}
}
else
{
lean_object* v_a_2076_; 
v_a_2076_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_a_2076_);
lean_dec_ref(v___x_2066_);
v___y_2013_ = v___y_2041_;
v___y_2014_ = v___y_2042_;
v___y_2015_ = v___y_2043_;
v___y_2016_ = v___y_2044_;
v___y_2017_ = v___y_2045_;
v___y_2018_ = v_val_2057_;
v___y_2019_ = v_a_2059_;
v___y_2020_ = v_a_2048_;
v___y_2021_ = v___x_2051_;
v___y_2022_ = v___y_2046_;
v_a_2023_ = v_a_2076_;
goto v___jp_2012_;
}
}
else
{
lean_object* v_a_2077_; 
v_a_2077_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2077_);
lean_dec_ref(v___x_2064_);
v___y_2013_ = v___y_2041_;
v___y_2014_ = v___y_2042_;
v___y_2015_ = v___y_2043_;
v___y_2016_ = v___y_2044_;
v___y_2017_ = v___y_2045_;
v___y_2018_ = v_val_2057_;
v___y_2019_ = v_a_2059_;
v___y_2020_ = v_a_2048_;
v___y_2021_ = v___x_2051_;
v___y_2022_ = v___y_2046_;
v_a_2023_ = v_a_2077_;
goto v___jp_2012_;
}
}
else
{
lean_object* v_a_2078_; 
v_a_2078_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2078_);
lean_dec_ref(v___x_2062_);
v___y_2013_ = v___y_2041_;
v___y_2014_ = v___y_2042_;
v___y_2015_ = v___y_2043_;
v___y_2016_ = v___y_2044_;
v___y_2017_ = v___y_2045_;
v___y_2018_ = v_val_2057_;
v___y_2019_ = v_a_2059_;
v___y_2020_ = v_a_2048_;
v___y_2021_ = v___x_2051_;
v___y_2022_ = v___y_2046_;
v_a_2023_ = v_a_2078_;
goto v___jp_2012_;
}
}
else
{
lean_object* v_a_2079_; 
lean_dec(v_a_2059_);
lean_dec(v_val_2057_);
lean_dec(v_val_2054_);
v_a_2079_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2079_);
lean_dec_ref(v___x_2060_);
v___y_1960_ = v___y_2041_;
v___y_1961_ = v___y_2042_;
v___y_1962_ = v___y_2043_;
v___y_1963_ = v___y_2044_;
v___y_1964_ = v___y_2045_;
v___y_1965_ = v___x_2051_;
v___y_1966_ = v_a_2048_;
v___y_1967_ = v___y_2046_;
v_a_1968_ = v_a_2079_;
goto v___jp_1959_;
}
}
else
{
lean_object* v_a_2080_; 
lean_dec(v_val_2057_);
lean_dec(v_val_2054_);
v_a_2080_ = lean_ctor_get(v___x_2058_, 0);
lean_inc(v_a_2080_);
lean_dec_ref(v___x_2058_);
v___y_1960_ = v___y_2041_;
v___y_1961_ = v___y_2042_;
v___y_1962_ = v___y_2043_;
v___y_1963_ = v___y_2044_;
v___y_1964_ = v___y_2045_;
v___y_1965_ = v___x_2051_;
v___y_1966_ = v_a_2048_;
v___y_1967_ = v___y_2046_;
v_a_1968_ = v_a_2080_;
goto v___jp_1959_;
}
}
else
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v_a_2083_; 
lean_dec(v_a_2056_);
lean_dec(v_val_2054_);
v___x_2081_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2082_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2081_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
lean_dec_ref(v___x_2082_);
v___y_1960_ = v___y_2041_;
v___y_1961_ = v___y_2042_;
v___y_1962_ = v___y_2043_;
v___y_1963_ = v___y_2044_;
v___y_1964_ = v___y_2045_;
v___y_1965_ = v___x_2051_;
v___y_1966_ = v_a_2048_;
v___y_1967_ = v___y_2046_;
v_a_1968_ = v_a_2083_;
goto v___jp_1959_;
}
}
else
{
lean_object* v_a_2084_; 
lean_dec(v_val_2054_);
v_a_2084_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2084_);
lean_dec_ref(v___x_2055_);
v___y_1960_ = v___y_2041_;
v___y_1961_ = v___y_2042_;
v___y_1962_ = v___y_2043_;
v___y_1963_ = v___y_2044_;
v___y_1964_ = v___y_2045_;
v___y_1965_ = v___x_2051_;
v___y_1966_ = v_a_2048_;
v___y_1967_ = v___y_2046_;
v_a_1968_ = v_a_2084_;
goto v___jp_1959_;
}
}
else
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v_a_2087_; 
lean_dec(v_a_2053_);
v___x_2085_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2086_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2085_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v_a_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_a_2087_);
lean_dec_ref(v___x_2086_);
v___y_1960_ = v___y_2041_;
v___y_1961_ = v___y_2042_;
v___y_1962_ = v___y_2043_;
v___y_1963_ = v___y_2044_;
v___y_1964_ = v___y_2045_;
v___y_1965_ = v___x_2051_;
v___y_1966_ = v_a_2048_;
v___y_1967_ = v___y_2046_;
v_a_1968_ = v_a_2087_;
goto v___jp_1959_;
}
}
else
{
lean_object* v_a_2088_; 
v_a_2088_ = lean_ctor_get(v___x_2052_, 0);
lean_inc(v_a_2088_);
lean_dec_ref(v___x_2052_);
v___y_1960_ = v___y_2041_;
v___y_1961_ = v___y_2042_;
v___y_1962_ = v___y_2043_;
v___y_1963_ = v___y_2044_;
v___y_1964_ = v___y_2045_;
v___y_1965_ = v___x_2051_;
v___y_1966_ = v_a_2048_;
v___y_1967_ = v___y_2046_;
v_a_1968_ = v_a_2088_;
goto v___jp_1959_;
}
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = lean_io_get_num_heartbeats();
v___x_2090_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1520_, v_a_1309_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref(v___x_2090_);
if (lean_obj_tag(v_a_2091_) == 1)
{
lean_object* v_val_2092_; lean_object* v___x_2093_; 
v_val_2092_ = lean_ctor_get(v_a_2091_, 0);
lean_inc(v_val_2092_);
lean_dec_ref(v_a_2091_);
v___x_2093_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1518_, v_a_1309_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_a_2094_);
lean_dec_ref(v___x_2093_);
if (lean_obj_tag(v_a_2094_) == 1)
{
lean_object* v_val_2095_; lean_object* v___x_2096_; 
v_val_2095_ = lean_ctor_get(v_a_2094_, 0);
lean_inc(v_val_2095_);
lean_dec_ref(v_a_2094_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc(v_val_2092_);
v___x_2096_ = lean_infer_type(v_val_2092_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2098_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2097_);
lean_dec_ref(v___x_2096_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc(v_val_2095_);
v___x_2098_ = lean_infer_type(v_val_2095_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_a_2099_; lean_object* v___x_2100_; 
v_a_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2099_);
lean_dec_ref(v___x_2098_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_2100_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_val_2092_, v_a_2099_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v___x_2102_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2101_);
lean_dec_ref(v___x_2100_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_binderType_1534_);
v___x_2102_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2101_, v_binderType_1534_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v___x_2104_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref(v___x_2102_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_arg_1520_);
v___x_2104_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1520_, v_a_2103_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref(v___x_2104_);
if (lean_obj_tag(v_a_2105_) == 1)
{
lean_object* v_val_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v_val_2106_ = lean_ctor_get(v_a_2105_, 0);
lean_inc(v_val_2106_);
lean_dec_ref(v_a_2105_);
v___x_2107_ = lean_box(0);
lean_inc_ref(v_fn_1519_);
v___x_2108_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2108_, 0, v_fn_1519_);
lean_ctor_set(v___x_2108_, 1, v___x_2107_);
lean_ctor_set_uint8(v___x_2108_, sizeof(void*)*2, v___y_2041_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_2109_ = l_Lean_Meta_Simp_mkCongr(v___x_2108_, v_val_2106_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2111_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_a_2110_);
lean_dec_ref(v___x_2109_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_arg_1518_);
v___x_2111_ = l_Lean_Meta_Simp_mkCongrFun(v_a_2110_, v_arg_1518_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1840_ = v___x_2089_;
v___y_1841_ = v___y_2041_;
v___y_1842_ = v___y_2042_;
v___y_1843_ = v___y_2043_;
v___y_1844_ = v___y_2044_;
v___y_1845_ = v___y_2045_;
v___y_1846_ = v_a_2097_;
v___y_1847_ = v_a_2048_;
v___y_1848_ = v_val_2095_;
v___y_1849_ = v___y_2046_;
v___y_1850_ = v___x_2111_;
goto v___jp_1839_;
}
else
{
v___y_1840_ = v___x_2089_;
v___y_1841_ = v___y_2041_;
v___y_1842_ = v___y_2042_;
v___y_1843_ = v___y_2043_;
v___y_1844_ = v___y_2044_;
v___y_1845_ = v___y_2045_;
v___y_1846_ = v_a_2097_;
v___y_1847_ = v_a_2048_;
v___y_1848_ = v_val_2095_;
v___y_1849_ = v___y_2046_;
v___y_1850_ = v___x_2109_;
goto v___jp_1839_;
}
}
else
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_dec(v_a_2105_);
v___x_2112_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2113_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2112_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1840_ = v___x_2089_;
v___y_1841_ = v___y_2041_;
v___y_1842_ = v___y_2042_;
v___y_1843_ = v___y_2043_;
v___y_1844_ = v___y_2044_;
v___y_1845_ = v___y_2045_;
v___y_1846_ = v_a_2097_;
v___y_1847_ = v_a_2048_;
v___y_1848_ = v_val_2095_;
v___y_1849_ = v___y_2046_;
v___y_1850_ = v___x_2113_;
goto v___jp_1839_;
}
}
else
{
lean_object* v_a_2114_; 
v_a_2114_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2114_);
lean_dec_ref(v___x_2104_);
v___y_1826_ = v___x_2089_;
v___y_1827_ = v___y_2041_;
v___y_1828_ = v___y_2042_;
v___y_1829_ = v___y_2043_;
v___y_1830_ = v___y_2044_;
v___y_1831_ = v___y_2045_;
v___y_1832_ = v_a_2097_;
v___y_1833_ = v_a_2048_;
v___y_1834_ = v_val_2095_;
v___y_1835_ = v___y_2046_;
v_a_1836_ = v_a_2114_;
goto v___jp_1825_;
}
}
else
{
lean_object* v_a_2115_; 
v_a_2115_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2115_);
lean_dec_ref(v___x_2102_);
v___y_1826_ = v___x_2089_;
v___y_1827_ = v___y_2041_;
v___y_1828_ = v___y_2042_;
v___y_1829_ = v___y_2043_;
v___y_1830_ = v___y_2044_;
v___y_1831_ = v___y_2045_;
v___y_1832_ = v_a_2097_;
v___y_1833_ = v_a_2048_;
v___y_1834_ = v_val_2095_;
v___y_1835_ = v___y_2046_;
v_a_1836_ = v_a_2115_;
goto v___jp_1825_;
}
}
else
{
lean_object* v_a_2116_; 
v_a_2116_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2116_);
lean_dec_ref(v___x_2100_);
v___y_1826_ = v___x_2089_;
v___y_1827_ = v___y_2041_;
v___y_1828_ = v___y_2042_;
v___y_1829_ = v___y_2043_;
v___y_1830_ = v___y_2044_;
v___y_1831_ = v___y_2045_;
v___y_1832_ = v_a_2097_;
v___y_1833_ = v_a_2048_;
v___y_1834_ = v_val_2095_;
v___y_1835_ = v___y_2046_;
v_a_1836_ = v_a_2116_;
goto v___jp_1825_;
}
}
else
{
lean_object* v_a_2117_; 
lean_dec(v_a_2097_);
lean_dec(v_val_2095_);
lean_dec(v_val_2092_);
v_a_2117_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_a_2117_);
lean_dec_ref(v___x_2098_);
v___y_1773_ = v___x_2089_;
v___y_1774_ = v___y_2041_;
v___y_1775_ = v___y_2042_;
v___y_1776_ = v___y_2043_;
v___y_1777_ = v___y_2044_;
v___y_1778_ = v___y_2045_;
v___y_1779_ = v_a_2048_;
v___y_1780_ = v___y_2046_;
v_a_1781_ = v_a_2117_;
goto v___jp_1772_;
}
}
else
{
lean_object* v_a_2118_; 
lean_dec(v_val_2095_);
lean_dec(v_val_2092_);
v_a_2118_ = lean_ctor_get(v___x_2096_, 0);
lean_inc(v_a_2118_);
lean_dec_ref(v___x_2096_);
v___y_1773_ = v___x_2089_;
v___y_1774_ = v___y_2041_;
v___y_1775_ = v___y_2042_;
v___y_1776_ = v___y_2043_;
v___y_1777_ = v___y_2044_;
v___y_1778_ = v___y_2045_;
v___y_1779_ = v_a_2048_;
v___y_1780_ = v___y_2046_;
v_a_1781_ = v_a_2118_;
goto v___jp_1772_;
}
}
else
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v_a_2121_; 
lean_dec(v_a_2094_);
lean_dec(v_val_2092_);
v___x_2119_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2120_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2119_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref(v___x_2120_);
v___y_1773_ = v___x_2089_;
v___y_1774_ = v___y_2041_;
v___y_1775_ = v___y_2042_;
v___y_1776_ = v___y_2043_;
v___y_1777_ = v___y_2044_;
v___y_1778_ = v___y_2045_;
v___y_1779_ = v_a_2048_;
v___y_1780_ = v___y_2046_;
v_a_1781_ = v_a_2121_;
goto v___jp_1772_;
}
}
else
{
lean_object* v_a_2122_; 
lean_dec(v_val_2092_);
v_a_2122_ = lean_ctor_get(v___x_2093_, 0);
lean_inc(v_a_2122_);
lean_dec_ref(v___x_2093_);
v___y_1773_ = v___x_2089_;
v___y_1774_ = v___y_2041_;
v___y_1775_ = v___y_2042_;
v___y_1776_ = v___y_2043_;
v___y_1777_ = v___y_2044_;
v___y_1778_ = v___y_2045_;
v___y_1779_ = v_a_2048_;
v___y_1780_ = v___y_2046_;
v_a_1781_ = v_a_2122_;
goto v___jp_1772_;
}
}
else
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v_a_2125_; 
lean_dec(v_a_2091_);
v___x_2123_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2124_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2123_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref(v___x_2124_);
v___y_1773_ = v___x_2089_;
v___y_1774_ = v___y_2041_;
v___y_1775_ = v___y_2042_;
v___y_1776_ = v___y_2043_;
v___y_1777_ = v___y_2044_;
v___y_1778_ = v___y_2045_;
v___y_1779_ = v_a_2048_;
v___y_1780_ = v___y_2046_;
v_a_1781_ = v_a_2125_;
goto v___jp_1772_;
}
}
else
{
lean_object* v_a_2126_; 
v_a_2126_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2126_);
lean_dec_ref(v___x_2090_);
v___y_1773_ = v___x_2089_;
v___y_1774_ = v___y_2041_;
v___y_1775_ = v___y_2042_;
v___y_1776_ = v___y_2043_;
v___y_1777_ = v___y_2044_;
v___y_1778_ = v___y_2045_;
v___y_1779_ = v_a_2048_;
v___y_1780_ = v___y_2046_;
v_a_1781_ = v_a_2126_;
goto v___jp_1772_;
}
}
}
v___jp_2127_:
{
if (v___y_2130_ == 0)
{
lean_object* v___x_2131_; 
lean_dec_ref(v___y_2129_);
v___x_2131_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1520_);
if (lean_obj_tag(v___x_2131_) == 1)
{
lean_object* v_val_2132_; lean_object* v_snd_2133_; lean_object* v___x_2134_; 
v_val_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_val_2132_);
lean_dec_ref(v___x_2131_);
v_snd_2133_ = lean_ctor_get(v_val_2132_, 1);
lean_inc(v_snd_2133_);
lean_dec(v_val_2132_);
v___x_2134_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1518_, v_a_1309_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref(v___x_2134_);
if (lean_obj_tag(v_a_2135_) == 1)
{
lean_object* v_val_2136_; lean_object* v___x_2137_; 
v_val_2136_ = lean_ctor_get(v_a_2135_, 0);
lean_inc(v_val_2136_);
lean_dec_ref(v_a_2135_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_2137_ = lean_infer_type(v_val_2136_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2139_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref(v___x_2137_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_2139_ = l_Lean_Meta_mkNumeral(v_a_2138_, v_snd_2133_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2141_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref(v___x_2139_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_2141_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2140_, v_binderType_1534_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2143_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref(v___x_2141_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_arg_1520_);
v___x_2143_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1520_, v_a_2142_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref(v___x_2143_);
if (lean_obj_tag(v_a_2144_) == 1)
{
lean_object* v_val_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v_val_2145_ = lean_ctor_get(v_a_2144_, 0);
lean_inc(v_val_2145_);
lean_dec_ref(v_a_2144_);
v___x_2146_ = lean_box(0);
lean_inc_ref(v_fn_1519_);
v___x_2147_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2147_, 0, v_fn_1519_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
lean_ctor_set_uint8(v___x_2147_, sizeof(void*)*2, v___y_2128_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_2148_ = l_Lean_Meta_Simp_mkCongr(v___x_2147_, v_val_2145_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2150_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2149_);
lean_dec_ref(v___x_2148_);
lean_inc_ref(v_arg_1518_);
v___x_2150_ = l_Lean_Meta_Simp_mkCongrFun(v_a_2149_, v_arg_1518_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_dec_ref(v_expr_1305_);
return v___x_2150_;
}
else
{
lean_object* v_a_2151_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref(v___x_2150_);
v___y_1320_ = v___y_2128_;
v_a_1321_ = v_a_2151_;
goto v___jp_1319_;
}
}
else
{
lean_object* v_a_2152_; 
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v_a_2152_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2152_);
lean_dec_ref(v___x_2148_);
v___y_1320_ = v___y_2128_;
v_a_1321_ = v_a_2152_;
goto v___jp_1319_;
}
}
else
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v_a_2155_; 
lean_dec(v_a_2144_);
v___x_2153_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2154_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2153_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v_a_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc(v_a_2155_);
lean_dec_ref(v___x_2154_);
v___y_1320_ = v___y_2128_;
v_a_1321_ = v_a_2155_;
goto v___jp_1319_;
}
}
else
{
lean_object* v_a_2156_; 
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v_a_2156_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2156_);
lean_dec_ref(v___x_2143_);
v___y_1320_ = v___y_2128_;
v_a_1321_ = v_a_2156_;
goto v___jp_1319_;
}
}
else
{
lean_object* v_a_2157_; 
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v_a_2157_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2157_);
lean_dec_ref(v___x_2141_);
v___y_1320_ = v___y_2128_;
v_a_1321_ = v_a_2157_;
goto v___jp_1319_;
}
}
else
{
lean_object* v_a_2158_; 
lean_dec_ref(v_binderType_1534_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v_a_2158_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2158_);
lean_dec_ref(v___x_2139_);
v___y_1320_ = v___y_2128_;
v_a_1321_ = v_a_2158_;
goto v___jp_1319_;
}
}
else
{
lean_object* v_a_2159_; 
lean_dec(v_snd_2133_);
lean_dec_ref(v_binderType_1534_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v_a_2159_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2159_);
lean_dec_ref(v___x_2137_);
v___y_1320_ = v___y_2128_;
v_a_1321_ = v_a_2159_;
goto v___jp_1319_;
}
}
else
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v_a_2162_; 
lean_dec(v_a_2135_);
lean_dec(v_snd_2133_);
lean_dec_ref(v_binderType_1534_);
v___x_2160_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2161_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2160_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
lean_inc(v_a_2162_);
lean_dec_ref(v___x_2161_);
v___y_1320_ = v___y_2128_;
v_a_1321_ = v_a_2162_;
goto v___jp_1319_;
}
}
else
{
lean_object* v_a_2163_; 
lean_dec(v_snd_2133_);
lean_dec_ref(v_binderType_1534_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v_a_2163_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2163_);
lean_dec_ref(v___x_2134_);
v___y_1320_ = v___y_2128_;
v_a_1321_ = v_a_2163_;
goto v___jp_1319_;
}
}
else
{
lean_object* v___x_2164_; 
lean_dec_ref(v_binderType_1534_);
v___x_2164_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_2131_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
lean_dec(v___x_2131_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; 
lean_dec_ref(v_expr_1305_);
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2165_);
lean_dec_ref(v___x_2164_);
v_a_1493_ = v_a_2165_;
goto v___jp_1492_;
}
else
{
lean_object* v_a_2166_; 
v_a_2166_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2166_);
lean_dec_ref(v___x_2164_);
v___y_1320_ = v___y_2128_;
v_a_1321_ = v_a_2166_;
goto v___jp_1319_;
}
}
}
else
{
lean_object* v___x_2167_; 
lean_dec_ref(v_binderType_1534_);
lean_dec_ref(v_expr_1305_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v___x_2167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2167_, 0, v___y_2129_);
return v___x_2167_;
}
}
v___jp_2168_:
{
uint8_t v___x_2171_; 
v___x_2171_ = l_Lean_Exception_isInterrupt(v_a_2170_);
if (v___x_2171_ == 0)
{
uint8_t v___x_2172_; 
lean_inc_ref(v_a_2170_);
v___x_2172_ = l_Lean_Exception_isRuntime(v_a_2170_);
v___y_2128_ = v___y_2169_;
v___y_2129_ = v_a_2170_;
v___y_2130_ = v___x_2172_;
goto v___jp_2127_;
}
else
{
v___y_2128_ = v___y_2169_;
v___y_2129_ = v_a_2170_;
v___y_2130_ = v___x_2171_;
goto v___jp_2127_;
}
}
v___jp_2173_:
{
if (v___y_2176_ == 0)
{
lean_object* v___x_2177_; 
lean_dec_ref(v___y_2175_);
v___x_2177_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1518_);
if (lean_obj_tag(v___x_2177_) == 1)
{
lean_object* v_val_2178_; lean_object* v_snd_2179_; lean_object* v___x_2180_; 
v_val_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_val_2178_);
lean_dec_ref(v___x_2177_);
v_snd_2179_ = lean_ctor_get(v_val_2178_, 1);
lean_inc(v_snd_2179_);
lean_dec(v_val_2178_);
v___x_2180_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1520_, v_a_1309_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2181_);
lean_dec_ref(v___x_2180_);
if (lean_obj_tag(v_a_2181_) == 1)
{
lean_object* v_val_2182_; lean_object* v___x_2183_; 
v_val_2182_ = lean_ctor_get(v_a_2181_, 0);
lean_inc(v_val_2182_);
lean_dec_ref(v_a_2181_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_2183_ = lean_infer_type(v_val_2182_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v___x_2185_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_a_2184_);
lean_dec_ref(v___x_2183_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_2185_ = l_Lean_Meta_mkNumeral(v_a_2184_, v_snd_2179_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; lean_object* v___x_2187_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
lean_dec_ref(v___x_2185_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_binderType_1534_);
v___x_2187_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2186_, v_binderType_1534_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; lean_object* v___x_2189_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_a_2188_);
lean_dec_ref(v___x_2187_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_arg_1518_);
v___x_2189_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1518_, v_a_2188_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2189_) == 0)
{
lean_object* v_a_2190_; 
v_a_2190_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2190_);
lean_dec_ref(v___x_2189_);
if (lean_obj_tag(v_a_2190_) == 1)
{
lean_object* v_val_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v_val_2191_ = lean_ctor_get(v_a_2190_, 0);
lean_inc(v_val_2191_);
lean_dec_ref(v_a_2190_);
lean_inc_ref(v_arg_1520_);
lean_inc_ref(v_fn_1519_);
v___x_2192_ = l_Lean_Expr_app___override(v_fn_1519_, v_arg_1520_);
v___x_2193_ = lean_box(0);
v___x_2194_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2194_, 0, v___x_2192_);
lean_ctor_set(v___x_2194_, 1, v___x_2193_);
lean_ctor_set_uint8(v___x_2194_, sizeof(void*)*2, v___y_2174_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_2195_ = l_Lean_Meta_Simp_mkCongr(v___x_2194_, v_val_2191_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_dec_ref(v_binderType_1534_);
lean_dec_ref(v_expr_1305_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
return v___x_2195_;
}
else
{
lean_object* v_a_2196_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref(v___x_2195_);
v___y_2169_ = v___y_2174_;
v_a_2170_ = v_a_2196_;
goto v___jp_2168_;
}
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v_a_2199_; 
lean_dec(v_a_2190_);
v___x_2197_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2198_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2197_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref(v___x_2198_);
v___y_2169_ = v___y_2174_;
v_a_2170_ = v_a_2199_;
goto v___jp_2168_;
}
}
else
{
lean_object* v_a_2200_; 
v_a_2200_ = lean_ctor_get(v___x_2189_, 0);
lean_inc(v_a_2200_);
lean_dec_ref(v___x_2189_);
v___y_2169_ = v___y_2174_;
v_a_2170_ = v_a_2200_;
goto v___jp_2168_;
}
}
else
{
lean_object* v_a_2201_; 
v_a_2201_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_a_2201_);
lean_dec_ref(v___x_2187_);
v___y_2169_ = v___y_2174_;
v_a_2170_ = v_a_2201_;
goto v___jp_2168_;
}
}
else
{
lean_object* v_a_2202_; 
v_a_2202_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2202_);
lean_dec_ref(v___x_2185_);
v___y_2169_ = v___y_2174_;
v_a_2170_ = v_a_2202_;
goto v___jp_2168_;
}
}
else
{
lean_object* v_a_2203_; 
lean_dec(v_snd_2179_);
v_a_2203_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_a_2203_);
lean_dec_ref(v___x_2183_);
v___y_2169_ = v___y_2174_;
v_a_2170_ = v_a_2203_;
goto v___jp_2168_;
}
}
else
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v_a_2206_; 
lean_dec(v_a_2181_);
lean_dec(v_snd_2179_);
v___x_2204_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2205_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2204_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_a_2206_);
lean_dec_ref(v___x_2205_);
v___y_2169_ = v___y_2174_;
v_a_2170_ = v_a_2206_;
goto v___jp_2168_;
}
}
else
{
lean_object* v_a_2207_; 
lean_dec(v_snd_2179_);
v_a_2207_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2207_);
lean_dec_ref(v___x_2180_);
v___y_2169_ = v___y_2174_;
v_a_2170_ = v_a_2207_;
goto v___jp_2168_;
}
}
else
{
lean_object* v___x_2208_; 
v___x_2208_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_2177_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec(v___x_2177_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; 
lean_dec_ref(v_binderType_1534_);
lean_dec_ref(v_expr_1305_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2209_);
lean_dec_ref(v___x_2208_);
v_a_1493_ = v_a_2209_;
goto v___jp_1492_;
}
else
{
lean_object* v_a_2210_; 
v_a_2210_ = lean_ctor_get(v___x_2208_, 0);
lean_inc(v_a_2210_);
lean_dec_ref(v___x_2208_);
v___y_2169_ = v___y_2174_;
v_a_2170_ = v_a_2210_;
goto v___jp_2168_;
}
}
}
else
{
lean_object* v___x_2211_; 
lean_dec_ref(v_binderType_1534_);
lean_dec_ref(v_expr_1305_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v___x_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2211_, 0, v___y_2175_);
return v___x_2211_;
}
}
v___jp_2212_:
{
uint8_t v___x_2215_; 
v___x_2215_ = l_Lean_Exception_isInterrupt(v_a_2214_);
if (v___x_2215_ == 0)
{
uint8_t v___x_2216_; 
lean_inc_ref(v_a_2214_);
v___x_2216_ = l_Lean_Exception_isRuntime(v_a_2214_);
v___y_2174_ = v___y_2213_;
v___y_2175_ = v_a_2214_;
v___y_2176_ = v___x_2216_;
goto v___jp_2173_;
}
else
{
v___y_2174_ = v___y_2213_;
v___y_2175_ = v_a_2214_;
v___y_2176_ = v___x_2215_;
goto v___jp_2173_;
}
}
v___jp_2217_:
{
if (lean_obj_tag(v___y_2219_) == 0)
{
lean_dec_ref(v_binderType_1534_);
lean_dec_ref(v_expr_1305_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
return v___y_2219_;
}
else
{
lean_object* v_a_2220_; 
v_a_2220_ = lean_ctor_get(v___y_2219_, 0);
lean_inc(v_a_2220_);
lean_dec_ref(v___y_2219_);
v___y_2213_ = v___y_2218_;
v_a_2214_ = v_a_2220_;
goto v___jp_2212_;
}
}
v___jp_2221_:
{
if (v___y_2226_ == 0)
{
lean_object* v___x_2227_; 
lean_dec_ref(v___y_2225_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_2227_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v___y_2224_, v___y_2222_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v___x_2229_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2228_);
lean_dec_ref(v___x_2227_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_binderType_1534_);
v___x_2229_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2228_, v_binderType_1534_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2231_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2230_);
lean_dec_ref(v___x_2229_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_arg_1518_);
v___x_2231_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1518_, v_a_2230_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2232_);
lean_dec_ref(v___x_2231_);
if (lean_obj_tag(v_a_2232_) == 1)
{
lean_object* v_val_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v_val_2233_ = lean_ctor_get(v_a_2232_, 0);
lean_inc(v_val_2233_);
lean_dec_ref(v_a_2232_);
lean_inc_ref(v_arg_1520_);
lean_inc_ref(v_fn_1519_);
v___x_2234_ = l_Lean_Expr_app___override(v_fn_1519_, v_arg_1520_);
v___x_2235_ = lean_box(0);
v___x_2236_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2236_, 0, v___x_2234_);
lean_ctor_set(v___x_2236_, 1, v___x_2235_);
lean_ctor_set_uint8(v___x_2236_, sizeof(void*)*2, v___y_2223_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_2237_ = l_Lean_Meta_Simp_mkCongr(v___x_2236_, v_val_2233_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_2218_ = v___y_2223_;
v___y_2219_ = v___x_2237_;
goto v___jp_2217_;
}
else
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
lean_dec(v_a_2232_);
v___x_2238_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2239_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2238_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_2218_ = v___y_2223_;
v___y_2219_ = v___x_2239_;
goto v___jp_2217_;
}
}
else
{
lean_object* v_a_2240_; 
v_a_2240_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2240_);
lean_dec_ref(v___x_2231_);
v___y_2213_ = v___y_2223_;
v_a_2214_ = v_a_2240_;
goto v___jp_2212_;
}
}
else
{
lean_object* v_a_2241_; 
v_a_2241_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2241_);
lean_dec_ref(v___x_2229_);
v___y_2213_ = v___y_2223_;
v_a_2214_ = v_a_2241_;
goto v___jp_2212_;
}
}
else
{
lean_object* v_a_2242_; 
v_a_2242_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2242_);
lean_dec_ref(v___x_2227_);
v___y_2213_ = v___y_2223_;
v_a_2214_ = v_a_2242_;
goto v___jp_2212_;
}
}
else
{
lean_dec_ref(v___y_2224_);
lean_dec_ref(v___y_2222_);
v___y_2213_ = v___y_2223_;
v_a_2214_ = v___y_2225_;
goto v___jp_2212_;
}
}
v___jp_2243_:
{
uint8_t v___x_2248_; 
v___x_2248_ = l_Lean_Exception_isInterrupt(v_a_2247_);
if (v___x_2248_ == 0)
{
uint8_t v___x_2249_; 
lean_inc_ref(v_a_2247_);
v___x_2249_ = l_Lean_Exception_isRuntime(v_a_2247_);
v___y_2222_ = v___y_2244_;
v___y_2223_ = v___y_2245_;
v___y_2224_ = v___y_2246_;
v___y_2225_ = v_a_2247_;
v___y_2226_ = v___x_2249_;
goto v___jp_2221_;
}
else
{
v___y_2222_ = v___y_2244_;
v___y_2223_ = v___y_2245_;
v___y_2224_ = v___y_2246_;
v___y_2225_ = v_a_2247_;
v___y_2226_ = v___x_2248_;
goto v___jp_2221_;
}
}
v___jp_2250_:
{
if (lean_obj_tag(v___y_2254_) == 0)
{
lean_dec_ref(v___y_2253_);
lean_dec_ref(v___y_2251_);
lean_dec_ref(v_binderType_1534_);
lean_dec_ref(v_expr_1305_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
return v___y_2254_;
}
else
{
lean_object* v_a_2255_; 
v_a_2255_ = lean_ctor_get(v___y_2254_, 0);
lean_inc(v_a_2255_);
lean_dec_ref(v___y_2254_);
v___y_2244_ = v___y_2251_;
v___y_2245_ = v___y_2252_;
v___y_2246_ = v___y_2253_;
v_a_2247_ = v_a_2255_;
goto v___jp_2243_;
}
}
v___jp_2256_:
{
uint8_t v___x_2258_; 
v___x_2258_ = 1;
if (v___y_2257_ == 0)
{
lean_object* v___x_2259_; 
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_binderType_1534_);
v___x_2259_ = l_Lean_Meta_isExprDefEq(v_binderType_1534_, v_binderType_1535_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2359_; 
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2262_ = v___x_2259_;
v_isShared_2263_ = v_isSharedCheck_2359_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2259_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2359_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
uint8_t v___x_2264_; 
v___x_2264_ = lean_unbox(v_a_2260_);
lean_dec(v_a_2260_);
if (v___x_2264_ == 0)
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2268_; 
lean_dec_ref(v_binderType_1534_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v___x_2265_ = lean_box(0);
v___x_2266_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2266_, 0, v_expr_1305_);
lean_ctor_set(v___x_2266_, 1, v___x_2265_);
lean_ctor_set_uint8(v___x_2266_, sizeof(void*)*2, v___x_2258_);
if (v_isShared_2263_ == 0)
{
lean_ctor_set(v___x_2262_, 0, v___x_2266_);
v___x_2268_ = v___x_2262_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2266_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
else
{
lean_object* v_options_2270_; uint8_t v_hasTrace_2271_; 
lean_del_object(v___x_2262_);
v_options_2270_ = lean_ctor_get(v_a_1308_, 2);
v_hasTrace_2271_ = lean_ctor_get_uint8(v_options_2270_, sizeof(void*)*1);
if (v_hasTrace_2271_ == 0)
{
lean_object* v___x_2272_; 
v___x_2272_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1520_, v_a_1309_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_a_2273_);
lean_dec_ref(v___x_2272_);
if (lean_obj_tag(v_a_2273_) == 1)
{
lean_object* v_val_2274_; lean_object* v___x_2275_; 
v_val_2274_ = lean_ctor_get(v_a_2273_, 0);
lean_inc(v_val_2274_);
lean_dec_ref(v_a_2273_);
v___x_2275_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1518_, v_a_1309_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2276_);
lean_dec_ref(v___x_2275_);
if (lean_obj_tag(v_a_2276_) == 1)
{
lean_object* v_val_2277_; lean_object* v___x_2278_; 
v_val_2277_ = lean_ctor_get(v_a_2276_, 0);
lean_inc(v_val_2277_);
lean_dec_ref(v_a_2276_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc(v_val_2274_);
v___x_2278_ = lean_infer_type(v_val_2274_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v_a_2279_; lean_object* v___x_2280_; 
v_a_2279_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2279_);
lean_dec_ref(v___x_2278_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc(v_val_2277_);
v___x_2280_ = lean_infer_type(v_val_2277_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; lean_object* v___x_2282_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_a_2281_);
lean_dec_ref(v___x_2280_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_2282_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_val_2274_, v_a_2281_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2282_) == 0)
{
lean_object* v_a_2283_; lean_object* v___x_2284_; 
v_a_2283_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2283_);
lean_dec_ref(v___x_2282_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_binderType_1534_);
v___x_2284_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2283_, v_binderType_1534_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2286_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref(v___x_2284_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_arg_1520_);
v___x_2286_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1520_, v_a_2285_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2287_);
lean_dec_ref(v___x_2286_);
if (lean_obj_tag(v_a_2287_) == 1)
{
lean_object* v_val_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; 
v_val_2288_ = lean_ctor_get(v_a_2287_, 0);
lean_inc(v_val_2288_);
lean_dec_ref(v_a_2287_);
v___x_2289_ = lean_box(0);
lean_inc_ref(v_fn_1519_);
v___x_2290_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2290_, 0, v_fn_1519_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
lean_ctor_set_uint8(v___x_2290_, sizeof(void*)*2, v___x_2258_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_2291_ = l_Lean_Meta_Simp_mkCongr(v___x_2290_, v_val_2288_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v_a_2292_; lean_object* v___x_2293_; 
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
lean_inc(v_a_2292_);
lean_dec_ref(v___x_2291_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_arg_1518_);
v___x_2293_ = l_Lean_Meta_Simp_mkCongrFun(v_a_2292_, v_arg_1518_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1661_ = v___x_2258_;
v___y_1662_ = v_a_2279_;
v___y_1663_ = v_val_2277_;
v___y_1664_ = v___x_2293_;
goto v___jp_1660_;
}
else
{
v___y_1661_ = v___x_2258_;
v___y_1662_ = v_a_2279_;
v___y_1663_ = v_val_2277_;
v___y_1664_ = v___x_2291_;
goto v___jp_1660_;
}
}
else
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
lean_dec(v_a_2287_);
v___x_2294_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2295_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2294_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_1661_ = v___x_2258_;
v___y_1662_ = v_a_2279_;
v___y_1663_ = v_val_2277_;
v___y_1664_ = v___x_2295_;
goto v___jp_1660_;
}
}
else
{
lean_object* v_a_2296_; 
v_a_2296_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2296_);
lean_dec_ref(v___x_2286_);
v___y_1654_ = v___x_2258_;
v___y_1655_ = v_a_2279_;
v___y_1656_ = v_val_2277_;
v_a_1657_ = v_a_2296_;
goto v___jp_1653_;
}
}
else
{
lean_object* v_a_2297_; 
v_a_2297_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2297_);
lean_dec_ref(v___x_2284_);
v___y_1654_ = v___x_2258_;
v___y_1655_ = v_a_2279_;
v___y_1656_ = v_val_2277_;
v_a_1657_ = v_a_2297_;
goto v___jp_1653_;
}
}
else
{
lean_object* v_a_2298_; 
v_a_2298_ = lean_ctor_get(v___x_2282_, 0);
lean_inc(v_a_2298_);
lean_dec_ref(v___x_2282_);
v___y_1654_ = v___x_2258_;
v___y_1655_ = v_a_2279_;
v___y_1656_ = v_val_2277_;
v_a_1657_ = v_a_2298_;
goto v___jp_1653_;
}
}
else
{
lean_object* v_a_2299_; 
lean_dec(v_a_2279_);
lean_dec(v_val_2277_);
lean_dec(v_val_2274_);
v_a_2299_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_a_2299_);
lean_dec_ref(v___x_2280_);
v___y_1623_ = v___x_2258_;
v_a_1624_ = v_a_2299_;
goto v___jp_1622_;
}
}
else
{
lean_object* v_a_2300_; 
lean_dec(v_val_2277_);
lean_dec(v_val_2274_);
v_a_2300_ = lean_ctor_get(v___x_2278_, 0);
lean_inc(v_a_2300_);
lean_dec_ref(v___x_2278_);
v___y_1623_ = v___x_2258_;
v_a_1624_ = v_a_2300_;
goto v___jp_1622_;
}
}
else
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v_a_2303_; 
lean_dec(v_a_2276_);
lean_dec(v_val_2274_);
v___x_2301_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2302_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2301_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref(v___x_2302_);
v___y_1623_ = v___x_2258_;
v_a_1624_ = v_a_2303_;
goto v___jp_1622_;
}
}
else
{
lean_object* v_a_2304_; 
lean_dec(v_val_2274_);
v_a_2304_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2304_);
lean_dec_ref(v___x_2275_);
v___y_1623_ = v___x_2258_;
v_a_1624_ = v_a_2304_;
goto v___jp_1622_;
}
}
else
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v_a_2307_; 
lean_dec(v_a_2273_);
v___x_2305_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2306_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
lean_inc(v_a_2307_);
lean_dec_ref(v___x_2306_);
v___y_1623_ = v___x_2258_;
v_a_1624_ = v_a_2307_;
goto v___jp_1622_;
}
}
else
{
lean_object* v_a_2308_; 
v_a_2308_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_a_2308_);
lean_dec_ref(v___x_2272_);
v___y_1623_ = v___x_2258_;
v_a_1624_ = v_a_2308_;
goto v___jp_1622_;
}
}
else
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v_a_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___f_2315_; lean_object* v___x_2316_; uint8_t v___x_2317_; 
v___x_2309_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__2_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_));
v___x_2310_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___x_2309_, v_a_1308_);
v_a_2311_ = lean_ctor_get(v___x_2310_, 0);
lean_inc(v_a_2311_);
lean_dec_ref(v___x_2310_);
v___x_2312_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_splittingProcedure___closed__1, &l_Lean_Elab_Tactic_NormCast_splittingProcedure___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___closed__1);
lean_inc_ref(v_expr_1305_);
v___x_2313_ = l_Lean_MessageData_ofExpr(v_expr_1305_);
v___x_2314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2312_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
lean_inc_ref(v_expr_1305_);
v___f_2315_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___boxed), 8, 2);
lean_closure_set(v___f_2315_, 0, v___x_2314_);
lean_closure_set(v___f_2315_, 1, v_expr_1305_);
v___x_2316_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_2317_ = lean_unbox(v_a_2311_);
if (v___x_2317_ == 0)
{
lean_object* v___x_2318_; uint8_t v___x_2319_; 
v___x_2318_ = l_Lean_trace_profiler;
v___x_2319_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_2270_, v___x_2318_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2320_; 
lean_dec_ref(v___f_2315_);
lean_dec(v_a_2311_);
v___x_2320_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1520_, v_a_1309_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref(v___x_2320_);
if (lean_obj_tag(v_a_2321_) == 1)
{
lean_object* v_val_2322_; lean_object* v___x_2323_; 
v_val_2322_ = lean_ctor_get(v_a_2321_, 0);
lean_inc(v_val_2322_);
lean_dec_ref(v_a_2321_);
v___x_2323_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1518_, v_a_1309_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref(v___x_2323_);
if (lean_obj_tag(v_a_2324_) == 1)
{
lean_object* v_val_2325_; lean_object* v___x_2326_; 
v_val_2325_ = lean_ctor_get(v_a_2324_, 0);
lean_inc(v_val_2325_);
lean_dec_ref(v_a_2324_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc(v_val_2322_);
v___x_2326_ = lean_infer_type(v_val_2322_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v___x_2328_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2327_);
lean_dec_ref(v___x_2326_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc(v_val_2325_);
v___x_2328_ = lean_infer_type(v_val_2325_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2330_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2329_);
lean_dec_ref(v___x_2328_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_2330_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_val_2322_, v_a_2329_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v___x_2332_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2331_);
lean_dec_ref(v___x_2330_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_binderType_1534_);
v___x_2332_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2331_, v_binderType_1534_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v___x_2334_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2333_);
lean_dec_ref(v___x_2332_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_arg_1520_);
v___x_2334_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1520_, v_a_2333_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref(v___x_2334_);
if (lean_obj_tag(v_a_2335_) == 1)
{
lean_object* v_val_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v_val_2336_ = lean_ctor_get(v_a_2335_, 0);
lean_inc(v_val_2336_);
lean_dec_ref(v_a_2335_);
v___x_2337_ = lean_box(0);
lean_inc_ref(v_fn_1519_);
v___x_2338_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2338_, 0, v_fn_1519_);
lean_ctor_set(v___x_2338_, 1, v___x_2337_);
lean_ctor_set_uint8(v___x_2338_, sizeof(void*)*2, v___x_2258_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
v___x_2339_ = l_Lean_Meta_Simp_mkCongr(v___x_2338_, v_val_2336_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2341_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref(v___x_2339_);
lean_inc(v_a_1309_);
lean_inc_ref(v_a_1308_);
lean_inc(v_a_1307_);
lean_inc_ref(v_a_1306_);
lean_inc_ref(v_arg_1518_);
v___x_2341_ = l_Lean_Meta_Simp_mkCongrFun(v_a_2340_, v_arg_1518_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_2251_ = v_a_2327_;
v___y_2252_ = v___x_2258_;
v___y_2253_ = v_val_2325_;
v___y_2254_ = v___x_2341_;
goto v___jp_2250_;
}
else
{
v___y_2251_ = v_a_2327_;
v___y_2252_ = v___x_2258_;
v___y_2253_ = v_val_2325_;
v___y_2254_ = v___x_2339_;
goto v___jp_2250_;
}
}
else
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
lean_dec(v_a_2335_);
v___x_2342_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2343_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2342_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v___y_2251_ = v_a_2327_;
v___y_2252_ = v___x_2258_;
v___y_2253_ = v_val_2325_;
v___y_2254_ = v___x_2343_;
goto v___jp_2250_;
}
}
else
{
lean_object* v_a_2344_; 
v_a_2344_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2344_);
lean_dec_ref(v___x_2334_);
v___y_2244_ = v_a_2327_;
v___y_2245_ = v___x_2258_;
v___y_2246_ = v_val_2325_;
v_a_2247_ = v_a_2344_;
goto v___jp_2243_;
}
}
else
{
lean_object* v_a_2345_; 
v_a_2345_ = lean_ctor_get(v___x_2332_, 0);
lean_inc(v_a_2345_);
lean_dec_ref(v___x_2332_);
v___y_2244_ = v_a_2327_;
v___y_2245_ = v___x_2258_;
v___y_2246_ = v_val_2325_;
v_a_2247_ = v_a_2345_;
goto v___jp_2243_;
}
}
else
{
lean_object* v_a_2346_; 
v_a_2346_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2346_);
lean_dec_ref(v___x_2330_);
v___y_2244_ = v_a_2327_;
v___y_2245_ = v___x_2258_;
v___y_2246_ = v_val_2325_;
v_a_2247_ = v_a_2346_;
goto v___jp_2243_;
}
}
else
{
lean_object* v_a_2347_; 
lean_dec(v_a_2327_);
lean_dec(v_val_2325_);
lean_dec(v_val_2322_);
v_a_2347_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2347_);
lean_dec_ref(v___x_2328_);
v___y_2213_ = v___x_2258_;
v_a_2214_ = v_a_2347_;
goto v___jp_2212_;
}
}
else
{
lean_object* v_a_2348_; 
lean_dec(v_val_2325_);
lean_dec(v_val_2322_);
v_a_2348_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2348_);
lean_dec_ref(v___x_2326_);
v___y_2213_ = v___x_2258_;
v_a_2214_ = v_a_2348_;
goto v___jp_2212_;
}
}
else
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v_a_2351_; 
lean_dec(v_a_2324_);
lean_dec(v_val_2322_);
v___x_2349_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2350_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2349_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
lean_inc(v_a_2351_);
lean_dec_ref(v___x_2350_);
v___y_2213_ = v___x_2258_;
v_a_2214_ = v_a_2351_;
goto v___jp_2212_;
}
}
else
{
lean_object* v_a_2352_; 
lean_dec(v_val_2322_);
v_a_2352_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2352_);
lean_dec_ref(v___x_2323_);
v___y_2213_ = v___x_2258_;
v_a_2214_ = v_a_2352_;
goto v___jp_2212_;
}
}
else
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v_a_2355_; 
lean_dec(v_a_2321_);
v___x_2353_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2354_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2353_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
v_a_2355_ = lean_ctor_get(v___x_2354_, 0);
lean_inc(v_a_2355_);
lean_dec_ref(v___x_2354_);
v___y_2213_ = v___x_2258_;
v_a_2214_ = v_a_2355_;
goto v___jp_2212_;
}
}
else
{
lean_object* v_a_2356_; 
v_a_2356_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2356_);
lean_dec_ref(v___x_2320_);
v___y_2213_ = v___x_2258_;
v_a_2214_ = v_a_2356_;
goto v___jp_2212_;
}
}
else
{
uint8_t v___x_2357_; 
v___x_2357_ = lean_unbox(v_a_2311_);
lean_dec(v_a_2311_);
lean_inc_ref(v_options_2270_);
v___y_2041_ = v___x_2258_;
v___y_2042_ = v_options_2270_;
v___y_2043_ = v___f_2315_;
v___y_2044_ = v___x_2316_;
v___y_2045_ = v___x_2309_;
v___y_2046_ = v___x_2357_;
goto v___jp_2040_;
}
}
else
{
uint8_t v___x_2358_; 
v___x_2358_ = lean_unbox(v_a_2311_);
lean_dec(v_a_2311_);
lean_inc_ref(v_options_2270_);
v___y_2041_ = v___x_2258_;
v___y_2042_ = v_options_2270_;
v___y_2043_ = v___f_2315_;
v___y_2044_ = v___x_2316_;
v___y_2045_ = v___x_2309_;
v___y_2046_ = v___x_2358_;
goto v___jp_2040_;
}
}
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec_ref(v_binderType_1534_);
lean_dec_ref(v_expr_1305_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v_a_2360_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2259_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2259_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
else
{
lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
lean_dec_ref(v_binderType_1535_);
lean_dec_ref(v_binderType_1534_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v___x_2368_ = lean_box(0);
v___x_2369_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2369_, 0, v_expr_1305_);
lean_ctor_set(v___x_2369_, 1, v___x_2368_);
lean_ctor_set_uint8(v___x_2369_, sizeof(void*)*2, v___x_2258_);
v___x_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2369_);
return v___x_2370_;
}
}
}
else
{
lean_dec_ref(v_a_1522_);
lean_dec_ref(v_body_1533_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
goto v___jp_1526_;
}
}
else
{
lean_dec(v_a_1522_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
goto v___jp_1526_;
}
v___jp_1526_:
{
lean_object* v___x_1527_; uint8_t v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1531_; 
v___x_1527_ = lean_box(0);
v___x_1528_ = 1;
v___x_1529_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1529_, 0, v_expr_1305_);
lean_ctor_set(v___x_1529_, 1, v___x_1527_);
lean_ctor_set_uint8(v___x_1529_, sizeof(void*)*2, v___x_1528_);
if (v_isShared_1525_ == 0)
{
lean_ctor_set(v___x_1524_, 0, v___x_1529_);
v___x_1531_ = v___x_1524_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
lean_dec_ref(v_expr_1305_);
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
v_a_2374_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2376_ = v___x_1521_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_1521_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
else
{
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
goto v___jp_1512_;
}
}
else
{
lean_dec(v_a_1309_);
lean_dec_ref(v_a_1308_);
lean_dec(v_a_1307_);
lean_dec_ref(v_a_1306_);
goto v___jp_1512_;
}
v___jp_1311_:
{
if (v___y_1314_ == 0)
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
lean_dec_ref(v___y_1312_);
v___x_1315_ = lean_box(0);
v___x_1316_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1316_, 0, v_expr_1305_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
lean_ctor_set_uint8(v___x_1316_, sizeof(void*)*2, v___y_1313_);
v___x_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
return v___x_1317_;
}
else
{
lean_object* v___x_1318_; 
lean_dec_ref(v_expr_1305_);
v___x_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1318_, 0, v___y_1312_);
return v___x_1318_;
}
}
v___jp_1319_:
{
uint8_t v___x_1322_; 
v___x_1322_ = l_Lean_Exception_isInterrupt(v_a_1321_);
if (v___x_1322_ == 0)
{
uint8_t v___x_1323_; 
lean_inc_ref(v_a_1321_);
v___x_1323_ = l_Lean_Exception_isRuntime(v_a_1321_);
v___y_1312_ = v_a_1321_;
v___y_1313_ = v___y_1320_;
v___y_1314_ = v___x_1323_;
goto v___jp_1311_;
}
else
{
v___y_1312_ = v_a_1321_;
v___y_1313_ = v___y_1320_;
v___y_1314_ = v___x_1322_;
goto v___jp_1311_;
}
}
v___jp_1324_:
{
if (v___y_1327_ == 0)
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
lean_dec_ref(v___y_1325_);
v___x_1328_ = lean_box(0);
v___x_1329_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1329_, 0, v_expr_1305_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
lean_ctor_set_uint8(v___x_1329_, sizeof(void*)*2, v___y_1326_);
v___x_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
return v___x_1330_;
}
else
{
lean_object* v___x_1331_; 
lean_dec_ref(v_expr_1305_);
v___x_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1331_, 0, v___y_1325_);
return v___x_1331_;
}
}
v___jp_1332_:
{
uint8_t v___x_1335_; 
v___x_1335_ = l_Lean_Exception_isInterrupt(v_a_1334_);
if (v___x_1335_ == 0)
{
uint8_t v___x_1336_; 
lean_inc_ref(v_a_1334_);
v___x_1336_ = l_Lean_Exception_isRuntime(v_a_1334_);
v___y_1325_ = v_a_1334_;
v___y_1326_ = v___y_1333_;
v___y_1327_ = v___x_1336_;
goto v___jp_1324_;
}
else
{
v___y_1325_ = v_a_1334_;
v___y_1326_ = v___y_1333_;
v___y_1327_ = v___x_1335_;
goto v___jp_1324_;
}
}
v___jp_1337_:
{
lean_object* v___x_1347_; double v___x_1348_; double v___x_1349_; double v___x_1350_; double v___x_1351_; double v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1347_ = lean_io_mono_nanos_now();
v___x_1348_ = lean_float_of_nat(v___y_1344_);
v___x_1349_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1);
v___x_1350_ = lean_float_div(v___x_1348_, v___x_1349_);
v___x_1351_ = lean_float_of_nat(v___x_1347_);
v___x_1352_ = lean_float_div(v___x_1351_, v___x_1349_);
v___x_1353_ = lean_box_float(v___x_1350_);
v___x_1354_ = lean_box_float(v___x_1352_);
v___x_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1353_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1356_, 0, v_a_1346_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___x_1357_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___y_1342_, v___y_1338_, v___y_1341_, v___y_1339_, v___y_1345_, v___y_1343_, v___y_1340_, v___x_1356_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec_ref(v___y_1339_);
return v___x_1357_;
}
v___jp_1358_:
{
lean_object* v___x_1368_; 
v___x_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1368_, 0, v_a_1367_);
v___y_1338_ = v___y_1359_;
v___y_1339_ = v___y_1360_;
v___y_1340_ = v___y_1361_;
v___y_1341_ = v___y_1362_;
v___y_1342_ = v___y_1363_;
v___y_1343_ = v___y_1365_;
v___y_1344_ = v___y_1364_;
v___y_1345_ = v___y_1366_;
v_a_1346_ = v___x_1368_;
goto v___jp_1337_;
}
v___jp_1369_:
{
lean_object* v___x_1379_; 
v___x_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1379_, 0, v_a_1378_);
v___y_1338_ = v___y_1370_;
v___y_1339_ = v___y_1371_;
v___y_1340_ = v___y_1372_;
v___y_1341_ = v___y_1373_;
v___y_1342_ = v___y_1374_;
v___y_1343_ = v___y_1376_;
v___y_1344_ = v___y_1375_;
v___y_1345_ = v___y_1377_;
v_a_1346_ = v___x_1379_;
goto v___jp_1337_;
}
v___jp_1380_:
{
if (v___y_1390_ == 0)
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
lean_dec_ref(v___y_1386_);
v___x_1391_ = lean_box(0);
v___x_1392_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1392_, 0, v_expr_1305_);
lean_ctor_set(v___x_1392_, 1, v___x_1391_);
lean_ctor_set_uint8(v___x_1392_, sizeof(void*)*2, v___y_1381_);
v___y_1370_ = v___y_1381_;
v___y_1371_ = v___y_1382_;
v___y_1372_ = v___y_1383_;
v___y_1373_ = v___y_1384_;
v___y_1374_ = v___y_1385_;
v___y_1375_ = v___y_1388_;
v___y_1376_ = v___y_1387_;
v___y_1377_ = v___y_1389_;
v_a_1378_ = v___x_1392_;
goto v___jp_1369_;
}
else
{
lean_dec_ref(v_expr_1305_);
v___y_1359_ = v___y_1381_;
v___y_1360_ = v___y_1382_;
v___y_1361_ = v___y_1383_;
v___y_1362_ = v___y_1384_;
v___y_1363_ = v___y_1385_;
v___y_1364_ = v___y_1388_;
v___y_1365_ = v___y_1387_;
v___y_1366_ = v___y_1389_;
v_a_1367_ = v___y_1386_;
goto v___jp_1358_;
}
}
v___jp_1393_:
{
uint8_t v___x_1403_; 
v___x_1403_ = l_Lean_Exception_isInterrupt(v_a_1402_);
if (v___x_1403_ == 0)
{
uint8_t v___x_1404_; 
lean_inc_ref(v_a_1402_);
v___x_1404_ = l_Lean_Exception_isRuntime(v_a_1402_);
v___y_1381_ = v___y_1394_;
v___y_1382_ = v___y_1395_;
v___y_1383_ = v___y_1396_;
v___y_1384_ = v___y_1397_;
v___y_1385_ = v___y_1398_;
v___y_1386_ = v_a_1402_;
v___y_1387_ = v___y_1400_;
v___y_1388_ = v___y_1399_;
v___y_1389_ = v___y_1401_;
v___y_1390_ = v___x_1404_;
goto v___jp_1380_;
}
else
{
v___y_1381_ = v___y_1394_;
v___y_1382_ = v___y_1395_;
v___y_1383_ = v___y_1396_;
v___y_1384_ = v___y_1397_;
v___y_1385_ = v___y_1398_;
v___y_1386_ = v_a_1402_;
v___y_1387_ = v___y_1400_;
v___y_1388_ = v___y_1399_;
v___y_1389_ = v___y_1401_;
v___y_1390_ = v___x_1403_;
goto v___jp_1380_;
}
}
v___jp_1405_:
{
lean_object* v_a_1415_; 
v_a_1415_ = lean_ctor_get(v_a_1414_, 0);
lean_inc(v_a_1415_);
lean_dec_ref(v_a_1414_);
v___y_1370_ = v___y_1406_;
v___y_1371_ = v___y_1407_;
v___y_1372_ = v___y_1408_;
v___y_1373_ = v___y_1409_;
v___y_1374_ = v___y_1410_;
v___y_1375_ = v___y_1412_;
v___y_1376_ = v___y_1411_;
v___y_1377_ = v___y_1413_;
v_a_1378_ = v_a_1415_;
goto v___jp_1369_;
}
v___jp_1416_:
{
lean_object* v___x_1426_; double v___x_1427_; double v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
v___x_1426_ = lean_io_get_num_heartbeats();
v___x_1427_ = lean_float_of_nat(v___y_1417_);
v___x_1428_ = lean_float_of_nat(v___x_1426_);
v___x_1429_ = lean_box_float(v___x_1427_);
v___x_1430_ = lean_box_float(v___x_1428_);
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1429_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v_a_1425_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
v___x_1433_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___y_1422_, v___y_1418_, v___y_1421_, v___y_1419_, v___y_1424_, v___y_1423_, v___y_1420_, v___x_1432_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_);
lean_dec_ref(v___y_1419_);
return v___x_1433_;
}
v___jp_1434_:
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1444_, 0, v_a_1443_);
v___y_1417_ = v___y_1435_;
v___y_1418_ = v___y_1436_;
v___y_1419_ = v___y_1437_;
v___y_1420_ = v___y_1438_;
v___y_1421_ = v___y_1439_;
v___y_1422_ = v___y_1440_;
v___y_1423_ = v___y_1441_;
v___y_1424_ = v___y_1442_;
v_a_1425_ = v___x_1444_;
goto v___jp_1416_;
}
v___jp_1445_:
{
lean_object* v___x_1455_; 
v___x_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1455_, 0, v_a_1454_);
v___y_1417_ = v___y_1446_;
v___y_1418_ = v___y_1447_;
v___y_1419_ = v___y_1448_;
v___y_1420_ = v___y_1449_;
v___y_1421_ = v___y_1450_;
v___y_1422_ = v___y_1451_;
v___y_1423_ = v___y_1452_;
v___y_1424_ = v___y_1453_;
v_a_1425_ = v___x_1455_;
goto v___jp_1416_;
}
v___jp_1456_:
{
if (v___y_1466_ == 0)
{
lean_object* v___x_1467_; lean_object* v___x_1468_; 
lean_dec_ref(v___y_1462_);
v___x_1467_ = lean_box(0);
v___x_1468_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1468_, 0, v_expr_1305_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
lean_ctor_set_uint8(v___x_1468_, sizeof(void*)*2, v___y_1458_);
v___y_1446_ = v___y_1457_;
v___y_1447_ = v___y_1458_;
v___y_1448_ = v___y_1459_;
v___y_1449_ = v___y_1460_;
v___y_1450_ = v___y_1461_;
v___y_1451_ = v___y_1463_;
v___y_1452_ = v___y_1464_;
v___y_1453_ = v___y_1465_;
v_a_1454_ = v___x_1468_;
goto v___jp_1445_;
}
else
{
lean_dec_ref(v_expr_1305_);
v___y_1435_ = v___y_1457_;
v___y_1436_ = v___y_1458_;
v___y_1437_ = v___y_1459_;
v___y_1438_ = v___y_1460_;
v___y_1439_ = v___y_1461_;
v___y_1440_ = v___y_1463_;
v___y_1441_ = v___y_1464_;
v___y_1442_ = v___y_1465_;
v_a_1443_ = v___y_1462_;
goto v___jp_1434_;
}
}
v___jp_1469_:
{
uint8_t v___x_1479_; 
v___x_1479_ = l_Lean_Exception_isInterrupt(v_a_1478_);
if (v___x_1479_ == 0)
{
uint8_t v___x_1480_; 
lean_inc_ref(v_a_1478_);
v___x_1480_ = l_Lean_Exception_isRuntime(v_a_1478_);
v___y_1457_ = v___y_1470_;
v___y_1458_ = v___y_1471_;
v___y_1459_ = v___y_1472_;
v___y_1460_ = v___y_1473_;
v___y_1461_ = v___y_1474_;
v___y_1462_ = v_a_1478_;
v___y_1463_ = v___y_1475_;
v___y_1464_ = v___y_1476_;
v___y_1465_ = v___y_1477_;
v___y_1466_ = v___x_1480_;
goto v___jp_1456_;
}
else
{
v___y_1457_ = v___y_1470_;
v___y_1458_ = v___y_1471_;
v___y_1459_ = v___y_1472_;
v___y_1460_ = v___y_1473_;
v___y_1461_ = v___y_1474_;
v___y_1462_ = v_a_1478_;
v___y_1463_ = v___y_1475_;
v___y_1464_ = v___y_1476_;
v___y_1465_ = v___y_1477_;
v___y_1466_ = v___x_1479_;
goto v___jp_1456_;
}
}
v___jp_1481_:
{
lean_object* v_a_1491_; 
v_a_1491_ = lean_ctor_get(v_a_1490_, 0);
lean_inc(v_a_1491_);
lean_dec_ref(v_a_1490_);
v___y_1446_ = v___y_1482_;
v___y_1447_ = v___y_1483_;
v___y_1448_ = v___y_1484_;
v___y_1449_ = v___y_1485_;
v___y_1450_ = v___y_1486_;
v___y_1451_ = v___y_1487_;
v___y_1452_ = v___y_1488_;
v___y_1453_ = v___y_1489_;
v_a_1454_ = v_a_1491_;
goto v___jp_1445_;
}
v___jp_1492_:
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1501_; 
v_a_1494_ = lean_ctor_get(v_a_1493_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_a_1493_);
if (v_isSharedCheck_1501_ == 0)
{
v___x_1496_ = v_a_1493_;
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v_a_1493_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1501_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
lean_object* v___x_1499_; 
if (v_isShared_1497_ == 0)
{
lean_ctor_set_tag(v___x_1496_, 0);
v___x_1499_ = v___x_1496_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_a_1494_);
v___x_1499_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
return v___x_1499_;
}
}
}
v___jp_1502_:
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1511_; 
v_a_1504_ = lean_ctor_get(v_a_1503_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_a_1503_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1506_ = v_a_1503_;
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v_a_1503_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1511_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v___x_1509_; 
if (v_isShared_1507_ == 0)
{
lean_ctor_set_tag(v___x_1506_, 0);
v___x_1509_ = v___x_1506_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_a_1504_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
v___jp_1512_:
{
lean_object* v___x_1513_; uint8_t v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1513_ = lean_box(0);
v___x_1514_ = 1;
v___x_1515_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1515_, 0, v_expr_1305_);
lean_ctor_set(v___x_1515_, 1, v___x_1513_);
lean_ctor_set_uint8(v___x_1515_, sizeof(void*)*2, v___x_1514_);
v___x_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
return v___x_1516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___boxed(lean_object* v_expr_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure(v_expr_2382_, v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
return v_res_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___redArg(lean_object* v_cls_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v_options_2392_; uint8_t v_hasTrace_2393_; 
v_options_2392_ = lean_ctor_get(v___y_2390_, 2);
v_hasTrace_2393_ = lean_ctor_get_uint8(v_options_2392_, sizeof(void*)*1);
if (v_hasTrace_2393_ == 0)
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
lean_dec(v_cls_2389_);
v___x_2394_ = lean_box(v_hasTrace_2393_);
v___x_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2394_);
return v___x_2395_;
}
else
{
lean_object* v_inheritedTraceOptions_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; uint8_t v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v_inheritedTraceOptions_2396_ = lean_ctor_get(v___y_2390_, 13);
v___x_2397_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__1));
v___x_2398_ = l_Lean_Name_append(v___x_2397_, v_cls_2389_);
v___x_2399_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2396_, v_options_2392_, v___x_2398_);
lean_dec(v___x_2398_);
v___x_2400_ = lean_box(v___x_2399_);
v___x_2401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2400_);
return v___x_2401_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___redArg___boxed(lean_object* v_cls_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___redArg(v_cls_2402_, v___y_2403_);
lean_dec_ref(v___y_2403_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_prove_spec__0(lean_object* v_cls_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v___x_2415_; 
v___x_2415_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___redArg(v_cls_2406_, v___y_2412_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___boxed(lean_object* v_cls_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_prove_spec__0(v_cls_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v___y_2417_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__1___redArg(lean_object* v___y_2426_){
_start:
{
lean_object* v___x_2428_; lean_object* v_traceState_2429_; lean_object* v_traces_2430_; lean_object* v___x_2431_; lean_object* v_traceState_2432_; lean_object* v_env_2433_; lean_object* v_nextMacroScope_2434_; lean_object* v_ngen_2435_; lean_object* v_auxDeclNGen_2436_; lean_object* v_cache_2437_; lean_object* v_messages_2438_; lean_object* v_infoState_2439_; lean_object* v_snapshotTasks_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2461_; 
v___x_2428_ = lean_st_ref_get(v___y_2426_);
v_traceState_2429_ = lean_ctor_get(v___x_2428_, 4);
lean_inc_ref(v_traceState_2429_);
lean_dec(v___x_2428_);
v_traces_2430_ = lean_ctor_get(v_traceState_2429_, 0);
lean_inc_ref(v_traces_2430_);
lean_dec_ref(v_traceState_2429_);
v___x_2431_ = lean_st_ref_take(v___y_2426_);
v_traceState_2432_ = lean_ctor_get(v___x_2431_, 4);
v_env_2433_ = lean_ctor_get(v___x_2431_, 0);
v_nextMacroScope_2434_ = lean_ctor_get(v___x_2431_, 1);
v_ngen_2435_ = lean_ctor_get(v___x_2431_, 2);
v_auxDeclNGen_2436_ = lean_ctor_get(v___x_2431_, 3);
v_cache_2437_ = lean_ctor_get(v___x_2431_, 5);
v_messages_2438_ = lean_ctor_get(v___x_2431_, 6);
v_infoState_2439_ = lean_ctor_get(v___x_2431_, 7);
v_snapshotTasks_2440_ = lean_ctor_get(v___x_2431_, 8);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2442_ = v___x_2431_;
v_isShared_2443_ = v_isSharedCheck_2461_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_snapshotTasks_2440_);
lean_inc(v_infoState_2439_);
lean_inc(v_messages_2438_);
lean_inc(v_cache_2437_);
lean_inc(v_traceState_2432_);
lean_inc(v_auxDeclNGen_2436_);
lean_inc(v_ngen_2435_);
lean_inc(v_nextMacroScope_2434_);
lean_inc(v_env_2433_);
lean_dec(v___x_2431_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2461_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
uint64_t v_tid_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2459_; 
v_tid_2444_ = lean_ctor_get_uint64(v_traceState_2432_, sizeof(void*)*1);
v_isSharedCheck_2459_ = !lean_is_exclusive(v_traceState_2432_);
if (v_isSharedCheck_2459_ == 0)
{
lean_object* v_unused_2460_; 
v_unused_2460_ = lean_ctor_get(v_traceState_2432_, 0);
lean_dec(v_unused_2460_);
v___x_2446_ = v_traceState_2432_;
v_isShared_2447_ = v_isSharedCheck_2459_;
goto v_resetjp_2445_;
}
else
{
lean_dec(v_traceState_2432_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2459_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2452_; 
v___x_2448_ = lean_unsigned_to_nat(32u);
v___x_2449_ = lean_mk_empty_array_with_capacity(v___x_2448_);
lean_dec_ref(v___x_2449_);
v___x_2450_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg___closed__1);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 0, v___x_2450_);
v___x_2452_ = v___x_2446_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2450_);
lean_ctor_set_uint64(v_reuseFailAlloc_2458_, sizeof(void*)*1, v_tid_2444_);
v___x_2452_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2454_; 
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 4, v___x_2452_);
v___x_2454_ = v___x_2442_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_env_2433_);
lean_ctor_set(v_reuseFailAlloc_2457_, 1, v_nextMacroScope_2434_);
lean_ctor_set(v_reuseFailAlloc_2457_, 2, v_ngen_2435_);
lean_ctor_set(v_reuseFailAlloc_2457_, 3, v_auxDeclNGen_2436_);
lean_ctor_set(v_reuseFailAlloc_2457_, 4, v___x_2452_);
lean_ctor_set(v_reuseFailAlloc_2457_, 5, v_cache_2437_);
lean_ctor_set(v_reuseFailAlloc_2457_, 6, v_messages_2438_);
lean_ctor_set(v_reuseFailAlloc_2457_, 7, v_infoState_2439_);
lean_ctor_set(v_reuseFailAlloc_2457_, 8, v_snapshotTasks_2440_);
v___x_2454_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2455_ = lean_st_ref_set(v___y_2426_, v___x_2454_);
v___x_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2456_, 0, v_traces_2430_);
return v___x_2456_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__1___redArg___boxed(lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__1___redArg(v___y_2462_);
lean_dec(v___y_2462_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__1(lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__1___redArg(v___y_2471_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__1___boxed(lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__1(v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v___y_2474_);
return v_res_2482_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2484_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__0));
v___x_2485_ = l_Lean_stringToMessageData(v___x_2484_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lam__0(lean_object* v_e_2486_, lean_object* v_x_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2496_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__1, &l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__1);
v___x_2497_ = l_Lean_MessageData_ofExpr(v_e_2486_);
v___x_2498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2496_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
v___x_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lam__0___boxed(lean_object* v_e_2500_, lean_object* v_x_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l_Lean_Elab_Tactic_NormCast_prove___lam__0(v_e_2500_, v_x_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v_x_2501_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__3___redArg(lean_object* v_oldTraces_2511_, lean_object* v_data_2512_, lean_object* v_ref_2513_, lean_object* v_msg_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v_fileName_2520_; lean_object* v_fileMap_2521_; lean_object* v_options_2522_; lean_object* v_currRecDepth_2523_; lean_object* v_maxRecDepth_2524_; lean_object* v_ref_2525_; lean_object* v_currNamespace_2526_; lean_object* v_openDecls_2527_; lean_object* v_initHeartbeats_2528_; lean_object* v_maxHeartbeats_2529_; lean_object* v_quotContext_2530_; lean_object* v_currMacroScope_2531_; uint8_t v_diag_2532_; lean_object* v_cancelTk_x3f_2533_; uint8_t v_suppressElabErrors_2534_; lean_object* v_inheritedTraceOptions_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2590_; 
v_fileName_2520_ = lean_ctor_get(v___y_2517_, 0);
v_fileMap_2521_ = lean_ctor_get(v___y_2517_, 1);
v_options_2522_ = lean_ctor_get(v___y_2517_, 2);
v_currRecDepth_2523_ = lean_ctor_get(v___y_2517_, 3);
v_maxRecDepth_2524_ = lean_ctor_get(v___y_2517_, 4);
v_ref_2525_ = lean_ctor_get(v___y_2517_, 5);
v_currNamespace_2526_ = lean_ctor_get(v___y_2517_, 6);
v_openDecls_2527_ = lean_ctor_get(v___y_2517_, 7);
v_initHeartbeats_2528_ = lean_ctor_get(v___y_2517_, 8);
v_maxHeartbeats_2529_ = lean_ctor_get(v___y_2517_, 9);
v_quotContext_2530_ = lean_ctor_get(v___y_2517_, 10);
v_currMacroScope_2531_ = lean_ctor_get(v___y_2517_, 11);
v_diag_2532_ = lean_ctor_get_uint8(v___y_2517_, sizeof(void*)*14);
v_cancelTk_x3f_2533_ = lean_ctor_get(v___y_2517_, 12);
v_suppressElabErrors_2534_ = lean_ctor_get_uint8(v___y_2517_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2535_ = lean_ctor_get(v___y_2517_, 13);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___y_2517_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2537_ = v___y_2517_;
v_isShared_2538_ = v_isSharedCheck_2590_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_inheritedTraceOptions_2535_);
lean_inc(v_cancelTk_x3f_2533_);
lean_inc(v_currMacroScope_2531_);
lean_inc(v_quotContext_2530_);
lean_inc(v_maxHeartbeats_2529_);
lean_inc(v_initHeartbeats_2528_);
lean_inc(v_openDecls_2527_);
lean_inc(v_currNamespace_2526_);
lean_inc(v_ref_2525_);
lean_inc(v_maxRecDepth_2524_);
lean_inc(v_currRecDepth_2523_);
lean_inc(v_options_2522_);
lean_inc(v_fileMap_2521_);
lean_inc(v_fileName_2520_);
lean_dec(v___y_2517_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2590_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2539_; lean_object* v_traceState_2540_; lean_object* v_traces_2541_; lean_object* v_ref_2542_; lean_object* v___x_2544_; 
v___x_2539_ = lean_st_ref_get(v___y_2518_);
v_traceState_2540_ = lean_ctor_get(v___x_2539_, 4);
lean_inc_ref(v_traceState_2540_);
lean_dec(v___x_2539_);
v_traces_2541_ = lean_ctor_get(v_traceState_2540_, 0);
lean_inc_ref(v_traces_2541_);
lean_dec_ref(v_traceState_2540_);
v_ref_2542_ = l_Lean_replaceRef(v_ref_2513_, v_ref_2525_);
lean_dec(v_ref_2525_);
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 5, v_ref_2542_);
v___x_2544_ = v___x_2537_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_fileName_2520_);
lean_ctor_set(v_reuseFailAlloc_2589_, 1, v_fileMap_2521_);
lean_ctor_set(v_reuseFailAlloc_2589_, 2, v_options_2522_);
lean_ctor_set(v_reuseFailAlloc_2589_, 3, v_currRecDepth_2523_);
lean_ctor_set(v_reuseFailAlloc_2589_, 4, v_maxRecDepth_2524_);
lean_ctor_set(v_reuseFailAlloc_2589_, 5, v_ref_2542_);
lean_ctor_set(v_reuseFailAlloc_2589_, 6, v_currNamespace_2526_);
lean_ctor_set(v_reuseFailAlloc_2589_, 7, v_openDecls_2527_);
lean_ctor_set(v_reuseFailAlloc_2589_, 8, v_initHeartbeats_2528_);
lean_ctor_set(v_reuseFailAlloc_2589_, 9, v_maxHeartbeats_2529_);
lean_ctor_set(v_reuseFailAlloc_2589_, 10, v_quotContext_2530_);
lean_ctor_set(v_reuseFailAlloc_2589_, 11, v_currMacroScope_2531_);
lean_ctor_set(v_reuseFailAlloc_2589_, 12, v_cancelTk_x3f_2533_);
lean_ctor_set(v_reuseFailAlloc_2589_, 13, v_inheritedTraceOptions_2535_);
lean_ctor_set_uint8(v_reuseFailAlloc_2589_, sizeof(void*)*14, v_diag_2532_);
lean_ctor_set_uint8(v_reuseFailAlloc_2589_, sizeof(void*)*14 + 1, v_suppressElabErrors_2534_);
v___x_2544_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
lean_object* v___x_2545_; size_t v_sz_2546_; size_t v___x_2547_; lean_object* v___x_2548_; lean_object* v_msg_2549_; lean_object* v___x_2550_; lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2588_; 
v___x_2545_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2541_);
lean_dec_ref(v_traces_2541_);
v_sz_2546_ = lean_array_size(v___x_2545_);
v___x_2547_ = ((size_t)0ULL);
v___x_2548_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__5(v_sz_2546_, v___x_2547_, v___x_2545_);
v_msg_2549_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2549_, 0, v_data_2512_);
lean_ctor_set(v_msg_2549_, 1, v_msg_2514_);
lean_ctor_set(v_msg_2549_, 2, v___x_2548_);
v___x_2550_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__6(v_msg_2549_, v___y_2515_, v___y_2516_, v___x_2544_, v___y_2518_);
lean_dec_ref(v___x_2544_);
v_a_2551_ = lean_ctor_get(v___x_2550_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2550_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2553_ = v___x_2550_;
v_isShared_2554_ = v_isSharedCheck_2588_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2550_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2588_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2555_; lean_object* v_traceState_2556_; lean_object* v_env_2557_; lean_object* v_nextMacroScope_2558_; lean_object* v_ngen_2559_; lean_object* v_auxDeclNGen_2560_; lean_object* v_cache_2561_; lean_object* v_messages_2562_; lean_object* v_infoState_2563_; lean_object* v_snapshotTasks_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2587_; 
v___x_2555_ = lean_st_ref_take(v___y_2518_);
v_traceState_2556_ = lean_ctor_get(v___x_2555_, 4);
v_env_2557_ = lean_ctor_get(v___x_2555_, 0);
v_nextMacroScope_2558_ = lean_ctor_get(v___x_2555_, 1);
v_ngen_2559_ = lean_ctor_get(v___x_2555_, 2);
v_auxDeclNGen_2560_ = lean_ctor_get(v___x_2555_, 3);
v_cache_2561_ = lean_ctor_get(v___x_2555_, 5);
v_messages_2562_ = lean_ctor_get(v___x_2555_, 6);
v_infoState_2563_ = lean_ctor_get(v___x_2555_, 7);
v_snapshotTasks_2564_ = lean_ctor_get(v___x_2555_, 8);
v_isSharedCheck_2587_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2587_ == 0)
{
v___x_2566_ = v___x_2555_;
v_isShared_2567_ = v_isSharedCheck_2587_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_snapshotTasks_2564_);
lean_inc(v_infoState_2563_);
lean_inc(v_messages_2562_);
lean_inc(v_cache_2561_);
lean_inc(v_traceState_2556_);
lean_inc(v_auxDeclNGen_2560_);
lean_inc(v_ngen_2559_);
lean_inc(v_nextMacroScope_2558_);
lean_inc(v_env_2557_);
lean_dec(v___x_2555_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2587_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
uint64_t v_tid_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2585_; 
v_tid_2568_ = lean_ctor_get_uint64(v_traceState_2556_, sizeof(void*)*1);
v_isSharedCheck_2585_ = !lean_is_exclusive(v_traceState_2556_);
if (v_isSharedCheck_2585_ == 0)
{
lean_object* v_unused_2586_; 
v_unused_2586_ = lean_ctor_get(v_traceState_2556_, 0);
lean_dec(v_unused_2586_);
v___x_2570_ = v_traceState_2556_;
v_isShared_2571_ = v_isSharedCheck_2585_;
goto v_resetjp_2569_;
}
else
{
lean_dec(v_traceState_2556_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2585_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2575_; 
v___x_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2572_, 0, v_ref_2513_);
lean_ctor_set(v___x_2572_, 1, v_a_2551_);
v___x_2573_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2511_, v___x_2572_);
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 0, v___x_2573_);
v___x_2575_ = v___x_2570_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2573_);
lean_ctor_set_uint64(v_reuseFailAlloc_2584_, sizeof(void*)*1, v_tid_2568_);
v___x_2575_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
lean_object* v___x_2577_; 
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 4, v___x_2575_);
v___x_2577_ = v___x_2566_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_env_2557_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v_nextMacroScope_2558_);
lean_ctor_set(v_reuseFailAlloc_2583_, 2, v_ngen_2559_);
lean_ctor_set(v_reuseFailAlloc_2583_, 3, v_auxDeclNGen_2560_);
lean_ctor_set(v_reuseFailAlloc_2583_, 4, v___x_2575_);
lean_ctor_set(v_reuseFailAlloc_2583_, 5, v_cache_2561_);
lean_ctor_set(v_reuseFailAlloc_2583_, 6, v_messages_2562_);
lean_ctor_set(v_reuseFailAlloc_2583_, 7, v_infoState_2563_);
lean_ctor_set(v_reuseFailAlloc_2583_, 8, v_snapshotTasks_2564_);
v___x_2577_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2581_; 
v___x_2578_ = lean_st_ref_set(v___y_2518_, v___x_2577_);
v___x_2579_ = lean_box(0);
if (v_isShared_2554_ == 0)
{
lean_ctor_set(v___x_2553_, 0, v___x_2579_);
v___x_2581_ = v___x_2553_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2579_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__3___redArg___boxed(lean_object* v_oldTraces_2591_, lean_object* v_data_2592_, lean_object* v_ref_2593_, lean_object* v_msg_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__3___redArg(v_oldTraces_2591_, v_data_2592_, v_ref_2593_, v_msg_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_);
lean_dec(v___y_2598_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__4___redArg(lean_object* v_x_2601_){
_start:
{
if (lean_obj_tag(v_x_2601_) == 0)
{
lean_object* v_a_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2610_; 
v_a_2603_ = lean_ctor_get(v_x_2601_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v_x_2601_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2605_ = v_x_2601_;
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_a_2603_);
lean_dec(v_x_2601_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2610_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2608_; 
if (v_isShared_2606_ == 0)
{
lean_ctor_set_tag(v___x_2605_, 1);
v___x_2608_ = v___x_2605_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2603_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
v_a_2611_ = lean_ctor_get(v_x_2601_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v_x_2601_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v_x_2601_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v_x_2601_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
lean_ctor_set_tag(v___x_2613_, 0);
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__4___redArg___boxed(lean_object* v_x_2619_, lean_object* v___y_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__4___redArg(v_x_2619_);
return v_res_2621_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__2(lean_object* v_e_2622_){
_start:
{
if (lean_obj_tag(v_e_2622_) == 0)
{
uint8_t v___x_2623_; 
v___x_2623_ = 2;
return v___x_2623_;
}
else
{
lean_object* v_a_2624_; 
v_a_2624_ = lean_ctor_get(v_e_2622_, 0);
if (lean_obj_tag(v_a_2624_) == 0)
{
uint8_t v___x_2625_; 
v___x_2625_ = 1;
return v___x_2625_;
}
else
{
uint8_t v___x_2626_; 
v___x_2626_ = 0;
return v___x_2626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__2___boxed(lean_object* v_e_2627_){
_start:
{
uint8_t v_res_2628_; lean_object* v_r_2629_; 
v_res_2628_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__2(v_e_2627_);
lean_dec_ref(v_e_2627_);
v_r_2629_ = lean_box(v_res_2628_);
return v_r_2629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2(lean_object* v_cls_2630_, uint8_t v_collapsed_2631_, lean_object* v_tag_2632_, lean_object* v_opts_2633_, uint8_t v_clsEnabled_2634_, lean_object* v_oldTraces_2635_, lean_object* v_msg_2636_, lean_object* v_resStartStop_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v_fst_2646_; lean_object* v_snd_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2745_; 
v_fst_2646_ = lean_ctor_get(v_resStartStop_2637_, 0);
v_snd_2647_ = lean_ctor_get(v_resStartStop_2637_, 1);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_resStartStop_2637_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2649_ = v_resStartStop_2637_;
v_isShared_2650_ = v_isSharedCheck_2745_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_snd_2647_);
lean_inc(v_fst_2646_);
lean_dec(v_resStartStop_2637_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2745_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v_data_2654_; lean_object* v_fst_2665_; lean_object* v_snd_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2744_; 
v_fst_2665_ = lean_ctor_get(v_snd_2647_, 0);
v_snd_2666_ = lean_ctor_get(v_snd_2647_, 1);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_snd_2647_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2668_ = v_snd_2647_;
v_isShared_2669_ = v_isSharedCheck_2744_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_snd_2666_);
lean_inc(v_fst_2665_);
lean_dec(v_snd_2647_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2744_;
goto v_resetjp_2667_;
}
v___jp_2651_:
{
lean_object* v___x_2655_; 
v___x_2655_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__3___redArg(v_oldTraces_2635_, v_data_2654_, v___y_2652_, v___y_2653_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec(v___y_2644_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v___x_2656_; 
lean_dec_ref(v___x_2655_);
v___x_2656_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__4___redArg(v_fst_2646_);
return v___x_2656_;
}
else
{
lean_object* v_a_2657_; lean_object* v___x_2659_; uint8_t v_isShared_2660_; uint8_t v_isSharedCheck_2664_; 
lean_dec(v_fst_2646_);
v_a_2657_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2664_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2664_ == 0)
{
v___x_2659_ = v___x_2655_;
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
else
{
lean_inc(v_a_2657_);
lean_dec(v___x_2655_);
v___x_2659_ = lean_box(0);
v_isShared_2660_ = v_isSharedCheck_2664_;
goto v_resetjp_2658_;
}
v_resetjp_2658_:
{
lean_object* v___x_2662_; 
if (v_isShared_2660_ == 0)
{
v___x_2662_ = v___x_2659_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2663_; 
v_reuseFailAlloc_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2663_, 0, v_a_2657_);
v___x_2662_ = v_reuseFailAlloc_2663_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
return v___x_2662_;
}
}
}
}
v_resetjp_2667_:
{
lean_object* v___x_2670_; uint8_t v___x_2671_; lean_object* v___y_2673_; lean_object* v_a_2674_; uint8_t v___y_2698_; double v___y_2729_; 
v___x_2670_ = l_Lean_trace_profiler;
v___x_2671_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_opts_2633_, v___x_2670_);
if (v___x_2671_ == 0)
{
v___y_2698_ = v___x_2671_;
goto v___jp_2697_;
}
else
{
lean_object* v___x_2734_; uint8_t v___x_2735_; 
v___x_2734_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2735_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_opts_2633_, v___x_2734_);
if (v___x_2735_ == 0)
{
lean_object* v___x_2736_; lean_object* v___x_2737_; double v___x_2738_; double v___x_2739_; double v___x_2740_; 
v___x_2736_ = l_Lean_trace_profiler_threshold;
v___x_2737_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__6(v_opts_2633_, v___x_2736_);
v___x_2738_ = lean_float_of_nat(v___x_2737_);
v___x_2739_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__5);
v___x_2740_ = lean_float_div(v___x_2738_, v___x_2739_);
v___y_2729_ = v___x_2740_;
goto v___jp_2728_;
}
else
{
lean_object* v___x_2741_; lean_object* v___x_2742_; double v___x_2743_; 
v___x_2741_ = l_Lean_trace_profiler_threshold;
v___x_2742_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__6(v_opts_2633_, v___x_2741_);
v___x_2743_ = lean_float_of_nat(v___x_2742_);
v___y_2729_ = v___x_2743_;
goto v___jp_2728_;
}
}
v___jp_2672_:
{
uint8_t v_result_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2680_; 
v_result_2675_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__2(v_fst_2646_);
v___x_2676_ = l_Lean_TraceResult_toEmoji(v_result_2675_);
v___x_2677_ = l_Lean_stringToMessageData(v___x_2676_);
v___x_2678_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1);
if (v_isShared_2669_ == 0)
{
lean_ctor_set_tag(v___x_2668_, 7);
lean_ctor_set(v___x_2668_, 1, v___x_2678_);
lean_ctor_set(v___x_2668_, 0, v___x_2677_);
v___x_2680_ = v___x_2668_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v___x_2677_);
lean_ctor_set(v_reuseFailAlloc_2691_, 1, v___x_2678_);
v___x_2680_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
lean_object* v_m_2682_; 
if (v_isShared_2650_ == 0)
{
lean_ctor_set_tag(v___x_2649_, 7);
lean_ctor_set(v___x_2649_, 1, v_a_2674_);
lean_ctor_set(v___x_2649_, 0, v___x_2680_);
v_m_2682_ = v___x_2649_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v___x_2680_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v_a_2674_);
v_m_2682_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; double v___x_2685_; lean_object* v_data_2686_; 
v___x_2683_ = lean_box(v_result_2675_);
v___x_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2683_);
v___x_2685_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2);
lean_inc_ref(v_tag_2632_);
lean_inc_ref(v___x_2684_);
lean_inc(v_cls_2630_);
v_data_2686_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2686_, 0, v_cls_2630_);
lean_ctor_set(v_data_2686_, 1, v___x_2684_);
lean_ctor_set(v_data_2686_, 2, v_tag_2632_);
lean_ctor_set_float(v_data_2686_, sizeof(void*)*3, v___x_2685_);
lean_ctor_set_float(v_data_2686_, sizeof(void*)*3 + 8, v___x_2685_);
lean_ctor_set_uint8(v_data_2686_, sizeof(void*)*3 + 16, v_collapsed_2631_);
if (v___x_2671_ == 0)
{
lean_dec_ref(v___x_2684_);
lean_dec(v_snd_2666_);
lean_dec(v_fst_2665_);
lean_dec_ref(v_tag_2632_);
lean_dec(v_cls_2630_);
v___y_2652_ = v___y_2673_;
v___y_2653_ = v_m_2682_;
v_data_2654_ = v_data_2686_;
goto v___jp_2651_;
}
else
{
lean_object* v_data_2687_; double v___x_2688_; double v___x_2689_; 
lean_dec_ref(v_data_2686_);
v_data_2687_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2687_, 0, v_cls_2630_);
lean_ctor_set(v_data_2687_, 1, v___x_2684_);
lean_ctor_set(v_data_2687_, 2, v_tag_2632_);
v___x_2688_ = lean_unbox_float(v_fst_2665_);
lean_dec(v_fst_2665_);
lean_ctor_set_float(v_data_2687_, sizeof(void*)*3, v___x_2688_);
v___x_2689_ = lean_unbox_float(v_snd_2666_);
lean_dec(v_snd_2666_);
lean_ctor_set_float(v_data_2687_, sizeof(void*)*3 + 8, v___x_2689_);
lean_ctor_set_uint8(v_data_2687_, sizeof(void*)*3 + 16, v_collapsed_2631_);
v___y_2652_ = v___y_2673_;
v___y_2653_ = v_m_2682_;
v_data_2654_ = v_data_2687_;
goto v___jp_2651_;
}
}
}
}
v___jp_2692_:
{
lean_object* v_ref_2693_; lean_object* v___x_2694_; 
v_ref_2693_ = lean_ctor_get(v___y_2643_, 5);
lean_inc(v___y_2644_);
lean_inc_ref(v___y_2643_);
lean_inc(v___y_2642_);
lean_inc_ref(v___y_2641_);
lean_inc(v_fst_2646_);
v___x_2694_ = lean_apply_9(v_msg_2636_, v_fst_2646_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, lean_box(0));
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2695_);
lean_dec_ref(v___x_2694_);
lean_inc(v_ref_2693_);
v___y_2673_ = v_ref_2693_;
v_a_2674_ = v_a_2695_;
goto v___jp_2672_;
}
else
{
lean_object* v___x_2696_; 
lean_dec_ref(v___x_2694_);
v___x_2696_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__4);
lean_inc(v_ref_2693_);
v___y_2673_ = v_ref_2693_;
v_a_2674_ = v___x_2696_;
goto v___jp_2672_;
}
}
v___jp_2697_:
{
if (v_clsEnabled_2634_ == 0)
{
if (v___y_2698_ == 0)
{
lean_object* v___x_2699_; lean_object* v_traceState_2700_; lean_object* v_env_2701_; lean_object* v_nextMacroScope_2702_; lean_object* v_ngen_2703_; lean_object* v_auxDeclNGen_2704_; lean_object* v_cache_2705_; lean_object* v_messages_2706_; lean_object* v_infoState_2707_; lean_object* v_snapshotTasks_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2727_; 
lean_del_object(v___x_2668_);
lean_dec(v_snd_2666_);
lean_dec(v_fst_2665_);
lean_del_object(v___x_2649_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v_msg_2636_);
lean_dec_ref(v_tag_2632_);
lean_dec(v_cls_2630_);
v___x_2699_ = lean_st_ref_take(v___y_2644_);
v_traceState_2700_ = lean_ctor_get(v___x_2699_, 4);
v_env_2701_ = lean_ctor_get(v___x_2699_, 0);
v_nextMacroScope_2702_ = lean_ctor_get(v___x_2699_, 1);
v_ngen_2703_ = lean_ctor_get(v___x_2699_, 2);
v_auxDeclNGen_2704_ = lean_ctor_get(v___x_2699_, 3);
v_cache_2705_ = lean_ctor_get(v___x_2699_, 5);
v_messages_2706_ = lean_ctor_get(v___x_2699_, 6);
v_infoState_2707_ = lean_ctor_get(v___x_2699_, 7);
v_snapshotTasks_2708_ = lean_ctor_get(v___x_2699_, 8);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2699_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2710_ = v___x_2699_;
v_isShared_2711_ = v_isSharedCheck_2727_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_snapshotTasks_2708_);
lean_inc(v_infoState_2707_);
lean_inc(v_messages_2706_);
lean_inc(v_cache_2705_);
lean_inc(v_traceState_2700_);
lean_inc(v_auxDeclNGen_2704_);
lean_inc(v_ngen_2703_);
lean_inc(v_nextMacroScope_2702_);
lean_inc(v_env_2701_);
lean_dec(v___x_2699_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2727_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
uint64_t v_tid_2712_; lean_object* v_traces_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2726_; 
v_tid_2712_ = lean_ctor_get_uint64(v_traceState_2700_, sizeof(void*)*1);
v_traces_2713_ = lean_ctor_get(v_traceState_2700_, 0);
v_isSharedCheck_2726_ = !lean_is_exclusive(v_traceState_2700_);
if (v_isSharedCheck_2726_ == 0)
{
v___x_2715_ = v_traceState_2700_;
v_isShared_2716_ = v_isSharedCheck_2726_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_traces_2713_);
lean_dec(v_traceState_2700_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2726_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2717_; lean_object* v___x_2719_; 
v___x_2717_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2635_, v_traces_2713_);
lean_dec_ref(v_traces_2713_);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 0, v___x_2717_);
v___x_2719_ = v___x_2715_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2717_);
lean_ctor_set_uint64(v_reuseFailAlloc_2725_, sizeof(void*)*1, v_tid_2712_);
v___x_2719_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
lean_object* v___x_2721_; 
if (v_isShared_2711_ == 0)
{
lean_ctor_set(v___x_2710_, 4, v___x_2719_);
v___x_2721_ = v___x_2710_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_env_2701_);
lean_ctor_set(v_reuseFailAlloc_2724_, 1, v_nextMacroScope_2702_);
lean_ctor_set(v_reuseFailAlloc_2724_, 2, v_ngen_2703_);
lean_ctor_set(v_reuseFailAlloc_2724_, 3, v_auxDeclNGen_2704_);
lean_ctor_set(v_reuseFailAlloc_2724_, 4, v___x_2719_);
lean_ctor_set(v_reuseFailAlloc_2724_, 5, v_cache_2705_);
lean_ctor_set(v_reuseFailAlloc_2724_, 6, v_messages_2706_);
lean_ctor_set(v_reuseFailAlloc_2724_, 7, v_infoState_2707_);
lean_ctor_set(v_reuseFailAlloc_2724_, 8, v_snapshotTasks_2708_);
v___x_2721_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2722_ = lean_st_ref_set(v___y_2644_, v___x_2721_);
lean_dec(v___y_2644_);
v___x_2723_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__4___redArg(v_fst_2646_);
return v___x_2723_;
}
}
}
}
}
else
{
goto v___jp_2692_;
}
}
else
{
goto v___jp_2692_;
}
}
v___jp_2728_:
{
double v___x_2730_; double v___x_2731_; double v___x_2732_; uint8_t v___x_2733_; 
v___x_2730_ = lean_unbox_float(v_snd_2666_);
v___x_2731_ = lean_unbox_float(v_fst_2665_);
v___x_2732_ = lean_float_sub(v___x_2730_, v___x_2731_);
v___x_2733_ = lean_float_decLt(v___y_2729_, v___x_2732_);
v___y_2698_ = v___x_2733_;
goto v___jp_2697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2___boxed(lean_object* v_cls_2746_, lean_object* v_collapsed_2747_, lean_object* v_tag_2748_, lean_object* v_opts_2749_, lean_object* v_clsEnabled_2750_, lean_object* v_oldTraces_2751_, lean_object* v_msg_2752_, lean_object* v_resStartStop_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
uint8_t v_collapsed_boxed_2762_; uint8_t v_clsEnabled_boxed_2763_; lean_object* v_res_2764_; 
v_collapsed_boxed_2762_ = lean_unbox(v_collapsed_2747_);
v_clsEnabled_boxed_2763_ = lean_unbox(v_clsEnabled_2750_);
v_res_2764_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2(v_cls_2746_, v_collapsed_boxed_2762_, v_tag_2748_, v_opts_2749_, v_clsEnabled_boxed_2763_, v_oldTraces_2751_, v_msg_2752_, v_resStartStop_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
lean_dec_ref(v_opts_2749_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove(lean_object* v_e_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_){
_start:
{
lean_object* v_____do__lift_2775_; lean_object* v_options_2788_; uint8_t v_hasTrace_2789_; 
v_options_2788_ = lean_ctor_get(v_a_2771_, 2);
v_hasTrace_2789_ = lean_ctor_get_uint8(v_options_2788_, sizeof(void*)*1);
if (v_hasTrace_2789_ == 0)
{
lean_object* v___x_2790_; 
lean_dec(v_a_2768_);
lean_dec_ref(v_a_2767_);
lean_dec(v_a_2766_);
v___x_2790_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_e_2765_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v_a_2791_; 
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
lean_inc(v_a_2791_);
lean_dec_ref(v___x_2790_);
v_____do__lift_2775_ = v_a_2791_;
goto v___jp_2774_;
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
v_a_2792_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2790_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2790_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
else
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2909_; 
v___x_2800_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__2_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_));
v___x_2801_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___redArg(v___x_2800_, v_a_2771_);
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2804_ = v___x_2801_;
v_isShared_2805_ = v_isSharedCheck_2909_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2801_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2909_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___f_2806_; lean_object* v___x_2807_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v_a_2811_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v_a_2827_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v_a_2834_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v_a_2847_; uint8_t v___x_2896_; 
lean_inc_ref(v_e_2765_);
v___f_2806_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_prove___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2806_, 0, v_e_2765_);
v___x_2807_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_2896_ = lean_unbox(v_a_2802_);
if (v___x_2896_ == 0)
{
lean_object* v___x_2897_; uint8_t v___x_2898_; 
v___x_2897_ = l_Lean_trace_profiler;
v___x_2898_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_2788_, v___x_2897_);
if (v___x_2898_ == 0)
{
lean_object* v___x_2899_; 
lean_dec_ref(v___f_2806_);
lean_del_object(v___x_2804_);
lean_dec(v_a_2802_);
lean_dec(v_a_2768_);
lean_dec_ref(v_a_2767_);
lean_dec(v_a_2766_);
v___x_2899_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_e_2765_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc(v_a_2900_);
lean_dec_ref(v___x_2899_);
v_____do__lift_2775_ = v_a_2900_;
goto v___jp_2774_;
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
v_a_2901_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2899_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2899_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
else
{
lean_inc_ref(v_options_2788_);
goto v___jp_2849_;
}
}
else
{
lean_inc_ref(v_options_2788_);
goto v___jp_2849_;
}
v___jp_2808_:
{
lean_object* v___x_2812_; double v___x_2813_; double v___x_2814_; double v___x_2815_; double v___x_2816_; double v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; lean_object* v___x_2823_; 
v___x_2812_ = lean_io_mono_nanos_now();
v___x_2813_ = lean_float_of_nat(v___y_2809_);
v___x_2814_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1);
v___x_2815_ = lean_float_div(v___x_2813_, v___x_2814_);
v___x_2816_ = lean_float_of_nat(v___x_2812_);
v___x_2817_ = lean_float_div(v___x_2816_, v___x_2814_);
v___x_2818_ = lean_box_float(v___x_2815_);
v___x_2819_ = lean_box_float(v___x_2817_);
v___x_2820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2820_, 0, v___x_2818_);
lean_ctor_set(v___x_2820_, 1, v___x_2819_);
v___x_2821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2821_, 0, v_a_2811_);
lean_ctor_set(v___x_2821_, 1, v___x_2820_);
v___x_2822_ = lean_unbox(v_a_2802_);
lean_dec(v_a_2802_);
v___x_2823_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2(v___x_2800_, v_hasTrace_2789_, v___x_2807_, v_options_2788_, v___x_2822_, v___y_2810_, v___f_2806_, v___x_2821_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_);
lean_dec_ref(v_options_2788_);
return v___x_2823_;
}
v___jp_2824_:
{
lean_object* v___x_2829_; 
if (v_isShared_2805_ == 0)
{
lean_ctor_set_tag(v___x_2804_, 1);
lean_ctor_set(v___x_2804_, 0, v_a_2827_);
v___x_2829_ = v___x_2804_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2827_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
v___y_2809_ = v___y_2825_;
v___y_2810_ = v___y_2826_;
v_a_2811_ = v___x_2829_;
goto v___jp_2808_;
}
}
v___jp_2831_:
{
lean_object* v___x_2835_; double v___x_2836_; double v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; uint8_t v___x_2842_; lean_object* v___x_2843_; 
v___x_2835_ = lean_io_get_num_heartbeats();
v___x_2836_ = lean_float_of_nat(v___y_2833_);
v___x_2837_ = lean_float_of_nat(v___x_2835_);
v___x_2838_ = lean_box_float(v___x_2836_);
v___x_2839_ = lean_box_float(v___x_2837_);
v___x_2840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2838_);
lean_ctor_set(v___x_2840_, 1, v___x_2839_);
v___x_2841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2841_, 0, v_a_2834_);
lean_ctor_set(v___x_2841_, 1, v___x_2840_);
v___x_2842_ = lean_unbox(v_a_2802_);
lean_dec(v_a_2802_);
v___x_2843_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2(v___x_2800_, v_hasTrace_2789_, v___x_2807_, v_options_2788_, v___x_2842_, v___y_2832_, v___f_2806_, v___x_2841_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_);
lean_dec_ref(v_options_2788_);
return v___x_2843_;
}
v___jp_2844_:
{
lean_object* v___x_2848_; 
v___x_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2848_, 0, v_a_2847_);
v___y_2832_ = v___y_2845_;
v___y_2833_ = v___y_2846_;
v_a_2834_ = v___x_2848_;
goto v___jp_2831_;
}
v___jp_2849_:
{
lean_object* v___x_2850_; lean_object* v_a_2851_; lean_object* v___x_2852_; uint8_t v___x_2853_; 
v___x_2850_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__1___redArg(v_a_2772_);
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref(v___x_2850_);
v___x_2852_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2853_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_2788_, v___x_2852_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2854_ = lean_io_mono_nanos_now();
lean_inc(v_a_2772_);
lean_inc_ref(v_a_2771_);
lean_inc(v_a_2770_);
lean_inc_ref(v_a_2769_);
v___x_2855_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_e_2765_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref(v___x_2855_);
if (lean_obj_tag(v_a_2856_) == 0)
{
lean_object* v___x_2857_; 
v___x_2857_ = lean_box(0);
v___y_2825_ = v___x_2854_;
v___y_2826_ = v_a_2851_;
v_a_2827_ = v___x_2857_;
goto v___jp_2824_;
}
else
{
lean_object* v_val_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2866_; 
v_val_2858_ = lean_ctor_get(v_a_2856_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v_a_2856_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2860_ = v_a_2856_;
v_isShared_2861_ = v_isSharedCheck_2866_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_val_2858_);
lean_dec(v_a_2856_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2866_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2862_; lean_object* v___x_2864_; 
v___x_2862_ = l_Lean_mkFVar(v_val_2858_);
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 0, v___x_2862_);
v___x_2864_ = v___x_2860_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v___x_2862_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
v___y_2825_ = v___x_2854_;
v___y_2826_ = v_a_2851_;
v_a_2827_ = v___x_2864_;
goto v___jp_2824_;
}
}
}
}
else
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
lean_del_object(v___x_2804_);
v_a_2867_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v___x_2855_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2855_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
lean_ctor_set_tag(v___x_2869_, 0);
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_a_2867_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
v___y_2809_ = v___x_2854_;
v___y_2810_ = v_a_2851_;
v_a_2811_ = v___x_2872_;
goto v___jp_2808_;
}
}
}
}
else
{
lean_object* v___x_2875_; lean_object* v___x_2876_; 
lean_del_object(v___x_2804_);
v___x_2875_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2772_);
lean_inc_ref(v_a_2771_);
lean_inc(v_a_2770_);
lean_inc_ref(v_a_2769_);
v___x_2876_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_e_2765_, v_a_2769_, v_a_2770_, v_a_2771_, v_a_2772_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_a_2877_);
lean_dec_ref(v___x_2876_);
if (lean_obj_tag(v_a_2877_) == 0)
{
lean_object* v___x_2878_; 
v___x_2878_ = lean_box(0);
v___y_2845_ = v_a_2851_;
v___y_2846_ = v___x_2875_;
v_a_2847_ = v___x_2878_;
goto v___jp_2844_;
}
else
{
lean_object* v_val_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2887_; 
v_val_2879_ = lean_ctor_get(v_a_2877_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v_a_2877_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2881_ = v_a_2877_;
v_isShared_2882_ = v_isSharedCheck_2887_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_val_2879_);
lean_dec(v_a_2877_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2887_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2883_; lean_object* v___x_2885_; 
v___x_2883_ = l_Lean_mkFVar(v_val_2879_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 0, v___x_2883_);
v___x_2885_ = v___x_2881_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2883_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
v___y_2845_ = v_a_2851_;
v___y_2846_ = v___x_2875_;
v_a_2847_ = v___x_2885_;
goto v___jp_2844_;
}
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
v_a_2888_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2876_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2876_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
lean_ctor_set_tag(v___x_2890_, 0);
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
v___y_2832_ = v_a_2851_;
v___y_2833_ = v___x_2875_;
v_a_2834_ = v___x_2893_;
goto v___jp_2831_;
}
}
}
}
}
}
}
v___jp_2774_:
{
if (lean_obj_tag(v_____do__lift_2775_) == 0)
{
lean_object* v___x_2776_; lean_object* v___x_2777_; 
v___x_2776_ = lean_box(0);
v___x_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2777_, 0, v___x_2776_);
return v___x_2777_;
}
else
{
lean_object* v_val_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2787_; 
v_val_2778_ = lean_ctor_get(v_____do__lift_2775_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v_____do__lift_2775_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2780_ = v_____do__lift_2775_;
v_isShared_2781_ = v_isSharedCheck_2787_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_val_2778_);
lean_dec(v_____do__lift_2775_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2787_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2782_; lean_object* v___x_2784_; 
v___x_2782_ = l_Lean_mkFVar(v_val_2778_);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v___x_2782_);
v___x_2784_ = v___x_2780_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v___x_2782_);
v___x_2784_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2783_;
}
v_reusejp_2783_:
{
lean_object* v___x_2785_; 
v___x_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2784_);
return v___x_2785_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___boxed(lean_object* v_e_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l_Lean_Elab_Tactic_NormCast_prove(v_e_2910_, v_a_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__4(lean_object* v_00_u03b1_2920_, lean_object* v_x_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v___x_2930_; 
v___x_2930_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__4___redArg(v_x_2921_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__4___boxed(lean_object* v_00_u03b1_2931_, lean_object* v_x_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__4(v_00_u03b1_2931_, v_x_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
lean_dec(v___y_2939_);
lean_dec_ref(v___y_2938_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__3(lean_object* v_oldTraces_2942_, lean_object* v_data_2943_, lean_object* v_ref_2944_, lean_object* v_msg_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
lean_object* v___x_2954_; 
v___x_2954_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__3___redArg(v_oldTraces_2942_, v_data_2943_, v_ref_2944_, v_msg_2945_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__3___boxed(lean_object* v_oldTraces_2955_, lean_object* v_data_2956_, lean_object* v_ref_2957_, lean_object* v_msg_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__2_spec__3(v_oldTraces_2955_, v_data_2956_, v_ref_2957_, v_msg_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
lean_dec(v___y_2965_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0(lean_object* v_a_2968_, lean_object* v_cache_2969_, lean_object* v_a_x3f_2970_){
_start:
{
lean_object* v___x_2972_; lean_object* v_congrCache_2973_; lean_object* v_dsimpCache_2974_; lean_object* v_usedTheorems_2975_; lean_object* v_numSteps_2976_; lean_object* v_diag_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2987_; 
v___x_2972_ = lean_st_ref_take(v_a_2968_);
v_congrCache_2973_ = lean_ctor_get(v___x_2972_, 1);
v_dsimpCache_2974_ = lean_ctor_get(v___x_2972_, 2);
v_usedTheorems_2975_ = lean_ctor_get(v___x_2972_, 3);
v_numSteps_2976_ = lean_ctor_get(v___x_2972_, 4);
v_diag_2977_ = lean_ctor_get(v___x_2972_, 5);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_2987_ == 0)
{
lean_object* v_unused_2988_; 
v_unused_2988_ = lean_ctor_get(v___x_2972_, 0);
lean_dec(v_unused_2988_);
v___x_2979_ = v___x_2972_;
v_isShared_2980_ = v_isSharedCheck_2987_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_diag_2977_);
lean_inc(v_numSteps_2976_);
lean_inc(v_usedTheorems_2975_);
lean_inc(v_dsimpCache_2974_);
lean_inc(v_congrCache_2973_);
lean_dec(v___x_2972_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2987_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2982_; 
if (v_isShared_2980_ == 0)
{
lean_ctor_set(v___x_2979_, 0, v_cache_2969_);
v___x_2982_ = v___x_2979_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_cache_2969_);
lean_ctor_set(v_reuseFailAlloc_2986_, 1, v_congrCache_2973_);
lean_ctor_set(v_reuseFailAlloc_2986_, 2, v_dsimpCache_2974_);
lean_ctor_set(v_reuseFailAlloc_2986_, 3, v_usedTheorems_2975_);
lean_ctor_set(v_reuseFailAlloc_2986_, 4, v_numSteps_2976_);
lean_ctor_set(v_reuseFailAlloc_2986_, 5, v_diag_2977_);
v___x_2982_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2983_ = lean_st_ref_set(v_a_2968_, v___x_2982_);
v___x_2984_ = lean_box(0);
v___x_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2984_);
return v___x_2985_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0___boxed(lean_object* v_a_2989_, lean_object* v_cache_2990_, lean_object* v_a_x3f_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0(v_a_2989_, v_cache_2990_, v_a_x3f_2991_);
lean_dec(v_a_x3f_2991_);
lean_dec(v_a_2989_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim(lean_object* v_up_2996_, lean_object* v_e_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_, lean_object* v_a_3000_, lean_object* v_a_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_){
_start:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v_congrCache_3008_; lean_object* v_dsimpCache_3009_; lean_object* v_usedTheorems_3010_; lean_object* v_numSteps_3011_; lean_object* v_diag_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3121_; 
v___x_3006_ = lean_st_ref_get(v_a_3000_);
v___x_3007_ = lean_st_ref_take(v_a_3000_);
v_congrCache_3008_ = lean_ctor_get(v___x_3007_, 1);
v_dsimpCache_3009_ = lean_ctor_get(v___x_3007_, 2);
v_usedTheorems_3010_ = lean_ctor_get(v___x_3007_, 3);
v_numSteps_3011_ = lean_ctor_get(v___x_3007_, 4);
v_diag_3012_ = lean_ctor_get(v___x_3007_, 5);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3121_ == 0)
{
lean_object* v_unused_3122_; 
v_unused_3122_ = lean_ctor_get(v___x_3007_, 0);
lean_dec(v_unused_3122_);
v___x_3014_ = v___x_3007_;
v_isShared_3015_ = v_isSharedCheck_3121_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_diag_3012_);
lean_inc(v_numSteps_3011_);
lean_inc(v_usedTheorems_3010_);
lean_inc(v_dsimpCache_3009_);
lean_inc(v_congrCache_3008_);
lean_dec(v___x_3007_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3121_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
uint8_t v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3019_; 
v___x_3016_ = 1;
v___x_3017_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6);
if (v_isShared_3015_ == 0)
{
lean_ctor_set(v___x_3014_, 0, v___x_3017_);
v___x_3019_ = v___x_3014_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v___x_3017_);
lean_ctor_set(v_reuseFailAlloc_3120_, 1, v_congrCache_3008_);
lean_ctor_set(v_reuseFailAlloc_3120_, 2, v_dsimpCache_3009_);
lean_ctor_set(v_reuseFailAlloc_3120_, 3, v_usedTheorems_3010_);
lean_ctor_set(v_reuseFailAlloc_3120_, 4, v_numSteps_3011_);
lean_ctor_set(v_reuseFailAlloc_3120_, 5, v_diag_3012_);
v___x_3019_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
lean_object* v___x_3020_; lean_object* v_post_3021_; lean_object* v_erased_3022_; lean_object* v_cache_3023_; lean_object* v_pre_3024_; lean_object* v_post_3025_; lean_object* v_dpre_3026_; lean_object* v_dpost_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3118_; 
v___x_3020_ = lean_st_ref_set(v_a_3000_, v___x_3019_);
v_post_3021_ = lean_ctor_get(v_up_2996_, 1);
lean_inc_ref(v_post_3021_);
v_erased_3022_ = lean_ctor_get(v_up_2996_, 4);
lean_inc_ref(v_erased_3022_);
lean_dec_ref(v_up_2996_);
v_cache_3023_ = lean_ctor_get(v___x_3006_, 0);
lean_inc_ref(v_cache_3023_);
lean_dec(v___x_3006_);
v_pre_3024_ = lean_ctor_get(v_a_2998_, 0);
v_post_3025_ = lean_ctor_get(v_a_2998_, 1);
v_dpre_3026_ = lean_ctor_get(v_a_2998_, 2);
v_dpost_3027_ = lean_ctor_get(v_a_2998_, 3);
v_isSharedCheck_3118_ = !lean_is_exclusive(v_a_2998_);
if (v_isSharedCheck_3118_ == 0)
{
lean_object* v_unused_3119_; 
v_unused_3119_ = lean_ctor_get(v_a_2998_, 4);
lean_dec(v_unused_3119_);
v___x_3029_ = v_a_2998_;
v_isShared_3030_ = v_isSharedCheck_3118_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_dpost_3027_);
lean_inc(v_dpre_3026_);
lean_inc(v_post_3025_);
lean_inc(v_pre_3024_);
lean_dec(v_a_2998_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3118_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3031_; uint8_t v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3035_; 
v___x_3031_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__0));
v___x_3032_ = 0;
v___x_3033_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__1));
if (v_isShared_3030_ == 0)
{
lean_ctor_set(v___x_3029_, 4, v___x_3031_);
v___x_3035_ = v___x_3029_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_pre_3024_);
lean_ctor_set(v_reuseFailAlloc_3117_, 1, v_post_3025_);
lean_ctor_set(v_reuseFailAlloc_3117_, 2, v_dpre_3026_);
lean_ctor_set(v_reuseFailAlloc_3117_, 3, v_dpost_3027_);
lean_ctor_set(v_reuseFailAlloc_3117_, 4, v___x_3031_);
v___x_3035_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
lean_object* v_r_3036_; 
lean_ctor_set_uint8(v___x_3035_, sizeof(void*)*5, v___x_3032_);
lean_inc(v_a_3004_);
lean_inc_ref(v_a_3003_);
lean_inc(v_a_3002_);
lean_inc_ref(v_a_3001_);
lean_inc(v_a_3000_);
lean_inc_ref(v_e_2997_);
v_r_3036_ = l_Lean_Meta_Simp_rewrite_x3f(v_e_2997_, v_post_3021_, v_erased_3022_, v___x_3033_, v___x_3032_, v___x_3035_, v_a_2999_, v_a_3000_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_);
if (lean_obj_tag(v_r_3036_) == 0)
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3105_; 
v_a_3037_ = lean_ctor_get(v_r_3036_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v_r_3036_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3039_ = v_r_3036_;
v_isShared_3040_ = v_isSharedCheck_3105_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v_r_3036_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3105_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
lean_inc(v_a_3037_);
if (v_isShared_3040_ == 0)
{
lean_ctor_set_tag(v___x_3039_, 1);
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
lean_object* v___x_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3102_; 
v___x_3043_ = l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0(v_a_3000_, v_cache_3023_, v___x_3042_);
lean_dec_ref(v___x_3042_);
lean_dec(v_a_3000_);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3043_);
if (v_isSharedCheck_3102_ == 0)
{
lean_object* v_unused_3103_; 
v_unused_3103_ = lean_ctor_get(v___x_3043_, 0);
lean_dec(v_unused_3103_);
v___x_3045_ = v___x_3043_;
v_isShared_3046_ = v_isSharedCheck_3102_;
goto v_resetjp_3044_;
}
else
{
lean_dec(v___x_3043_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3102_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___y_3048_; lean_object* v_expr_3049_; 
if (lean_obj_tag(v_a_3037_) == 0)
{
lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3098_ = lean_box(0);
lean_inc_ref(v_e_2997_);
v___x_3099_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_3099_, 0, v_e_2997_);
lean_ctor_set(v___x_3099_, 1, v___x_3098_);
lean_ctor_set_uint8(v___x_3099_, sizeof(void*)*2, v___x_3016_);
lean_inc_ref(v_e_2997_);
v___y_3048_ = v___x_3099_;
v_expr_3049_ = v_e_2997_;
goto v___jp_3047_;
}
else
{
lean_object* v_val_3100_; lean_object* v_expr_3101_; 
v_val_3100_ = lean_ctor_get(v_a_3037_, 0);
lean_inc(v_val_3100_);
lean_dec_ref(v_a_3037_);
v_expr_3101_ = lean_ctor_get(v_val_3100_, 0);
lean_inc_ref(v_expr_3101_);
v___y_3048_ = v_val_3100_;
v_expr_3049_ = v_expr_3101_;
goto v___jp_3047_;
}
v___jp_3047_:
{
lean_object* v___x_3050_; 
lean_inc(v_a_3004_);
lean_inc_ref(v_a_3003_);
lean_inc(v_a_3002_);
lean_inc_ref(v_a_3001_);
v___x_3050_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure(v_expr_3049_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v___x_3052_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec_ref(v___x_3050_);
v___x_3052_ = l_Lean_Meta_Simp_Result_mkEqTrans(v___y_3048_, v_a_3051_, v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3081_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3055_ = v___x_3052_;
v_isShared_3056_ = v_isSharedCheck_3081_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_3052_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3081_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v_expr_3057_; uint8_t v___x_3058_; 
v_expr_3057_ = lean_ctor_get(v_a_3053_, 0);
v___x_3058_ = lean_expr_eqv(v_expr_3057_, v_e_2997_);
if (v___x_3058_ == 0)
{
lean_object* v___x_3060_; 
lean_dec_ref(v_e_2997_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set_tag(v___x_3045_, 1);
lean_ctor_set(v___x_3045_, 0, v_a_3053_);
v___x_3060_ = v___x_3045_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3053_);
v___x_3060_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
lean_object* v___x_3062_; 
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 0, v___x_3060_);
v___x_3062_ = v___x_3055_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3060_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
else
{
lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3078_; 
v_isSharedCheck_3078_ = !lean_is_exclusive(v_a_3053_);
if (v_isSharedCheck_3078_ == 0)
{
lean_object* v_unused_3079_; lean_object* v_unused_3080_; 
v_unused_3079_ = lean_ctor_get(v_a_3053_, 1);
lean_dec(v_unused_3079_);
v_unused_3080_ = lean_ctor_get(v_a_3053_, 0);
lean_dec(v_unused_3080_);
v___x_3066_ = v_a_3053_;
v_isShared_3067_ = v_isSharedCheck_3078_;
goto v_resetjp_3065_;
}
else
{
lean_dec(v_a_3053_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3078_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3068_; lean_object* v___x_3070_; 
v___x_3068_ = lean_box(0);
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 1, v___x_3068_);
lean_ctor_set(v___x_3066_, 0, v_e_2997_);
v___x_3070_ = v___x_3066_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_e_2997_);
lean_ctor_set(v_reuseFailAlloc_3077_, 1, v___x_3068_);
v___x_3070_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
lean_object* v___x_3072_; 
lean_ctor_set_uint8(v___x_3070_, sizeof(void*)*2, v___x_3058_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v___x_3070_);
v___x_3072_ = v___x_3045_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3070_);
v___x_3072_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
lean_object* v___x_3074_; 
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 0, v___x_3072_);
v___x_3074_ = v___x_3055_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3072_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3089_; 
lean_del_object(v___x_3045_);
lean_dec_ref(v_e_2997_);
v_a_3082_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3084_ = v___x_3052_;
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3052_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3087_; 
if (v_isShared_3085_ == 0)
{
v___x_3087_ = v___x_3084_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_a_3082_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
}
else
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3097_; 
lean_dec_ref(v___y_3048_);
lean_del_object(v___x_3045_);
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec_ref(v_e_2997_);
v_a_3090_ = lean_ctor_get(v___x_3050_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3050_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3092_ = v___x_3050_;
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_3050_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3095_; 
if (v_isShared_3093_ == 0)
{
v___x_3095_ = v___x_3092_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_a_3090_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
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
lean_object* v_a_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
lean_dec(v_a_3004_);
lean_dec_ref(v_a_3003_);
lean_dec(v_a_3002_);
lean_dec_ref(v_a_3001_);
lean_dec_ref(v_e_2997_);
v_a_3106_ = lean_ctor_get(v_r_3036_, 0);
lean_inc(v_a_3106_);
lean_dec_ref(v_r_3036_);
v___x_3107_ = lean_box(0);
v___x_3108_ = l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0(v_a_3000_, v_cache_3023_, v___x_3107_);
lean_dec(v_a_3000_);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3115_ == 0)
{
lean_object* v_unused_3116_; 
v_unused_3116_ = lean_ctor_get(v___x_3108_, 0);
lean_dec(v_unused_3116_);
v___x_3110_ = v___x_3108_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_dec(v___x_3108_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
lean_ctor_set_tag(v___x_3110_, 1);
lean_ctor_set(v___x_3110_, 0, v_a_3106_);
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3106_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___boxed(lean_object* v_up_3123_, lean_object* v_e_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_, lean_object* v_a_3128_, lean_object* v_a_3129_, lean_object* v_a_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l_Lean_Elab_Tactic_NormCast_upwardAndElim(v_up_3123_, v_e_3124_, v_a_3125_, v_a_3126_, v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_numeralToCoe(lean_object* v_e_3138_, lean_object* v_a_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_){
_start:
{
lean_object* v___x_3144_; 
v___x_3144_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_e_3138_);
if (lean_obj_tag(v___x_3144_) == 1)
{
lean_object* v_val_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3220_; 
v_val_3145_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3220_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3220_ == 0)
{
v___x_3147_ = v___x_3144_;
v_isShared_3148_ = v_isSharedCheck_3220_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_val_3145_);
lean_dec(v___x_3144_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3220_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v_fst_3149_; lean_object* v_snd_3150_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___x_3198_; 
v_fst_3149_ = lean_ctor_get(v_val_3145_, 0);
lean_inc(v_fst_3149_);
v_snd_3150_ = lean_ctor_get(v_val_3145_, 1);
lean_inc(v_snd_3150_);
lean_dec(v_val_3145_);
lean_inc(v_a_3142_);
lean_inc_ref(v_a_3141_);
lean_inc(v_a_3140_);
lean_inc_ref(v_a_3139_);
lean_inc(v_fst_3149_);
v___x_3198_ = lean_whnf(v_fst_3149_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_object* v_a_3199_; lean_object* v___x_3200_; uint8_t v___x_3201_; 
v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
lean_inc(v_a_3199_);
lean_dec_ref(v___x_3198_);
v___x_3200_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__5));
v___x_3201_ = l_Lean_Expr_isConstOf(v_a_3199_, v___x_3200_);
lean_dec(v_a_3199_);
if (v___x_3201_ == 0)
{
v___y_3152_ = v_a_3139_;
v___y_3153_ = v_a_3140_;
v___y_3154_ = v_a_3141_;
v___y_3155_ = v_a_3142_;
goto v___jp_3151_;
}
else
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3211_; 
lean_dec(v_snd_3150_);
lean_dec(v_fst_3149_);
lean_del_object(v___x_3147_);
lean_dec_ref(v_e_3138_);
v___x_3202_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_3203_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_3202_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_);
lean_dec(v_a_3142_);
lean_dec_ref(v_a_3141_);
lean_dec(v_a_3140_);
lean_dec_ref(v_a_3139_);
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3206_ = v___x_3203_;
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___x_3203_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3209_; 
if (v_isShared_3207_ == 0)
{
v___x_3209_ = v___x_3206_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_a_3204_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
}
else
{
lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3219_; 
lean_dec(v_snd_3150_);
lean_dec(v_fst_3149_);
lean_del_object(v___x_3147_);
lean_dec(v_a_3142_);
lean_dec_ref(v_a_3141_);
lean_dec(v_a_3140_);
lean_dec_ref(v_a_3139_);
lean_dec_ref(v_e_3138_);
v_a_3212_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3214_ = v___x_3198_;
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3198_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3219_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
lean_object* v___x_3217_; 
if (v_isShared_3215_ == 0)
{
v___x_3217_ = v___x_3214_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_a_3212_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
v___jp_3151_:
{
lean_object* v___x_3156_; lean_object* v___x_3158_; 
v___x_3156_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_numeralToCoe___closed__1));
if (v_isShared_3148_ == 0)
{
lean_ctor_set(v___x_3147_, 0, v_fst_3149_);
v___x_3158_ = v___x_3147_;
goto v_reusejp_3157_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_fst_3149_);
v___x_3158_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3157_;
}
v_reusejp_3157_:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3159_ = lean_box(0);
v___x_3160_ = l_Lean_mkNatLit(v_snd_3150_);
v___x_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
v___x_3162_ = lean_unsigned_to_nat(3u);
v___x_3163_ = lean_mk_empty_array_with_capacity(v___x_3162_);
v___x_3164_ = lean_array_push(v___x_3163_, v___x_3158_);
v___x_3165_ = lean_array_push(v___x_3164_, v___x_3159_);
v___x_3166_ = lean_array_push(v___x_3165_, v___x_3161_);
lean_inc(v___y_3155_);
lean_inc_ref(v___y_3154_);
lean_inc(v___y_3153_);
lean_inc_ref(v___y_3152_);
v___x_3167_ = l_Lean_Meta_mkAppOptM(v___x_3156_, v___x_3166_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
if (lean_obj_tag(v___x_3167_) == 0)
{
lean_object* v_a_3168_; lean_object* v___x_3169_; 
v_a_3168_ = lean_ctor_get(v___x_3167_, 0);
lean_inc(v_a_3168_);
lean_dec_ref(v___x_3167_);
lean_inc(v___y_3155_);
lean_inc_ref(v___y_3154_);
lean_inc(v___y_3153_);
lean_inc_ref(v___y_3152_);
v___x_3169_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_e_3138_, v_a_3168_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3180_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3172_ = v___x_3169_;
v_isShared_3173_ = v_isSharedCheck_3180_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3169_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3180_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
if (lean_obj_tag(v_a_3170_) == 1)
{
lean_object* v_val_3174_; lean_object* v___x_3176_; 
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
v_val_3174_ = lean_ctor_get(v_a_3170_, 0);
lean_inc(v_val_3174_);
lean_dec_ref(v_a_3170_);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 0, v_val_3174_);
v___x_3176_ = v___x_3172_;
goto v_reusejp_3175_;
}
else
{
lean_object* v_reuseFailAlloc_3177_; 
v_reuseFailAlloc_3177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3177_, 0, v_val_3174_);
v___x_3176_ = v_reuseFailAlloc_3177_;
goto v_reusejp_3175_;
}
v_reusejp_3175_:
{
return v___x_3176_;
}
}
else
{
lean_object* v___x_3178_; lean_object* v___x_3179_; 
lean_del_object(v___x_3172_);
lean_dec(v_a_3170_);
v___x_3178_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_3179_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_3178_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
return v___x_3179_;
}
}
}
else
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
v_a_3181_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_3169_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3169_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3196_; 
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec_ref(v_e_3138_);
v_a_3189_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3196_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3191_ = v___x_3167_;
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3167_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3196_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3194_; 
if (v_isShared_3192_ == 0)
{
v___x_3194_ = v___x_3191_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v_a_3189_);
v___x_3194_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
return v___x_3194_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
lean_dec(v___x_3144_);
lean_dec_ref(v_e_3138_);
v___x_3221_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_3222_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_3221_, v_a_3139_, v_a_3140_, v_a_3141_, v_a_3142_);
lean_dec(v_a_3142_);
lean_dec_ref(v_a_3141_);
lean_dec(v_a_3140_);
lean_dec_ref(v_a_3139_);
return v___x_3222_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_numeralToCoe___boxed(lean_object* v_e_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l_Lean_Elab_Tactic_NormCast_numeralToCoe(v_e_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(lean_object* v_e_3238_, lean_object* v_a_3239_, lean_object* v_a_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_){
_start:
{
lean_object* v___x_3244_; uint8_t v___x_3245_; uint8_t v___x_3246_; lean_object* v___x_3247_; 
v___x_3244_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_));
v___x_3245_ = 0;
v___x_3246_ = 1;
v___x_3247_ = l_Lean_Meta_evalExpr_x27___redArg(v___x_3244_, v_e_3238_, v___x_3245_, v___x_3246_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_);
return v___x_3247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3____boxed(lean_object* v_e_3248_, lean_object* v_a_3249_, lean_object* v_a_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_){
_start:
{
lean_object* v_res_3254_; 
v_res_3254_ = l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(v_e_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_);
return v_res_3254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(lean_object* v_e_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_){
_start:
{
lean_object* v___x_3263_; 
v___x_3263_ = l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(v_e_3255_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3____boxed(lean_object* v_e_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l_Lean_Elab_Tactic_NormCast_evalUnsafe_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(v_e_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_);
lean_dec(v_a_3266_);
lean_dec_ref(v_a_3265_);
return v_res_3272_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__0(void){
_start:
{
lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3273_ = lean_box(1);
v___x_3274_ = l_Lean_MessageData_ofFormat(v___x_3273_);
return v___x_3274_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__3(void){
_start:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; 
v___x_3278_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__2));
v___x_3279_ = l_Lean_MessageData_ofFormat(v___x_3278_);
return v___x_3279_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9(lean_object* v_x_3280_, lean_object* v_x_3281_){
_start:
{
if (lean_obj_tag(v_x_3281_) == 0)
{
return v_x_3280_;
}
else
{
lean_object* v_head_3282_; lean_object* v_tail_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3305_; 
v_head_3282_ = lean_ctor_get(v_x_3281_, 0);
v_tail_3283_ = lean_ctor_get(v_x_3281_, 1);
v_isSharedCheck_3305_ = !lean_is_exclusive(v_x_3281_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3285_ = v_x_3281_;
v_isShared_3286_ = v_isSharedCheck_3305_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_tail_3283_);
lean_inc(v_head_3282_);
lean_dec(v_x_3281_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3305_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v_before_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3303_; 
v_before_3287_ = lean_ctor_get(v_head_3282_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v_head_3282_);
if (v_isSharedCheck_3303_ == 0)
{
lean_object* v_unused_3304_; 
v_unused_3304_ = lean_ctor_get(v_head_3282_, 1);
lean_dec(v_unused_3304_);
v___x_3289_ = v_head_3282_;
v_isShared_3290_ = v_isSharedCheck_3303_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_before_3287_);
lean_dec(v_head_3282_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3303_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3291_; lean_object* v___x_3293_; 
v___x_3291_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__0);
if (v_isShared_3290_ == 0)
{
lean_ctor_set_tag(v___x_3289_, 7);
lean_ctor_set(v___x_3289_, 1, v___x_3291_);
lean_ctor_set(v___x_3289_, 0, v_x_3280_);
v___x_3293_ = v___x_3289_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_x_3280_);
lean_ctor_set(v_reuseFailAlloc_3302_, 1, v___x_3291_);
v___x_3293_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
lean_object* v___x_3294_; lean_object* v___x_3296_; 
v___x_3294_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__3);
if (v_isShared_3286_ == 0)
{
lean_ctor_set_tag(v___x_3285_, 7);
lean_ctor_set(v___x_3285_, 1, v___x_3294_);
lean_ctor_set(v___x_3285_, 0, v___x_3293_);
v___x_3296_ = v___x_3285_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3293_);
lean_ctor_set(v_reuseFailAlloc_3301_, 1, v___x_3294_);
v___x_3296_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3297_ = l_Lean_MessageData_ofSyntax(v_before_3287_);
v___x_3298_ = l_Lean_indentD(v___x_3297_);
v___x_3299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3296_);
lean_ctor_set(v___x_3299_, 1, v___x_3298_);
v_x_3280_ = v___x_3299_;
v_x_3281_ = v_tail_3283_;
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
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__1));
v___x_3310_ = l_Lean_MessageData_ofFormat(v___x_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg(lean_object* v_msgData_3311_, lean_object* v_macroStack_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v_options_3315_; lean_object* v___x_3316_; uint8_t v___x_3317_; 
v_options_3315_ = lean_ctor_get(v___y_3313_, 2);
v___x_3316_ = l_Lean_Elab_pp_macroStack;
v___x_3317_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_3315_, v___x_3316_);
if (v___x_3317_ == 0)
{
lean_object* v___x_3318_; 
lean_dec(v_macroStack_3312_);
v___x_3318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3318_, 0, v_msgData_3311_);
return v___x_3318_;
}
else
{
if (lean_obj_tag(v_macroStack_3312_) == 0)
{
lean_object* v___x_3319_; 
v___x_3319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3319_, 0, v_msgData_3311_);
return v___x_3319_;
}
else
{
lean_object* v_head_3320_; lean_object* v_after_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3336_; 
v_head_3320_ = lean_ctor_get(v_macroStack_3312_, 0);
lean_inc(v_head_3320_);
v_after_3321_ = lean_ctor_get(v_head_3320_, 1);
v_isSharedCheck_3336_ = !lean_is_exclusive(v_head_3320_);
if (v_isSharedCheck_3336_ == 0)
{
lean_object* v_unused_3337_; 
v_unused_3337_ = lean_ctor_get(v_head_3320_, 0);
lean_dec(v_unused_3337_);
v___x_3323_ = v_head_3320_;
v_isShared_3324_ = v_isSharedCheck_3336_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_after_3321_);
lean_dec(v_head_3320_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3336_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3325_; lean_object* v___x_3327_; 
v___x_3325_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9___closed__0);
if (v_isShared_3324_ == 0)
{
lean_ctor_set_tag(v___x_3323_, 7);
lean_ctor_set(v___x_3323_, 1, v___x_3325_);
lean_ctor_set(v___x_3323_, 0, v_msgData_3311_);
v___x_3327_ = v___x_3323_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_msgData_3311_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v___x_3325_);
v___x_3327_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v_msgData_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; 
v___x_3328_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__2);
v___x_3329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3327_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
v___x_3330_ = l_Lean_MessageData_ofSyntax(v_after_3321_);
v___x_3331_ = l_Lean_indentD(v___x_3330_);
v_msgData_3332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_3332_, 0, v___x_3329_);
lean_ctor_set(v_msgData_3332_, 1, v___x_3331_);
v___x_3333_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__9(v_msgData_3332_, v_macroStack_3312_);
v___x_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3333_);
return v___x_3334_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___boxed(lean_object* v_msgData_3338_, lean_object* v_macroStack_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg(v_msgData_3338_, v_macroStack_3339_, v___y_3340_);
lean_dec_ref(v___y_3340_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg(lean_object* v_msg_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
lean_object* v_ref_3351_; lean_object* v___x_3352_; lean_object* v_a_3353_; lean_object* v_macroStack_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3365_; 
v_ref_3351_ = lean_ctor_get(v___y_3348_, 5);
v___x_3352_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__6(v_msg_3343_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc(v_a_3353_);
lean_dec_ref(v___x_3352_);
v_macroStack_3354_ = lean_ctor_get(v___y_3344_, 1);
lean_inc(v_macroStack_3354_);
lean_dec_ref(v___y_3344_);
lean_inc(v_macroStack_3354_);
v___x_3355_ = l_Lean_Elab_getBetterRef(v_ref_3351_, v_macroStack_3354_);
v___x_3356_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg(v_a_3353_, v_macroStack_3354_, v___y_3348_);
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3359_ = v___x_3356_;
v_isShared_3360_ = v_isSharedCheck_3365_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3356_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3365_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3361_; lean_object* v___x_3363_; 
v___x_3361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3361_, 0, v___x_3355_);
lean_ctor_set(v___x_3361_, 1, v_a_3357_);
if (v_isShared_3360_ == 0)
{
lean_ctor_set_tag(v___x_3359_, 1);
lean_ctor_set(v___x_3359_, 0, v___x_3361_);
v___x_3363_ = v___x_3359_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3361_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg___boxed(lean_object* v_msg_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_){
_start:
{
lean_object* v_res_3374_; 
v_res_3374_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg(v_msg_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec(v___y_3368_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__3___redArg(lean_object* v_cls_3377_, lean_object* v_msg_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_){
_start:
{
lean_object* v_ref_3384_; lean_object* v___x_3385_; lean_object* v_a_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3430_; 
v_ref_3384_ = lean_ctor_get(v___y_3381_, 5);
v___x_3385_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3_spec__4_spec__6(v_msg_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_);
v_a_3386_ = lean_ctor_get(v___x_3385_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3388_ = v___x_3385_;
v_isShared_3389_ = v_isSharedCheck_3430_;
goto v_resetjp_3387_;
}
else
{
lean_inc(v_a_3386_);
lean_dec(v___x_3385_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3430_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3390_; lean_object* v_traceState_3391_; lean_object* v_env_3392_; lean_object* v_nextMacroScope_3393_; lean_object* v_ngen_3394_; lean_object* v_auxDeclNGen_3395_; lean_object* v_cache_3396_; lean_object* v_messages_3397_; lean_object* v_infoState_3398_; lean_object* v_snapshotTasks_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3429_; 
v___x_3390_ = lean_st_ref_take(v___y_3382_);
v_traceState_3391_ = lean_ctor_get(v___x_3390_, 4);
v_env_3392_ = lean_ctor_get(v___x_3390_, 0);
v_nextMacroScope_3393_ = lean_ctor_get(v___x_3390_, 1);
v_ngen_3394_ = lean_ctor_get(v___x_3390_, 2);
v_auxDeclNGen_3395_ = lean_ctor_get(v___x_3390_, 3);
v_cache_3396_ = lean_ctor_get(v___x_3390_, 5);
v_messages_3397_ = lean_ctor_get(v___x_3390_, 6);
v_infoState_3398_ = lean_ctor_get(v___x_3390_, 7);
v_snapshotTasks_3399_ = lean_ctor_get(v___x_3390_, 8);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3401_ = v___x_3390_;
v_isShared_3402_ = v_isSharedCheck_3429_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_snapshotTasks_3399_);
lean_inc(v_infoState_3398_);
lean_inc(v_messages_3397_);
lean_inc(v_cache_3396_);
lean_inc(v_traceState_3391_);
lean_inc(v_auxDeclNGen_3395_);
lean_inc(v_ngen_3394_);
lean_inc(v_nextMacroScope_3393_);
lean_inc(v_env_3392_);
lean_dec(v___x_3390_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3429_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
uint64_t v_tid_3403_; lean_object* v_traces_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3428_; 
v_tid_3403_ = lean_ctor_get_uint64(v_traceState_3391_, sizeof(void*)*1);
v_traces_3404_ = lean_ctor_get(v_traceState_3391_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v_traceState_3391_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3406_ = v_traceState_3391_;
v_isShared_3407_ = v_isSharedCheck_3428_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_traces_3404_);
lean_dec(v_traceState_3391_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3428_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3408_; double v___x_3409_; uint8_t v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3418_; 
v___x_3408_ = lean_box(0);
v___x_3409_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__2);
v___x_3410_ = 0;
v___x_3411_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_3412_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3412_, 0, v_cls_3377_);
lean_ctor_set(v___x_3412_, 1, v___x_3408_);
lean_ctor_set(v___x_3412_, 2, v___x_3411_);
lean_ctor_set_float(v___x_3412_, sizeof(void*)*3, v___x_3409_);
lean_ctor_set_float(v___x_3412_, sizeof(void*)*3 + 8, v___x_3409_);
lean_ctor_set_uint8(v___x_3412_, sizeof(void*)*3 + 16, v___x_3410_);
v___x_3413_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__3___redArg___closed__0));
v___x_3414_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3412_);
lean_ctor_set(v___x_3414_, 1, v_a_3386_);
lean_ctor_set(v___x_3414_, 2, v___x_3413_);
lean_inc(v_ref_3384_);
v___x_3415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3415_, 0, v_ref_3384_);
lean_ctor_set(v___x_3415_, 1, v___x_3414_);
v___x_3416_ = l_Lean_PersistentArray_push___redArg(v_traces_3404_, v___x_3415_);
if (v_isShared_3407_ == 0)
{
lean_ctor_set(v___x_3406_, 0, v___x_3416_);
v___x_3418_ = v___x_3406_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v___x_3416_);
lean_ctor_set_uint64(v_reuseFailAlloc_3427_, sizeof(void*)*1, v_tid_3403_);
v___x_3418_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
lean_object* v___x_3420_; 
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 4, v___x_3418_);
v___x_3420_ = v___x_3401_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_env_3392_);
lean_ctor_set(v_reuseFailAlloc_3426_, 1, v_nextMacroScope_3393_);
lean_ctor_set(v_reuseFailAlloc_3426_, 2, v_ngen_3394_);
lean_ctor_set(v_reuseFailAlloc_3426_, 3, v_auxDeclNGen_3395_);
lean_ctor_set(v_reuseFailAlloc_3426_, 4, v___x_3418_);
lean_ctor_set(v_reuseFailAlloc_3426_, 5, v_cache_3396_);
lean_ctor_set(v_reuseFailAlloc_3426_, 6, v_messages_3397_);
lean_ctor_set(v_reuseFailAlloc_3426_, 7, v_infoState_3398_);
lean_ctor_set(v_reuseFailAlloc_3426_, 8, v_snapshotTasks_3399_);
v___x_3420_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
lean_object* v___x_3421_; lean_object* v___x_3422_; lean_object* v___x_3424_; 
v___x_3421_ = lean_st_ref_set(v___y_3382_, v___x_3420_);
v___x_3422_ = lean_box(0);
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 0, v___x_3422_);
v___x_3424_ = v___x_3388_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v___x_3422_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_cls_3431_, lean_object* v_msg_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__3___redArg(v_cls_3431_, v_msg_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
return v_res_3438_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(lean_object* v_keys_3439_, lean_object* v_i_3440_, lean_object* v_k_3441_){
_start:
{
lean_object* v___x_3442_; uint8_t v___x_3443_; 
v___x_3442_ = lean_array_get_size(v_keys_3439_);
v___x_3443_ = lean_nat_dec_lt(v_i_3440_, v___x_3442_);
if (v___x_3443_ == 0)
{
lean_dec(v_i_3440_);
return v___x_3443_;
}
else
{
lean_object* v_k_x27_3444_; uint8_t v___x_3445_; 
v_k_x27_3444_ = lean_array_fget_borrowed(v_keys_3439_, v_i_3440_);
v___x_3445_ = l_Lean_instBEqExtraModUse_beq(v_k_3441_, v_k_x27_3444_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3446_ = lean_unsigned_to_nat(1u);
v___x_3447_ = lean_nat_add(v_i_3440_, v___x_3446_);
lean_dec(v_i_3440_);
v_i_3440_ = v___x_3447_;
goto _start;
}
else
{
lean_dec(v_i_3440_);
return v___x_3445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg___boxed(lean_object* v_keys_3449_, lean_object* v_i_3450_, lean_object* v_k_3451_){
_start:
{
uint8_t v_res_3452_; lean_object* v_r_3453_; 
v_res_3452_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_keys_3449_, v_i_3450_, v_k_3451_);
lean_dec_ref(v_k_3451_);
lean_dec_ref(v_keys_3449_);
v_r_3453_ = lean_box(v_res_3452_);
return v_r_3453_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_3454_; size_t v___x_3455_; size_t v___x_3456_; 
v___x_3454_ = ((size_t)5ULL);
v___x_3455_ = ((size_t)1ULL);
v___x_3456_ = lean_usize_shift_left(v___x_3455_, v___x_3454_);
return v___x_3456_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_3457_; size_t v___x_3458_; size_t v___x_3459_; 
v___x_3457_ = ((size_t)1ULL);
v___x_3458_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_3459_ = lean_usize_sub(v___x_3458_, v___x_3457_);
return v___x_3459_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_3460_, size_t v_x_3461_, lean_object* v_x_3462_){
_start:
{
if (lean_obj_tag(v_x_3460_) == 0)
{
lean_object* v_es_3463_; lean_object* v___x_3464_; size_t v___x_3465_; size_t v___x_3466_; size_t v___x_3467_; lean_object* v_j_3468_; lean_object* v___x_3469_; 
v_es_3463_ = lean_ctor_get(v_x_3460_, 0);
lean_inc_ref(v_es_3463_);
lean_dec_ref(v_x_3460_);
v___x_3464_ = lean_box(2);
v___x_3465_ = ((size_t)5ULL);
v___x_3466_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_3467_ = lean_usize_land(v_x_3461_, v___x_3466_);
v_j_3468_ = lean_usize_to_nat(v___x_3467_);
v___x_3469_ = lean_array_get(v___x_3464_, v_es_3463_, v_j_3468_);
lean_dec(v_j_3468_);
lean_dec_ref(v_es_3463_);
switch(lean_obj_tag(v___x_3469_))
{
case 0:
{
lean_object* v_key_3470_; uint8_t v___x_3471_; 
v_key_3470_ = lean_ctor_get(v___x_3469_, 0);
lean_inc(v_key_3470_);
lean_dec_ref(v___x_3469_);
v___x_3471_ = l_Lean_instBEqExtraModUse_beq(v_x_3462_, v_key_3470_);
lean_dec(v_key_3470_);
return v___x_3471_;
}
case 1:
{
lean_object* v_node_3472_; size_t v___x_3473_; 
v_node_3472_ = lean_ctor_get(v___x_3469_, 0);
lean_inc(v_node_3472_);
lean_dec_ref(v___x_3469_);
v___x_3473_ = lean_usize_shift_right(v_x_3461_, v___x_3465_);
v_x_3460_ = v_node_3472_;
v_x_3461_ = v___x_3473_;
goto _start;
}
default: 
{
uint8_t v___x_3475_; 
v___x_3475_ = 0;
return v___x_3475_;
}
}
}
else
{
lean_object* v_ks_3476_; lean_object* v___x_3477_; uint8_t v___x_3478_; 
v_ks_3476_ = lean_ctor_get(v_x_3460_, 0);
lean_inc_ref(v_ks_3476_);
lean_dec_ref(v_x_3460_);
v___x_3477_ = lean_unsigned_to_nat(0u);
v___x_3478_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_ks_3476_, v___x_3477_, v_x_3462_);
lean_dec_ref(v_ks_3476_);
return v___x_3478_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_3479_, lean_object* v_x_3480_, lean_object* v_x_3481_){
_start:
{
size_t v_x_12041__boxed_3482_; uint8_t v_res_3483_; lean_object* v_r_3484_; 
v_x_12041__boxed_3482_ = lean_unbox_usize(v_x_3480_);
lean_dec(v_x_3480_);
v_res_3483_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg(v_x_3479_, v_x_12041__boxed_3482_, v_x_3481_);
lean_dec_ref(v_x_3481_);
v_r_3484_ = lean_box(v_res_3483_);
return v_r_3484_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3485_, lean_object* v_x_3486_){
_start:
{
uint64_t v___x_3487_; size_t v___x_3488_; uint8_t v___x_3489_; 
v___x_3487_ = l_Lean_instHashableExtraModUse_hash(v_x_3486_);
v___x_3488_ = lean_uint64_to_usize(v___x_3487_);
v___x_3489_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg(v_x_3485_, v___x_3488_, v_x_3486_);
return v___x_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3490_, lean_object* v_x_3491_){
_start:
{
uint8_t v_res_3492_; lean_object* v_r_3493_; 
v_res_3492_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___redArg(v_x_3490_, v_x_3491_);
lean_dec_ref(v_x_3491_);
v_r_3493_ = lean_box(v_res_3492_);
return v_r_3493_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg(lean_object* v_cls_3494_, lean_object* v___y_3495_){
_start:
{
lean_object* v_options_3497_; uint8_t v_hasTrace_3498_; 
v_options_3497_ = lean_ctor_get(v___y_3495_, 2);
v_hasTrace_3498_ = lean_ctor_get_uint8(v_options_3497_, sizeof(void*)*1);
if (v_hasTrace_3498_ == 0)
{
lean_object* v___x_3499_; lean_object* v___x_3500_; 
lean_dec(v_cls_3494_);
v___x_3499_ = lean_box(v_hasTrace_3498_);
v___x_3500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3499_);
return v___x_3500_;
}
else
{
lean_object* v_inheritedTraceOptions_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; uint8_t v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v_inheritedTraceOptions_3501_ = lean_ctor_get(v___y_3495_, 13);
v___x_3502_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__1));
v___x_3503_ = l_Lean_Name_append(v___x_3502_, v_cls_3494_);
v___x_3504_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3501_, v_options_3497_, v___x_3503_);
lean_dec(v___x_3503_);
v___x_3505_ = lean_box(v___x_3504_);
v___x_3506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3505_);
return v___x_3506_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_cls_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg(v_cls_3507_, v___y_3508_);
lean_dec_ref(v___y_3508_);
return v_res_3510_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3513_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__1));
v___x_3514_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__0));
v___x_3515_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_3514_, v___x_3513_);
return v___x_3515_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3516_; 
v___x_3516_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3516_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__3);
v___x_3518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
return v___x_3518_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3519_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4);
v___x_3520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3520_, 0, v___x_3519_);
lean_ctor_set(v___x_3520_, 1, v___x_3519_);
return v___x_3520_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3521_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4);
v___x_3522_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3521_);
lean_ctor_set(v___x_3522_, 1, v___x_3521_);
lean_ctor_set(v___x_3522_, 2, v___x_3521_);
lean_ctor_set(v___x_3522_, 3, v___x_3521_);
lean_ctor_set(v___x_3522_, 4, v___x_3521_);
lean_ctor_set(v___x_3522_, 5, v___x_3521_);
return v___x_3522_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v___x_3527_; lean_object* v___x_3528_; 
v___x_3527_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__9));
v___x_3528_ = l_Lean_stringToMessageData(v___x_3527_);
return v___x_3528_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3530_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__11));
v___x_3531_ = l_Lean_stringToMessageData(v___x_3530_);
return v___x_3531_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__13(void){
_start:
{
lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3532_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_3533_ = l_Lean_stringToMessageData(v___x_3532_);
return v___x_3533_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__15(void){
_start:
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3535_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__14));
v___x_3536_ = l_Lean_stringToMessageData(v___x_3535_);
return v___x_3536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0(lean_object* v_mod_3541_, uint8_t v_isMeta_3542_, lean_object* v_hint_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v___x_3551_; lean_object* v_env_3552_; uint8_t v_isExporting_3553_; lean_object* v___x_3554_; lean_object* v_env_3555_; lean_object* v___x_3556_; lean_object* v_entry_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___y_3562_; lean_object* v___y_3563_; lean_object* v___x_3603_; uint8_t v___x_3604_; 
v___x_3551_ = lean_st_ref_get(v___y_3549_);
v_env_3552_ = lean_ctor_get(v___x_3551_, 0);
lean_inc_ref(v_env_3552_);
lean_dec(v___x_3551_);
v_isExporting_3553_ = lean_ctor_get_uint8(v_env_3552_, sizeof(void*)*8);
lean_dec_ref(v_env_3552_);
v___x_3554_ = lean_st_ref_get(v___y_3549_);
v_env_3555_ = lean_ctor_get(v___x_3554_, 0);
lean_inc_ref(v_env_3555_);
lean_dec(v___x_3554_);
v___x_3556_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__2);
lean_inc(v_mod_3541_);
v_entry_3557_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3557_, 0, v_mod_3541_);
lean_ctor_set_uint8(v_entry_3557_, sizeof(void*)*1, v_isExporting_3553_);
lean_ctor_set_uint8(v_entry_3557_, sizeof(void*)*1 + 1, v_isMeta_3542_);
v___x_3558_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3559_ = lean_box(1);
v___x_3560_ = lean_box(0);
v___x_3603_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3556_, v___x_3558_, v_env_3555_, v___x_3559_, v___x_3560_);
v___x_3604_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___redArg(v___x_3603_, v_entry_3557_);
if (v___x_3604_ == 0)
{
lean_object* v_cls_3605_; lean_object* v___x_3606_; lean_object* v_a_3607_; lean_object* v___y_3609_; lean_object* v___y_3610_; lean_object* v___y_3614_; lean_object* v___y_3615_; uint8_t v___x_3627_; 
v_cls_3605_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__8));
v___x_3606_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg(v_cls_3605_, v___y_3548_);
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
lean_inc(v_a_3607_);
lean_dec_ref(v___x_3606_);
v___x_3627_ = lean_unbox(v_a_3607_);
lean_dec(v_a_3607_);
if (v___x_3627_ == 0)
{
lean_dec(v_hint_3543_);
lean_dec(v_mod_3541_);
v___y_3562_ = v___y_3547_;
v___y_3563_ = v___y_3549_;
goto v___jp_3561_;
}
else
{
lean_object* v___x_3628_; lean_object* v___y_3630_; 
v___x_3628_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__15);
if (v_isExporting_3553_ == 0)
{
lean_object* v___x_3637_; 
v___x_3637_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__18));
v___y_3630_ = v___x_3637_;
goto v___jp_3629_;
}
else
{
lean_object* v___x_3638_; 
v___x_3638_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__19));
v___y_3630_ = v___x_3638_;
goto v___jp_3629_;
}
v___jp_3629_:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; 
v___x_3631_ = l_Lean_stringToMessageData(v___y_3630_);
v___x_3632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3628_);
lean_ctor_set(v___x_3632_, 1, v___x_3631_);
v___x_3633_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1);
v___x_3634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3632_);
lean_ctor_set(v___x_3634_, 1, v___x_3633_);
if (v_isMeta_3542_ == 0)
{
lean_object* v___x_3635_; 
v___x_3635_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__16));
v___y_3614_ = v___x_3634_;
v___y_3615_ = v___x_3635_;
goto v___jp_3613_;
}
else
{
lean_object* v___x_3636_; 
v___x_3636_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__17));
v___y_3614_ = v___x_3634_;
v___y_3615_ = v___x_3636_;
goto v___jp_3613_;
}
}
}
v___jp_3608_:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3611_, 0, v___y_3609_);
lean_ctor_set(v___x_3611_, 1, v___y_3610_);
v___x_3612_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__3___redArg(v_cls_3605_, v___x_3611_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_dec_ref(v___x_3612_);
v___y_3562_ = v___y_3547_;
v___y_3563_ = v___y_3549_;
goto v___jp_3561_;
}
else
{
lean_dec_ref(v_entry_3557_);
return v___x_3612_;
}
}
v___jp_3613_:
{
lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; uint8_t v___x_3622_; 
v___x_3616_ = l_Lean_stringToMessageData(v___y_3615_);
v___x_3617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___y_3614_);
lean_ctor_set(v___x_3617_, 1, v___x_3616_);
v___x_3618_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__10);
v___x_3619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3617_);
lean_ctor_set(v___x_3619_, 1, v___x_3618_);
v___x_3620_ = l_Lean_MessageData_ofName(v_mod_3541_);
v___x_3621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3619_);
lean_ctor_set(v___x_3621_, 1, v___x_3620_);
v___x_3622_ = l_Lean_Name_isAnonymous(v_hint_3543_);
if (v___x_3622_ == 0)
{
lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; 
v___x_3623_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__12);
v___x_3624_ = l_Lean_MessageData_ofName(v_hint_3543_);
v___x_3625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3623_);
lean_ctor_set(v___x_3625_, 1, v___x_3624_);
v___y_3609_ = v___x_3621_;
v___y_3610_ = v___x_3625_;
goto v___jp_3608_;
}
else
{
lean_object* v___x_3626_; 
lean_dec(v_hint_3543_);
v___x_3626_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__13);
v___y_3609_ = v___x_3621_;
v___y_3610_ = v___x_3626_;
goto v___jp_3608_;
}
}
}
else
{
lean_object* v___x_3639_; lean_object* v___x_3640_; 
lean_dec_ref(v_entry_3557_);
lean_dec(v_hint_3543_);
lean_dec(v_mod_3541_);
v___x_3639_ = lean_box(0);
v___x_3640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3640_, 0, v___x_3639_);
return v___x_3640_;
}
v___jp_3561_:
{
lean_object* v___x_3564_; lean_object* v_toEnvExtension_3565_; lean_object* v_env_3566_; lean_object* v_nextMacroScope_3567_; lean_object* v_ngen_3568_; lean_object* v_auxDeclNGen_3569_; lean_object* v_traceState_3570_; lean_object* v_messages_3571_; lean_object* v_infoState_3572_; lean_object* v_snapshotTasks_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3601_; 
v___x_3564_ = lean_st_ref_take(v___y_3563_);
v_toEnvExtension_3565_ = lean_ctor_get(v___x_3558_, 0);
lean_inc_ref(v_toEnvExtension_3565_);
v_env_3566_ = lean_ctor_get(v___x_3564_, 0);
v_nextMacroScope_3567_ = lean_ctor_get(v___x_3564_, 1);
v_ngen_3568_ = lean_ctor_get(v___x_3564_, 2);
v_auxDeclNGen_3569_ = lean_ctor_get(v___x_3564_, 3);
v_traceState_3570_ = lean_ctor_get(v___x_3564_, 4);
v_messages_3571_ = lean_ctor_get(v___x_3564_, 6);
v_infoState_3572_ = lean_ctor_get(v___x_3564_, 7);
v_snapshotTasks_3573_ = lean_ctor_get(v___x_3564_, 8);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3564_);
if (v_isSharedCheck_3601_ == 0)
{
lean_object* v_unused_3602_; 
v_unused_3602_ = lean_ctor_get(v___x_3564_, 5);
lean_dec(v_unused_3602_);
v___x_3575_ = v___x_3564_;
v_isShared_3576_ = v_isSharedCheck_3601_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_snapshotTasks_3573_);
lean_inc(v_infoState_3572_);
lean_inc(v_messages_3571_);
lean_inc(v_traceState_3570_);
lean_inc(v_auxDeclNGen_3569_);
lean_inc(v_ngen_3568_);
lean_inc(v_nextMacroScope_3567_);
lean_inc(v_env_3566_);
lean_dec(v___x_3564_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3601_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v_asyncMode_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3581_; 
v_asyncMode_3577_ = lean_ctor_get(v_toEnvExtension_3565_, 2);
lean_inc(v_asyncMode_3577_);
lean_dec_ref(v_toEnvExtension_3565_);
v___x_3578_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3558_, v_env_3566_, v_entry_3557_, v_asyncMode_3577_, v___x_3560_);
lean_dec(v_asyncMode_3577_);
v___x_3579_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__5);
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 5, v___x_3579_);
lean_ctor_set(v___x_3575_, 0, v___x_3578_);
v___x_3581_ = v___x_3575_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3578_);
lean_ctor_set(v_reuseFailAlloc_3600_, 1, v_nextMacroScope_3567_);
lean_ctor_set(v_reuseFailAlloc_3600_, 2, v_ngen_3568_);
lean_ctor_set(v_reuseFailAlloc_3600_, 3, v_auxDeclNGen_3569_);
lean_ctor_set(v_reuseFailAlloc_3600_, 4, v_traceState_3570_);
lean_ctor_set(v_reuseFailAlloc_3600_, 5, v___x_3579_);
lean_ctor_set(v_reuseFailAlloc_3600_, 6, v_messages_3571_);
lean_ctor_set(v_reuseFailAlloc_3600_, 7, v_infoState_3572_);
lean_ctor_set(v_reuseFailAlloc_3600_, 8, v_snapshotTasks_3573_);
v___x_3581_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v_mctx_3584_; lean_object* v_zetaDeltaFVarIds_3585_; lean_object* v_postponed_3586_; lean_object* v_diag_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3598_; 
v___x_3582_ = lean_st_ref_set(v___y_3563_, v___x_3581_);
v___x_3583_ = lean_st_ref_take(v___y_3562_);
v_mctx_3584_ = lean_ctor_get(v___x_3583_, 0);
v_zetaDeltaFVarIds_3585_ = lean_ctor_get(v___x_3583_, 2);
v_postponed_3586_ = lean_ctor_get(v___x_3583_, 3);
v_diag_3587_ = lean_ctor_get(v___x_3583_, 4);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3598_ == 0)
{
lean_object* v_unused_3599_; 
v_unused_3599_ = lean_ctor_get(v___x_3583_, 1);
lean_dec(v_unused_3599_);
v___x_3589_ = v___x_3583_;
v_isShared_3590_ = v_isSharedCheck_3598_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_diag_3587_);
lean_inc(v_postponed_3586_);
lean_inc(v_zetaDeltaFVarIds_3585_);
lean_inc(v_mctx_3584_);
lean_dec(v___x_3583_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3598_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3591_; lean_object* v___x_3593_; 
v___x_3591_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__6);
if (v_isShared_3590_ == 0)
{
lean_ctor_set(v___x_3589_, 1, v___x_3591_);
v___x_3593_ = v___x_3589_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_mctx_3584_);
lean_ctor_set(v_reuseFailAlloc_3597_, 1, v___x_3591_);
lean_ctor_set(v_reuseFailAlloc_3597_, 2, v_zetaDeltaFVarIds_3585_);
lean_ctor_set(v_reuseFailAlloc_3597_, 3, v_postponed_3586_);
lean_ctor_set(v_reuseFailAlloc_3597_, 4, v_diag_3587_);
v___x_3593_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3594_ = lean_st_ref_set(v___y_3562_, v___x_3593_);
v___x_3595_ = lean_box(0);
v___x_3596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3596_, 0, v___x_3595_);
return v___x_3596_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___boxed(lean_object* v_mod_3641_, lean_object* v_isMeta_3642_, lean_object* v_hint_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
uint8_t v_isMeta_boxed_3651_; lean_object* v_res_3652_; 
v_isMeta_boxed_3651_ = lean_unbox(v_isMeta_3642_);
v_res_3652_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0(v_mod_3641_, v_isMeta_boxed_3651_, v_hint_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_);
lean_dec(v___y_3649_);
lean_dec_ref(v___y_3648_);
lean_dec(v___y_3647_);
lean_dec_ref(v___y_3646_);
lean_dec(v___y_3645_);
lean_dec_ref(v___y_3644_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__1(lean_object* v___x_3653_, lean_object* v_declName_3654_, lean_object* v_as_3655_, size_t v_sz_3656_, size_t v_i_3657_, lean_object* v_b_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_){
_start:
{
uint8_t v___x_3666_; 
v___x_3666_ = lean_usize_dec_lt(v_i_3657_, v_sz_3656_);
if (v___x_3666_ == 0)
{
lean_object* v___x_3667_; 
lean_dec(v_declName_3654_);
v___x_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3667_, 0, v_b_3658_);
return v___x_3667_;
}
else
{
lean_object* v___x_3668_; lean_object* v_modules_3669_; lean_object* v___x_3670_; lean_object* v_a_3671_; lean_object* v___x_3672_; lean_object* v_toImport_3673_; lean_object* v_module_3674_; uint8_t v___x_3675_; lean_object* v___x_3676_; 
v___x_3668_ = l_Lean_Environment_header(v___x_3653_);
v_modules_3669_ = lean_ctor_get(v___x_3668_, 3);
lean_inc_ref(v_modules_3669_);
lean_dec_ref(v___x_3668_);
v___x_3670_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3671_ = lean_array_uget_borrowed(v_as_3655_, v_i_3657_);
v___x_3672_ = lean_array_get(v___x_3670_, v_modules_3669_, v_a_3671_);
lean_dec_ref(v_modules_3669_);
v_toImport_3673_ = lean_ctor_get(v___x_3672_, 0);
lean_inc_ref(v_toImport_3673_);
lean_dec(v___x_3672_);
v_module_3674_ = lean_ctor_get(v_toImport_3673_, 0);
lean_inc(v_module_3674_);
lean_dec_ref(v_toImport_3673_);
v___x_3675_ = 0;
lean_inc(v_declName_3654_);
v___x_3676_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0(v_module_3674_, v___x_3675_, v_declName_3654_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v___x_3677_; size_t v___x_3678_; size_t v___x_3679_; 
lean_dec_ref(v___x_3676_);
v___x_3677_ = lean_box(0);
v___x_3678_ = ((size_t)1ULL);
v___x_3679_ = lean_usize_add(v_i_3657_, v___x_3678_);
v_i_3657_ = v___x_3679_;
v_b_3658_ = v___x_3677_;
goto _start;
}
else
{
lean_dec(v_declName_3654_);
return v___x_3676_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__1___boxed(lean_object* v___x_3681_, lean_object* v_declName_3682_, lean_object* v_as_3683_, lean_object* v_sz_3684_, lean_object* v_i_3685_, lean_object* v_b_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_){
_start:
{
size_t v_sz_boxed_3694_; size_t v_i_boxed_3695_; lean_object* v_res_3696_; 
v_sz_boxed_3694_ = lean_unbox_usize(v_sz_3684_);
lean_dec(v_sz_3684_);
v_i_boxed_3695_ = lean_unbox_usize(v_i_3685_);
lean_dec(v_i_3685_);
v_res_3696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__1(v___x_3681_, v_declName_3682_, v_as_3683_, v_sz_boxed_3694_, v_i_boxed_3695_, v_b_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_);
lean_dec(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec_ref(v_as_3683_);
lean_dec_ref(v___x_3681_);
return v_res_3696_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__6___redArg(lean_object* v_a_3697_, lean_object* v_x_3698_){
_start:
{
if (lean_obj_tag(v_x_3698_) == 0)
{
lean_object* v___x_3699_; 
v___x_3699_ = lean_box(0);
return v___x_3699_;
}
else
{
lean_object* v_key_3700_; lean_object* v_value_3701_; lean_object* v_tail_3702_; uint8_t v___x_3703_; 
v_key_3700_ = lean_ctor_get(v_x_3698_, 0);
v_value_3701_ = lean_ctor_get(v_x_3698_, 1);
v_tail_3702_ = lean_ctor_get(v_x_3698_, 2);
v___x_3703_ = lean_name_eq(v_key_3700_, v_a_3697_);
if (v___x_3703_ == 0)
{
v_x_3698_ = v_tail_3702_;
goto _start;
}
else
{
lean_object* v___x_3705_; 
lean_inc(v_value_3701_);
v___x_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3705_, 0, v_value_3701_);
return v___x_3705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__6___redArg___boxed(lean_object* v_a_3706_, lean_object* v_x_3707_){
_start:
{
lean_object* v_res_3708_; 
v_res_3708_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__6___redArg(v_a_3706_, v_x_3707_);
lean_dec(v_x_3707_);
lean_dec(v_a_3706_);
return v_res_3708_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3709_; uint64_t v___x_3710_; 
v___x_3709_ = lean_unsigned_to_nat(1723u);
v___x_3710_ = lean_uint64_of_nat(v___x_3709_);
return v___x_3710_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg(lean_object* v_m_3711_, lean_object* v_a_3712_){
_start:
{
lean_object* v_buckets_3713_; lean_object* v___x_3714_; uint64_t v___y_3716_; 
v_buckets_3713_ = lean_ctor_get(v_m_3711_, 1);
v___x_3714_ = lean_array_get_size(v_buckets_3713_);
if (lean_obj_tag(v_a_3712_) == 0)
{
uint64_t v___x_3730_; 
v___x_3730_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg___closed__0);
v___y_3716_ = v___x_3730_;
goto v___jp_3715_;
}
else
{
uint64_t v_hash_3731_; 
v_hash_3731_ = lean_ctor_get_uint64(v_a_3712_, sizeof(void*)*2);
v___y_3716_ = v_hash_3731_;
goto v___jp_3715_;
}
v___jp_3715_:
{
uint64_t v___x_3717_; uint64_t v___x_3718_; uint64_t v_fold_3719_; uint64_t v___x_3720_; uint64_t v___x_3721_; uint64_t v___x_3722_; size_t v___x_3723_; size_t v___x_3724_; size_t v___x_3725_; size_t v___x_3726_; size_t v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3717_ = 32ULL;
v___x_3718_ = lean_uint64_shift_right(v___y_3716_, v___x_3717_);
v_fold_3719_ = lean_uint64_xor(v___y_3716_, v___x_3718_);
v___x_3720_ = 16ULL;
v___x_3721_ = lean_uint64_shift_right(v_fold_3719_, v___x_3720_);
v___x_3722_ = lean_uint64_xor(v_fold_3719_, v___x_3721_);
v___x_3723_ = lean_uint64_to_usize(v___x_3722_);
v___x_3724_ = lean_usize_of_nat(v___x_3714_);
v___x_3725_ = ((size_t)1ULL);
v___x_3726_ = lean_usize_sub(v___x_3724_, v___x_3725_);
v___x_3727_ = lean_usize_land(v___x_3723_, v___x_3726_);
v___x_3728_ = lean_array_uget_borrowed(v_buckets_3713_, v___x_3727_);
v___x_3729_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__6___redArg(v_a_3712_, v___x_3728_);
return v___x_3729_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg___boxed(lean_object* v_m_3732_, lean_object* v_a_3733_){
_start:
{
lean_object* v_res_3734_; 
v_res_3734_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg(v_m_3732_, v_a_3733_);
lean_dec(v_a_3733_);
lean_dec_ref(v_m_3732_);
return v_res_3734_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
v___x_3737_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__1));
v___x_3738_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__0));
v___x_3739_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_3738_, v___x_3737_);
return v___x_3739_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0(lean_object* v_declName_3742_, uint8_t v_isMeta_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
lean_object* v___x_3751_; lean_object* v_env_3755_; lean_object* v___y_3757_; lean_object* v___x_3770_; 
v___x_3751_ = lean_st_ref_get(v___y_3749_);
v_env_3755_ = lean_ctor_get(v___x_3751_, 0);
lean_inc_ref(v_env_3755_);
lean_dec(v___x_3751_);
v___x_3770_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3755_, v_declName_3742_);
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_dec_ref(v_env_3755_);
lean_dec(v_declName_3742_);
goto v___jp_3752_;
}
else
{
lean_object* v_val_3771_; lean_object* v___x_3772_; lean_object* v_modules_3773_; lean_object* v___x_3774_; uint8_t v___x_3775_; 
v_val_3771_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_val_3771_);
lean_dec_ref(v___x_3770_);
v___x_3772_ = l_Lean_Environment_header(v_env_3755_);
v_modules_3773_ = lean_ctor_get(v___x_3772_, 3);
lean_inc_ref(v_modules_3773_);
lean_dec_ref(v___x_3772_);
v___x_3774_ = lean_array_get_size(v_modules_3773_);
v___x_3775_ = lean_nat_dec_lt(v_val_3771_, v___x_3774_);
if (v___x_3775_ == 0)
{
lean_dec_ref(v_modules_3773_);
lean_dec(v_val_3771_);
lean_dec_ref(v_env_3755_);
lean_dec(v_declName_3742_);
goto v___jp_3752_;
}
else
{
lean_object* v___x_3776_; lean_object* v_env_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; uint8_t v___y_3781_; 
v___x_3776_ = lean_st_ref_get(v___y_3749_);
v_env_3777_ = lean_ctor_get(v___x_3776_, 0);
lean_inc_ref(v_env_3777_);
lean_dec(v___x_3776_);
v___x_3778_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__2);
v___x_3779_ = lean_array_fget(v_modules_3773_, v_val_3771_);
lean_dec(v_val_3771_);
lean_dec_ref(v_modules_3773_);
if (v_isMeta_3743_ == 0)
{
lean_dec_ref(v_env_3777_);
v___y_3781_ = v_isMeta_3743_;
goto v___jp_3780_;
}
else
{
uint8_t v___x_3792_; 
lean_inc(v_declName_3742_);
v___x_3792_ = l_Lean_isMarkedMeta(v_env_3777_, v_declName_3742_);
if (v___x_3792_ == 0)
{
v___y_3781_ = v_isMeta_3743_;
goto v___jp_3780_;
}
else
{
uint8_t v___x_3793_; 
v___x_3793_ = 0;
v___y_3781_ = v___x_3793_;
goto v___jp_3780_;
}
}
v___jp_3780_:
{
lean_object* v_toImport_3782_; lean_object* v_module_3783_; lean_object* v___x_3784_; 
v_toImport_3782_ = lean_ctor_get(v___x_3779_, 0);
lean_inc_ref(v_toImport_3782_);
lean_dec(v___x_3779_);
v_module_3783_ = lean_ctor_get(v_toImport_3782_, 0);
lean_inc(v_module_3783_);
lean_dec_ref(v_toImport_3782_);
lean_inc(v_declName_3742_);
v___x_3784_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0(v_module_3783_, v___y_3781_, v_declName_3742_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
lean_dec_ref(v___x_3784_);
v___x_3785_ = l_Lean_indirectModUseExt;
v___x_3786_ = lean_box(1);
v___x_3787_ = lean_box(0);
lean_inc_ref(v_env_3755_);
v___x_3788_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3778_, v___x_3785_, v_env_3755_, v___x_3786_, v___x_3787_);
v___x_3789_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg(v___x_3788_, v_declName_3742_);
lean_dec(v___x_3788_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v___x_3790_; 
v___x_3790_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__3));
v___y_3757_ = v___x_3790_;
goto v___jp_3756_;
}
else
{
lean_object* v_val_3791_; 
v_val_3791_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_val_3791_);
lean_dec_ref(v___x_3789_);
v___y_3757_ = v_val_3791_;
goto v___jp_3756_;
}
}
else
{
lean_dec_ref(v_env_3755_);
lean_dec(v_declName_3742_);
return v___x_3784_;
}
}
}
}
v___jp_3752_:
{
lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3753_ = lean_box(0);
v___x_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3753_);
return v___x_3754_;
}
v___jp_3756_:
{
lean_object* v___x_3758_; size_t v_sz_3759_; size_t v___x_3760_; lean_object* v___x_3761_; 
v___x_3758_ = lean_box(0);
v_sz_3759_ = lean_array_size(v___y_3757_);
v___x_3760_ = ((size_t)0ULL);
v___x_3761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__1(v_env_3755_, v_declName_3742_, v___y_3757_, v_sz_3759_, v___x_3760_, v___x_3758_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_);
lean_dec_ref(v___y_3757_);
lean_dec_ref(v_env_3755_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3768_ == 0)
{
lean_object* v_unused_3769_; 
v_unused_3769_ = lean_ctor_get(v___x_3761_, 0);
lean_dec(v_unused_3769_);
v___x_3763_ = v___x_3761_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_dec(v___x_3761_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 0, v___x_3758_);
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v___x_3758_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
else
{
return v___x_3761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___boxed(lean_object* v_declName_3794_, lean_object* v_isMeta_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_){
_start:
{
uint8_t v_isMeta_boxed_3803_; lean_object* v_res_3804_; 
v_isMeta_boxed_3803_ = lean_unbox(v_isMeta_3795_);
v_res_3804_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0(v_declName_3794_, v_isMeta_boxed_3803_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
lean_dec(v___y_3801_);
lean_dec_ref(v___y_3800_);
lean_dec(v___y_3799_);
lean_dec_ref(v___y_3798_);
lean_dec(v___y_3797_);
lean_dec_ref(v___y_3796_);
return v_res_3804_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__1(void){
_start:
{
lean_object* v___x_3806_; lean_object* v___x_3807_; 
v___x_3806_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__0));
v___x_3807_ = l_Lean_stringToMessageData(v___x_3806_);
return v___x_3807_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__3(void){
_start:
{
lean_object* v___x_3809_; lean_object* v___x_3810_; 
v___x_3809_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__2));
v___x_3810_ = l_Lean_stringToMessageData(v___x_3809_);
return v___x_3810_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__5(void){
_start:
{
lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3812_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__4));
v___x_3813_ = l_Lean_stringToMessageData(v___x_3812_);
return v___x_3813_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__7(void){
_start:
{
lean_object* v___x_3815_; lean_object* v___x_3816_; 
v___x_3815_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__6));
v___x_3816_ = l_Lean_stringToMessageData(v___x_3815_);
return v___x_3816_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__8(void){
_start:
{
lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3817_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_));
v___x_3818_ = l_Lean_MessageData_ofName(v___x_3817_);
return v___x_3818_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__9(void){
_start:
{
lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3819_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__8, &l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__8);
v___x_3820_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__7, &l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__7);
v___x_3821_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3820_);
lean_ctor_set(v___x_3821_, 1, v___x_3819_);
return v___x_3821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg(lean_object* v_optConfig_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_){
_start:
{
lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; uint8_t v___y_3848_; lean_object* v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; uint8_t v_recover_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; uint8_t v___x_3875_; uint8_t v___x_3876_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; 
v_recover_3870_ = lean_ctor_get_uint8(v_a_3830_, sizeof(void*)*1);
lean_inc(v_optConfig_3829_);
v___x_3871_ = l_Lean_Parser_Tactic_getConfigItems(v_optConfig_3829_);
v___x_3872_ = l_Lean_Elab_Tactic_mkConfigItemViews(v___x_3871_);
v___x_3873_ = lean_array_get_size(v___x_3872_);
v___x_3874_ = lean_unsigned_to_nat(0u);
v___x_3875_ = lean_nat_dec_eq(v___x_3873_, v___x_3874_);
v___x_3876_ = 1;
if (v___x_3875_ == 0)
{
lean_object* v___x_3928_; lean_object* v_fileName_3929_; lean_object* v_fileMap_3930_; lean_object* v_options_3931_; lean_object* v_currRecDepth_3932_; lean_object* v_maxRecDepth_3933_; lean_object* v_ref_3934_; lean_object* v_currNamespace_3935_; lean_object* v_openDecls_3936_; lean_object* v_initHeartbeats_3937_; lean_object* v_maxHeartbeats_3938_; lean_object* v_quotContext_3939_; lean_object* v_currMacroScope_3940_; uint8_t v_diag_3941_; lean_object* v_cancelTk_x3f_3942_; uint8_t v_suppressElabErrors_3943_; lean_object* v_inheritedTraceOptions_3944_; lean_object* v___x_3946_; uint8_t v_isShared_3947_; uint8_t v_isSharedCheck_3965_; 
v___x_3928_ = lean_st_ref_get(v_a_3836_);
v_fileName_3929_ = lean_ctor_get(v_a_3835_, 0);
v_fileMap_3930_ = lean_ctor_get(v_a_3835_, 1);
v_options_3931_ = lean_ctor_get(v_a_3835_, 2);
v_currRecDepth_3932_ = lean_ctor_get(v_a_3835_, 3);
v_maxRecDepth_3933_ = lean_ctor_get(v_a_3835_, 4);
v_ref_3934_ = lean_ctor_get(v_a_3835_, 5);
v_currNamespace_3935_ = lean_ctor_get(v_a_3835_, 6);
v_openDecls_3936_ = lean_ctor_get(v_a_3835_, 7);
v_initHeartbeats_3937_ = lean_ctor_get(v_a_3835_, 8);
v_maxHeartbeats_3938_ = lean_ctor_get(v_a_3835_, 9);
v_quotContext_3939_ = lean_ctor_get(v_a_3835_, 10);
v_currMacroScope_3940_ = lean_ctor_get(v_a_3835_, 11);
v_diag_3941_ = lean_ctor_get_uint8(v_a_3835_, sizeof(void*)*14);
v_cancelTk_x3f_3942_ = lean_ctor_get(v_a_3835_, 12);
v_suppressElabErrors_3943_ = lean_ctor_get_uint8(v_a_3835_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3944_ = lean_ctor_get(v_a_3835_, 13);
v_isSharedCheck_3965_ = !lean_is_exclusive(v_a_3835_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3946_ = v_a_3835_;
v_isShared_3947_ = v_isSharedCheck_3965_;
goto v_resetjp_3945_;
}
else
{
lean_inc(v_inheritedTraceOptions_3944_);
lean_inc(v_cancelTk_x3f_3942_);
lean_inc(v_currMacroScope_3940_);
lean_inc(v_quotContext_3939_);
lean_inc(v_maxHeartbeats_3938_);
lean_inc(v_initHeartbeats_3937_);
lean_inc(v_openDecls_3936_);
lean_inc(v_currNamespace_3935_);
lean_inc(v_ref_3934_);
lean_inc(v_maxRecDepth_3933_);
lean_inc(v_currRecDepth_3932_);
lean_inc(v_options_3931_);
lean_inc(v_fileMap_3930_);
lean_inc(v_fileName_3929_);
lean_dec(v_a_3835_);
v___x_3946_ = lean_box(0);
v_isShared_3947_ = v_isSharedCheck_3965_;
goto v_resetjp_3945_;
}
v_resetjp_3945_:
{
lean_object* v_env_3948_; lean_object* v_ref_3949_; lean_object* v___x_3951_; 
v_env_3948_ = lean_ctor_get(v___x_3928_, 0);
lean_inc_ref(v_env_3948_);
lean_dec(v___x_3928_);
v_ref_3949_ = l_Lean_replaceRef(v_optConfig_3829_, v_ref_3934_);
lean_dec(v_ref_3934_);
lean_dec(v_optConfig_3829_);
if (v_isShared_3947_ == 0)
{
lean_ctor_set(v___x_3946_, 5, v_ref_3949_);
v___x_3951_ = v___x_3946_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_fileName_3929_);
lean_ctor_set(v_reuseFailAlloc_3964_, 1, v_fileMap_3930_);
lean_ctor_set(v_reuseFailAlloc_3964_, 2, v_options_3931_);
lean_ctor_set(v_reuseFailAlloc_3964_, 3, v_currRecDepth_3932_);
lean_ctor_set(v_reuseFailAlloc_3964_, 4, v_maxRecDepth_3933_);
lean_ctor_set(v_reuseFailAlloc_3964_, 5, v_ref_3949_);
lean_ctor_set(v_reuseFailAlloc_3964_, 6, v_currNamespace_3935_);
lean_ctor_set(v_reuseFailAlloc_3964_, 7, v_openDecls_3936_);
lean_ctor_set(v_reuseFailAlloc_3964_, 8, v_initHeartbeats_3937_);
lean_ctor_set(v_reuseFailAlloc_3964_, 9, v_maxHeartbeats_3938_);
lean_ctor_set(v_reuseFailAlloc_3964_, 10, v_quotContext_3939_);
lean_ctor_set(v_reuseFailAlloc_3964_, 11, v_currMacroScope_3940_);
lean_ctor_set(v_reuseFailAlloc_3964_, 12, v_cancelTk_x3f_3942_);
lean_ctor_set(v_reuseFailAlloc_3964_, 13, v_inheritedTraceOptions_3944_);
lean_ctor_set_uint8(v_reuseFailAlloc_3964_, sizeof(void*)*14, v_diag_3941_);
lean_ctor_set_uint8(v_reuseFailAlloc_3964_, sizeof(void*)*14 + 1, v_suppressElabErrors_3943_);
v___x_3951_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
lean_object* v___x_3952_; uint8_t v___x_3953_; 
v___x_3952_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_));
v___x_3953_ = l_Lean_Environment_contains(v_env_3948_, v___x_3952_, v___x_3876_);
if (v___x_3953_ == 0)
{
lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3963_; 
lean_dec_ref(v___x_3872_);
v___x_3954_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__9, &l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__9);
v___x_3955_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg(v___x_3954_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v___x_3951_, v_a_3836_);
lean_dec(v_a_3836_);
lean_dec_ref(v___x_3951_);
lean_dec(v_a_3834_);
lean_dec_ref(v_a_3833_);
lean_dec(v_a_3832_);
v_a_3956_ = lean_ctor_get(v___x_3955_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3955_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3958_ = v___x_3955_;
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3955_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3961_; 
if (v_isShared_3959_ == 0)
{
v___x_3961_ = v___x_3958_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3956_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
else
{
v___y_3878_ = v_a_3831_;
v___y_3879_ = v_a_3832_;
v___y_3880_ = v_a_3833_;
v___y_3881_ = v_a_3834_;
v___y_3882_ = v___x_3951_;
v___y_3883_ = v_a_3836_;
goto v___jp_3877_;
}
}
}
}
else
{
lean_object* v___x_3966_; lean_object* v___x_3967_; 
lean_dec_ref(v___x_3872_);
lean_dec(v_a_3836_);
lean_dec_ref(v_a_3835_);
lean_dec(v_a_3834_);
lean_dec_ref(v_a_3833_);
lean_dec(v_a_3832_);
lean_dec_ref(v_a_3831_);
lean_dec(v_optConfig_3829_);
v___x_3966_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__10));
v___x_3967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3966_);
return v___x_3967_;
}
v___jp_3838_:
{
if (v___y_3848_ == 0)
{
lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; 
lean_dec_ref(v___y_3841_);
v___x_3849_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__1, &l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__1);
v___x_3850_ = l_Lean_MessageData_ofExpr(v___y_3840_);
v___x_3851_ = l_Lean_indentD(v___x_3850_);
v___x_3852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3849_);
lean_ctor_set(v___x_3852_, 1, v___x_3851_);
v___x_3853_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__3, &l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__3);
v___x_3854_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3852_);
lean_ctor_set(v___x_3854_, 1, v___x_3853_);
v___x_3855_ = l_Lean_Exception_toMessageData(v___y_3842_);
v___x_3856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3856_, 0, v___x_3854_);
lean_ctor_set(v___x_3856_, 1, v___x_3855_);
v___x_3857_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg(v___x_3856_, v___y_3847_, v___y_3846_, v___y_3843_, v___y_3839_, v___y_3845_, v___y_3844_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3845_);
lean_dec(v___y_3839_);
lean_dec_ref(v___y_3843_);
lean_dec(v___y_3846_);
return v___x_3857_;
}
else
{
lean_dec_ref(v___y_3847_);
lean_dec(v___y_3846_);
lean_dec_ref(v___y_3845_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec_ref(v___y_3840_);
lean_dec(v___y_3839_);
return v___y_3841_;
}
}
v___jp_3858_:
{
lean_object* v___x_3866_; 
lean_inc(v___y_3865_);
lean_inc_ref(v___y_3864_);
lean_inc(v___y_3863_);
lean_inc_ref(v___y_3862_);
lean_inc_ref(v___y_3859_);
v___x_3866_ = l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(v___y_3859_, v___y_3862_, v___y_3863_, v___y_3864_, v___y_3865_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
lean_dec_ref(v___y_3859_);
return v___x_3866_;
}
else
{
lean_object* v_a_3867_; uint8_t v___x_3868_; 
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
lean_inc(v_a_3867_);
v___x_3868_ = l_Lean_Exception_isInterrupt(v_a_3867_);
if (v___x_3868_ == 0)
{
uint8_t v___x_3869_; 
lean_inc(v_a_3867_);
v___x_3869_ = l_Lean_Exception_isRuntime(v_a_3867_);
v___y_3839_ = v___y_3863_;
v___y_3840_ = v___y_3859_;
v___y_3841_ = v___x_3866_;
v___y_3842_ = v_a_3867_;
v___y_3843_ = v___y_3862_;
v___y_3844_ = v___y_3865_;
v___y_3845_ = v___y_3864_;
v___y_3846_ = v___y_3861_;
v___y_3847_ = v___y_3860_;
v___y_3848_ = v___x_3869_;
goto v___jp_3838_;
}
else
{
v___y_3839_ = v___y_3863_;
v___y_3840_ = v___y_3859_;
v___y_3841_ = v___x_3866_;
v___y_3842_ = v_a_3867_;
v___y_3843_ = v___y_3862_;
v___y_3844_ = v___y_3865_;
v___y_3845_ = v___y_3864_;
v___y_3846_ = v___y_3861_;
v___y_3847_ = v___y_3860_;
v___y_3848_ = v___x_3868_;
goto v___jp_3838_;
}
}
}
v___jp_3877_:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3884_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_));
v___x_3885_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0(v___x_3884_, v___x_3876_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v___x_3886_; 
lean_dec_ref(v___x_3885_);
lean_inc(v___y_3883_);
lean_inc_ref(v___y_3882_);
lean_inc(v___y_3881_);
lean_inc_ref(v___y_3880_);
lean_inc(v___y_3879_);
lean_inc_ref(v___y_3878_);
v___x_3886_ = l_Lean_Elab_Tactic_elabConfig(v_recover_3870_, v___x_3884_, v___x_3872_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3911_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3889_ = v___x_3886_;
v_isShared_3890_ = v_isSharedCheck_3911_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_a_3887_);
lean_dec(v___x_3886_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3911_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
uint8_t v___x_3891_; 
v___x_3891_ = l_Lean_Expr_hasSyntheticSorry(v_a_3887_);
if (v___x_3891_ == 0)
{
uint8_t v___x_3892_; 
lean_del_object(v___x_3889_);
v___x_3892_ = l_Lean_Expr_hasSorry(v_a_3887_);
if (v___x_3892_ == 0)
{
v___y_3859_ = v_a_3887_;
v___y_3860_ = v___y_3878_;
v___y_3861_ = v___y_3879_;
v___y_3862_ = v___y_3880_;
v___y_3863_ = v___y_3881_;
v___y_3864_ = v___y_3882_;
v___y_3865_ = v___y_3883_;
goto v___jp_3858_;
}
else
{
lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v_a_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3902_; 
lean_dec(v_a_3887_);
v___x_3893_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__5, &l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__5);
v___x_3894_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg(v___x_3893_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec(v___y_3879_);
v_a_3895_ = lean_ctor_get(v___x_3894_, 0);
v_isSharedCheck_3902_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3897_ = v___x_3894_;
v_isShared_3898_ = v_isSharedCheck_3902_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_a_3895_);
lean_dec(v___x_3894_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3902_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
lean_object* v___x_3900_; 
if (v_isShared_3898_ == 0)
{
v___x_3900_ = v___x_3897_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v_a_3895_);
v___x_3900_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
return v___x_3900_;
}
}
}
}
else
{
lean_object* v___x_3903_; lean_object* v___x_3904_; uint8_t v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3909_; 
lean_dec(v_a_3887_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
v___x_3903_ = lean_unsigned_to_nat(100000u);
v___x_3904_ = lean_unsigned_to_nat(2u);
v___x_3905_ = 0;
v___x_3906_ = lean_box(0);
v___x_3907_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_3907_, 0, v___x_3903_);
lean_ctor_set(v___x_3907_, 1, v___x_3904_);
lean_ctor_set(v___x_3907_, 2, v___x_3906_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3, v___x_3875_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 1, v___x_3876_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 2, v___x_3875_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 3, v___x_3875_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 4, v___x_3875_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 5, v___x_3875_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 6, v___x_3905_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 7, v___x_3875_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 8, v___x_3875_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 9, v___x_3875_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 10, v___x_3875_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 11, v___x_3875_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 12, v___x_3876_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 13, v___x_3876_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 14, v___x_3875_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 15, v___x_3875_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 16, v___x_3875_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 17, v___x_3876_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 18, v___x_3876_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 19, v___x_3876_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 20, v___x_3876_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 21, v___x_3876_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 22, v___x_3876_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 23, v___x_3876_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 24, v___x_3876_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 25, v___x_3876_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 26, v___x_3875_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 27, v___x_3875_);
lean_ctor_set_uint8(v___x_3907_, sizeof(void*)*3 + 28, v___x_3875_);
if (v_isShared_3890_ == 0)
{
lean_ctor_set(v___x_3889_, 0, v___x_3907_);
v___x_3909_ = v___x_3889_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v___x_3907_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
}
else
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3919_; 
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
v_a_3912_ = lean_ctor_get(v___x_3886_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___x_3886_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3914_ = v___x_3886_;
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___x_3886_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3917_; 
if (v_isShared_3915_ == 0)
{
v___x_3917_ = v___x_3914_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_a_3912_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
}
}
else
{
lean_object* v_a_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3927_; 
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec_ref(v___y_3880_);
lean_dec(v___y_3879_);
lean_dec_ref(v___y_3878_);
lean_dec_ref(v___x_3872_);
v_a_3920_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3922_ = v___x_3885_;
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_a_3920_);
lean_dec(v___x_3885_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___boxed(lean_object* v_optConfig_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_){
_start:
{
lean_object* v_res_3977_; 
v_res_3977_ = l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg(v_optConfig_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_, v_a_3974_, v_a_3975_);
lean_dec_ref(v_a_3969_);
return v_res_3977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig(lean_object* v_optConfig_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_){
_start:
{
lean_object* v___x_3988_; 
v___x_3988_ = l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg(v_optConfig_3978_, v_a_3979_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_);
return v___x_3988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___boxed(lean_object* v_optConfig_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_){
_start:
{
lean_object* v_res_3999_; 
v_res_3999_ = l_Lean_Elab_Tactic_NormCast_elabNormCastConfig(v_optConfig_3989_, v_a_3990_, v_a_3991_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_);
lean_dec(v_a_3991_);
lean_dec_ref(v_a_3990_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1(lean_object* v_00_u03b1_4000_, lean_object* v_msg_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_){
_start:
{
lean_object* v___x_4009_; 
v___x_4009_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg(v_msg_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_);
return v___x_4009_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___boxed(lean_object* v_00_u03b1_4010_, lean_object* v_msg_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_){
_start:
{
lean_object* v_res_4019_; 
v_res_4019_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1(v_00_u03b1_4010_, v_msg_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
lean_dec(v___y_4015_);
lean_dec_ref(v___y_4014_);
lean_dec(v___y_4013_);
return v_res_4019_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2(lean_object* v_cls_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
lean_object* v___x_4028_; 
v___x_4028_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg(v_cls_4020_, v___y_4025_);
return v___x_4028_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_){
_start:
{
lean_object* v_res_4037_; 
v_res_4037_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2(v_cls_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
lean_dec(v___y_4035_);
lean_dec_ref(v___y_4034_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
return v_res_4037_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2(lean_object* v_00_u03b2_4038_, lean_object* v_m_4039_, lean_object* v_a_4040_){
_start:
{
lean_object* v___x_4041_; 
v___x_4041_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg(v_m_4039_, v_a_4040_);
return v___x_4041_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___boxed(lean_object* v_00_u03b2_4042_, lean_object* v_m_4043_, lean_object* v_a_4044_){
_start:
{
lean_object* v_res_4045_; 
v_res_4045_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2(v_00_u03b2_4042_, v_m_4043_, v_a_4044_);
lean_dec(v_a_4044_);
lean_dec_ref(v_m_4043_);
return v_res_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4(lean_object* v_msgData_4046_, lean_object* v_macroStack_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_){
_start:
{
lean_object* v___x_4055_; 
v___x_4055_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg(v_msgData_4046_, v_macroStack_4047_, v___y_4052_);
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___boxed(lean_object* v_msgData_4056_, lean_object* v_macroStack_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_){
_start:
{
lean_object* v_res_4065_; 
v_res_4065_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4(v_msgData_4056_, v_macroStack_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_);
lean_dec(v___y_4063_);
lean_dec_ref(v___y_4062_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
lean_dec(v___y_4059_);
lean_dec_ref(v___y_4058_);
return v_res_4065_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_4066_, lean_object* v_x_4067_, lean_object* v_x_4068_){
_start:
{
uint8_t v___x_4069_; 
v___x_4069_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___redArg(v_x_4067_, v_x_4068_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_4070_, lean_object* v_x_4071_, lean_object* v_x_4072_){
_start:
{
uint8_t v_res_4073_; lean_object* v_r_4074_; 
v_res_4073_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1(v_00_u03b2_4070_, v_x_4071_, v_x_4072_);
lean_dec_ref(v_x_4072_);
v_r_4074_ = lean_box(v_res_4073_);
return v_r_4074_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__3(lean_object* v_cls_4075_, lean_object* v_msg_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
lean_object* v___x_4084_; 
v___x_4084_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__3___redArg(v_cls_4075_, v_msg_4076_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__3___boxed(lean_object* v_cls_4085_, lean_object* v_msg_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_){
_start:
{
lean_object* v_res_4094_; 
v_res_4094_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__3(v_cls_4085_, v_msg_4086_, v___y_4087_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
lean_dec(v___y_4092_);
lean_dec_ref(v___y_4091_);
lean_dec(v___y_4090_);
lean_dec_ref(v___y_4089_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__6(lean_object* v_00_u03b2_4095_, lean_object* v_a_4096_, lean_object* v_x_4097_){
_start:
{
lean_object* v___x_4098_; 
v___x_4098_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__6___redArg(v_a_4096_, v_x_4097_);
return v___x_4098_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__6___boxed(lean_object* v_00_u03b2_4099_, lean_object* v_a_4100_, lean_object* v_x_4101_){
_start:
{
lean_object* v_res_4102_; 
v_res_4102_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__6(v_00_u03b2_4099_, v_a_4100_, v_x_4101_);
lean_dec(v_x_4101_);
lean_dec(v_a_4100_);
return v_res_4102_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_4103_, lean_object* v_x_4104_, size_t v_x_4105_, lean_object* v_x_4106_){
_start:
{
uint8_t v___x_4107_; 
v___x_4107_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg(v_x_4104_, v_x_4105_, v_x_4106_);
return v___x_4107_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_4108_, lean_object* v_x_4109_, lean_object* v_x_4110_, lean_object* v_x_4111_){
_start:
{
size_t v_x_13158__boxed_4112_; uint8_t v_res_4113_; lean_object* v_r_4114_; 
v_x_13158__boxed_4112_ = lean_unbox_usize(v_x_4110_);
lean_dec(v_x_4110_);
v_res_4113_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_4108_, v_x_4109_, v_x_13158__boxed_4112_, v_x_4111_);
lean_dec_ref(v_x_4111_);
v_r_4114_ = lean_box(v_res_4113_);
return v_r_4114_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__8(lean_object* v_00_u03b2_4115_, lean_object* v_keys_4116_, lean_object* v_vals_4117_, lean_object* v_heq_4118_, lean_object* v_i_4119_, lean_object* v_k_4120_){
_start:
{
uint8_t v___x_4121_; 
v___x_4121_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__8___redArg(v_keys_4116_, v_i_4119_, v_k_4120_);
return v___x_4121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__8___boxed(lean_object* v_00_u03b2_4122_, lean_object* v_keys_4123_, lean_object* v_vals_4124_, lean_object* v_heq_4125_, lean_object* v_i_4126_, lean_object* v_k_4127_){
_start:
{
uint8_t v_res_4128_; lean_object* v_r_4129_; 
v_res_4128_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__8(v_00_u03b2_4122_, v_keys_4123_, v_vals_4124_, v_heq_4125_, v_i_4126_, v_k_4127_);
lean_dec_ref(v_k_4127_);
lean_dec_ref(v_vals_4124_);
lean_dec_ref(v_keys_4123_);
v_r_4129_ = lean_box(v_res_4128_);
return v_r_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(lean_object* v_e_4130_, lean_object* v___y_4131_){
_start:
{
uint8_t v___x_4133_; 
v___x_4133_ = l_Lean_Expr_hasMVar(v_e_4130_);
if (v___x_4133_ == 0)
{
lean_object* v___x_4134_; 
v___x_4134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4134_, 0, v_e_4130_);
return v___x_4134_;
}
else
{
lean_object* v___x_4135_; lean_object* v_mctx_4136_; lean_object* v___x_4137_; lean_object* v_fst_4138_; lean_object* v_snd_4139_; lean_object* v___x_4140_; lean_object* v_cache_4141_; lean_object* v_zetaDeltaFVarIds_4142_; lean_object* v_postponed_4143_; lean_object* v_diag_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4153_; 
v___x_4135_ = lean_st_ref_get(v___y_4131_);
v_mctx_4136_ = lean_ctor_get(v___x_4135_, 0);
lean_inc_ref(v_mctx_4136_);
lean_dec(v___x_4135_);
v___x_4137_ = l_Lean_instantiateMVarsCore(v_mctx_4136_, v_e_4130_);
v_fst_4138_ = lean_ctor_get(v___x_4137_, 0);
lean_inc(v_fst_4138_);
v_snd_4139_ = lean_ctor_get(v___x_4137_, 1);
lean_inc(v_snd_4139_);
lean_dec_ref(v___x_4137_);
v___x_4140_ = lean_st_ref_take(v___y_4131_);
v_cache_4141_ = lean_ctor_get(v___x_4140_, 1);
v_zetaDeltaFVarIds_4142_ = lean_ctor_get(v___x_4140_, 2);
v_postponed_4143_ = lean_ctor_get(v___x_4140_, 3);
v_diag_4144_ = lean_ctor_get(v___x_4140_, 4);
v_isSharedCheck_4153_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4153_ == 0)
{
lean_object* v_unused_4154_; 
v_unused_4154_ = lean_ctor_get(v___x_4140_, 0);
lean_dec(v_unused_4154_);
v___x_4146_ = v___x_4140_;
v_isShared_4147_ = v_isSharedCheck_4153_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_diag_4144_);
lean_inc(v_postponed_4143_);
lean_inc(v_zetaDeltaFVarIds_4142_);
lean_inc(v_cache_4141_);
lean_dec(v___x_4140_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4153_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4149_; 
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 0, v_snd_4139_);
v___x_4149_ = v___x_4146_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v_snd_4139_);
lean_ctor_set(v_reuseFailAlloc_4152_, 1, v_cache_4141_);
lean_ctor_set(v_reuseFailAlloc_4152_, 2, v_zetaDeltaFVarIds_4142_);
lean_ctor_set(v_reuseFailAlloc_4152_, 3, v_postponed_4143_);
lean_ctor_set(v_reuseFailAlloc_4152_, 4, v_diag_4144_);
v___x_4149_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
lean_object* v___x_4150_; lean_object* v___x_4151_; 
v___x_4150_ = lean_st_ref_set(v___y_4131_, v___x_4149_);
v___x_4151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4151_, 0, v_fst_4138_);
return v___x_4151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg___boxed(lean_object* v_e_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_){
_start:
{
lean_object* v_res_4158_; 
v_res_4158_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_e_4155_, v___y_4156_);
lean_dec(v___y_4156_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0(lean_object* v_e_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
lean_object* v___x_4165_; 
v___x_4165_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_e_4159_, v___y_4161_);
return v___x_4165_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___boxed(lean_object* v_e_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v_res_4172_; 
v_res_4172_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0(v_e_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
return v_res_4172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__0(lean_object* v_x_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_){
_start:
{
lean_object* v___x_4184_; lean_object* v___x_4185_; 
v___x_4184_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___lam__0___closed__0));
v___x_4185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4184_);
return v___x_4185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__0___boxed(lean_object* v_x_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
lean_object* v_res_4195_; 
v_res_4195_ = l_Lean_Elab_Tactic_NormCast_derive___lam__0(v_x_4186_, v___y_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_);
lean_dec(v___y_4193_);
lean_dec_ref(v___y_4192_);
lean_dec(v___y_4191_);
lean_dec_ref(v___y_4190_);
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
lean_dec(v___y_4187_);
lean_dec_ref(v_x_4186_);
return v_res_4195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__1(lean_object* v_e_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_){
_start:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; 
v___x_4205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4205_, 0, v_e_4196_);
v___x_4206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4206_, 0, v___x_4205_);
return v___x_4206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__1___boxed(lean_object* v_e_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_){
_start:
{
lean_object* v_res_4216_; 
v_res_4216_ = l_Lean_Elab_Tactic_NormCast_derive___lam__1(v_e_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_);
lean_dec(v___y_4214_);
lean_dec_ref(v___y_4213_);
lean_dec(v___y_4212_);
lean_dec_ref(v___y_4211_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
lean_dec(v___y_4208_);
return v_res_4216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__2(lean_object* v___x_4217_, lean_object* v_x_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
lean_object* v___x_4227_; lean_object* v___x_4228_; 
v___x_4227_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4227_, 0, v___x_4217_);
v___x_4228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4228_, 0, v___x_4227_);
return v___x_4228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__2___boxed(lean_object* v___x_4229_, lean_object* v_x_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_){
_start:
{
lean_object* v_res_4239_; 
v_res_4239_ = l_Lean_Elab_Tactic_NormCast_derive___lam__2(v___x_4229_, v_x_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
lean_dec(v___y_4235_);
lean_dec_ref(v___y_4234_);
lean_dec(v___y_4233_);
lean_dec_ref(v___y_4232_);
lean_dec(v___y_4231_);
lean_dec_ref(v_x_4230_);
return v_res_4239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__3(lean_object* v___x_4240_, lean_object* v_x_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
lean_object* v___x_4250_; 
v___x_4250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4250_, 0, v___x_4240_);
return v___x_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__3___boxed(lean_object* v___x_4251_, lean_object* v_x_4252_, lean_object* v___y_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_){
_start:
{
lean_object* v_res_4261_; 
v_res_4261_ = l_Lean_Elab_Tactic_NormCast_derive___lam__3(v___x_4251_, v_x_4252_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
lean_dec(v___y_4259_);
lean_dec_ref(v___y_4258_);
lean_dec(v___y_4257_);
lean_dec_ref(v___y_4256_);
lean_dec(v___y_4255_);
lean_dec_ref(v___y_4254_);
lean_dec(v___y_4253_);
lean_dec_ref(v_x_4252_);
return v_res_4261_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__0(void){
_start:
{
lean_object* v___x_4262_; lean_object* v___x_4263_; 
v___x_4262_ = l_Lean_bombEmoji;
v___x_4263_ = l_Lean_stringToMessageData(v___x_4262_);
return v___x_4263_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__1(void){
_start:
{
lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
v___x_4264_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__3___closed__1);
v___x_4265_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__0, &l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__0_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__0);
v___x_4266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4266_, 0, v___x_4265_);
lean_ctor_set(v___x_4266_, 1, v___x_4264_);
return v___x_4266_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__3(void){
_start:
{
lean_object* v___x_4268_; lean_object* v___x_4269_; 
v___x_4268_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__2));
v___x_4269_ = l_Lean_stringToMessageData(v___x_4268_);
return v___x_4269_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__5(void){
_start:
{
lean_object* v___x_4271_; lean_object* v___x_4272_; 
v___x_4271_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__4));
v___x_4272_ = l_Lean_stringToMessageData(v___x_4271_);
return v___x_4272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__4(lean_object* v_phase_4273_, lean_object* v_x_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_){
_start:
{
if (lean_obj_tag(v_x_4274_) == 0)
{
lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4289_; 
v_isSharedCheck_4289_ = !lean_is_exclusive(v_x_4274_);
if (v_isSharedCheck_4289_ == 0)
{
lean_object* v_unused_4290_; 
v_unused_4290_ = lean_ctor_get(v_x_4274_, 0);
lean_dec(v_unused_4290_);
v___x_4281_ = v_x_4274_;
v_isShared_4282_ = v_isSharedCheck_4289_;
goto v_resetjp_4280_;
}
else
{
lean_dec(v_x_4274_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4289_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4287_; 
v___x_4283_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__1, &l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__1);
v___x_4284_ = l_Lean_stringToMessageData(v_phase_4273_);
v___x_4285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4285_, 0, v___x_4283_);
lean_ctor_set(v___x_4285_, 1, v___x_4284_);
if (v_isShared_4282_ == 0)
{
lean_ctor_set(v___x_4281_, 0, v___x_4285_);
v___x_4287_ = v___x_4281_;
goto v_reusejp_4286_;
}
else
{
lean_object* v_reuseFailAlloc_4288_; 
v_reuseFailAlloc_4288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4288_, 0, v___x_4285_);
v___x_4287_ = v_reuseFailAlloc_4288_;
goto v_reusejp_4286_;
}
v_reusejp_4286_:
{
return v___x_4287_;
}
}
}
else
{
lean_object* v_a_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4306_; 
v_a_4291_ = lean_ctor_get(v_x_4274_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v_x_4274_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4293_ = v_x_4274_;
v_isShared_4294_ = v_isSharedCheck_4306_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_a_4291_);
lean_dec(v_x_4274_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4306_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v_expr_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4304_; 
v_expr_4295_ = lean_ctor_get(v_a_4291_, 0);
lean_inc_ref(v_expr_4295_);
lean_dec(v_a_4291_);
v___x_4296_ = l_Lean_MessageData_ofExpr(v_expr_4295_);
v___x_4297_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__3, &l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__3_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__3);
v___x_4298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4296_);
lean_ctor_set(v___x_4298_, 1, v___x_4297_);
v___x_4299_ = l_Lean_stringToMessageData(v_phase_4273_);
v___x_4300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4300_, 0, v___x_4298_);
lean_ctor_set(v___x_4300_, 1, v___x_4299_);
v___x_4301_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__5, &l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__5);
v___x_4302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4302_, 0, v___x_4300_);
lean_ctor_set(v___x_4302_, 1, v___x_4301_);
if (v_isShared_4294_ == 0)
{
lean_ctor_set_tag(v___x_4293_, 0);
lean_ctor_set(v___x_4293_, 0, v___x_4302_);
v___x_4304_ = v___x_4293_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v___x_4302_);
v___x_4304_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
return v___x_4304_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__4___boxed(lean_object* v_phase_4307_, lean_object* v_x_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_){
_start:
{
lean_object* v_res_4314_; 
v_res_4314_ = l_Lean_Elab_Tactic_NormCast_derive___lam__4(v_phase_4307_, v_x_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
lean_dec(v___y_4312_);
lean_dec_ref(v___y_4311_);
lean_dec(v___y_4310_);
lean_dec_ref(v___y_4309_);
return v_res_4314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__5(lean_object* v___x_4315_, uint8_t v___x_4316_, lean_object* v_phase_4317_, lean_object* v_k_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_){
_start:
{
lean_object* v_options_4324_; uint8_t v_hasTrace_4325_; 
v_options_4324_ = lean_ctor_get(v___y_4321_, 2);
v_hasTrace_4325_ = lean_ctor_get_uint8(v_options_4324_, sizeof(void*)*1);
if (v_hasTrace_4325_ == 0)
{
lean_object* v___x_4326_; 
lean_dec_ref(v_phase_4317_);
lean_dec(v___x_4315_);
v___x_4326_ = lean_apply_5(v_k_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_, lean_box(0));
return v___x_4326_;
}
else
{
lean_object* v___x_4327_; lean_object* v_a_4328_; lean_object* v___f_4329_; lean_object* v___x_4330_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v_a_4334_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v_a_4350_; uint8_t v___x_4401_; 
lean_inc(v___x_4315_);
v___x_4327_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___x_4315_, v___y_4321_);
v_a_4328_ = lean_ctor_get(v___x_4327_, 0);
lean_inc(v_a_4328_);
lean_dec_ref(v___x_4327_);
v___f_4329_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4329_, 0, v_phase_4317_);
v___x_4330_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_4401_ = lean_unbox(v_a_4328_);
if (v___x_4401_ == 0)
{
lean_object* v___x_4402_; uint8_t v___x_4403_; 
v___x_4402_ = l_Lean_trace_profiler;
v___x_4403_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_4324_, v___x_4402_);
if (v___x_4403_ == 0)
{
lean_object* v___x_4404_; 
lean_dec_ref(v___f_4329_);
lean_dec(v_a_4328_);
lean_dec(v___x_4315_);
v___x_4404_ = lean_apply_5(v_k_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_, lean_box(0));
return v___x_4404_;
}
else
{
lean_inc_ref(v_options_4324_);
goto v___jp_4360_;
}
}
else
{
lean_inc_ref(v_options_4324_);
goto v___jp_4360_;
}
v___jp_4331_:
{
lean_object* v___x_4335_; double v___x_4336_; double v___x_4337_; double v___x_4338_; double v___x_4339_; double v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; uint8_t v___x_4345_; lean_object* v___x_4346_; 
v___x_4335_ = lean_io_mono_nanos_now();
v___x_4336_ = lean_float_of_nat(v___y_4333_);
v___x_4337_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1);
v___x_4338_ = lean_float_div(v___x_4336_, v___x_4337_);
v___x_4339_ = lean_float_of_nat(v___x_4335_);
v___x_4340_ = lean_float_div(v___x_4339_, v___x_4337_);
v___x_4341_ = lean_box_float(v___x_4338_);
v___x_4342_ = lean_box_float(v___x_4340_);
v___x_4343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4343_, 0, v___x_4341_);
lean_ctor_set(v___x_4343_, 1, v___x_4342_);
v___x_4344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4344_, 0, v_a_4334_);
lean_ctor_set(v___x_4344_, 1, v___x_4343_);
v___x_4345_ = lean_unbox(v_a_4328_);
lean_dec(v_a_4328_);
v___x_4346_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4315_, v___x_4316_, v___x_4330_, v_options_4324_, v___x_4345_, v___y_4332_, v___f_4329_, v___x_4344_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_);
lean_dec_ref(v_options_4324_);
return v___x_4346_;
}
v___jp_4347_:
{
lean_object* v___x_4351_; double v___x_4352_; double v___x_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; uint8_t v___x_4358_; lean_object* v___x_4359_; 
v___x_4351_ = lean_io_get_num_heartbeats();
v___x_4352_ = lean_float_of_nat(v___y_4349_);
v___x_4353_ = lean_float_of_nat(v___x_4351_);
v___x_4354_ = lean_box_float(v___x_4352_);
v___x_4355_ = lean_box_float(v___x_4353_);
v___x_4356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4356_, 0, v___x_4354_);
lean_ctor_set(v___x_4356_, 1, v___x_4355_);
v___x_4357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4357_, 0, v_a_4350_);
lean_ctor_set(v___x_4357_, 1, v___x_4356_);
v___x_4358_ = lean_unbox(v_a_4328_);
lean_dec(v_a_4328_);
v___x_4359_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4315_, v___x_4316_, v___x_4330_, v_options_4324_, v___x_4358_, v___y_4348_, v___f_4329_, v___x_4357_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_);
lean_dec_ref(v_options_4324_);
return v___x_4359_;
}
v___jp_4360_:
{
lean_object* v___x_4361_; lean_object* v_a_4362_; lean_object* v___x_4363_; uint8_t v___x_4364_; 
v___x_4361_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg(v___y_4322_);
v_a_4362_ = lean_ctor_get(v___x_4361_, 0);
lean_inc(v_a_4362_);
lean_dec_ref(v___x_4361_);
v___x_4363_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4364_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_4324_, v___x_4363_);
if (v___x_4364_ == 0)
{
lean_object* v___x_4365_; lean_object* v___x_4366_; 
v___x_4365_ = lean_io_mono_nanos_now();
lean_inc(v___y_4322_);
lean_inc_ref(v___y_4321_);
lean_inc(v___y_4320_);
lean_inc_ref(v___y_4319_);
v___x_4366_ = lean_apply_5(v_k_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_, lean_box(0));
if (lean_obj_tag(v___x_4366_) == 0)
{
lean_object* v_a_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4374_; 
v_a_4367_ = lean_ctor_get(v___x_4366_, 0);
v_isSharedCheck_4374_ = !lean_is_exclusive(v___x_4366_);
if (v_isSharedCheck_4374_ == 0)
{
v___x_4369_ = v___x_4366_;
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_a_4367_);
lean_dec(v___x_4366_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v___x_4372_; 
if (v_isShared_4370_ == 0)
{
lean_ctor_set_tag(v___x_4369_, 1);
v___x_4372_ = v___x_4369_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4373_; 
v_reuseFailAlloc_4373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4373_, 0, v_a_4367_);
v___x_4372_ = v_reuseFailAlloc_4373_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
v___y_4332_ = v_a_4362_;
v___y_4333_ = v___x_4365_;
v_a_4334_ = v___x_4372_;
goto v___jp_4331_;
}
}
}
else
{
lean_object* v_a_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4382_; 
v_a_4375_ = lean_ctor_get(v___x_4366_, 0);
v_isSharedCheck_4382_ = !lean_is_exclusive(v___x_4366_);
if (v_isSharedCheck_4382_ == 0)
{
v___x_4377_ = v___x_4366_;
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_a_4375_);
lean_dec(v___x_4366_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v___x_4380_; 
if (v_isShared_4378_ == 0)
{
lean_ctor_set_tag(v___x_4377_, 0);
v___x_4380_ = v___x_4377_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4381_; 
v_reuseFailAlloc_4381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4381_, 0, v_a_4375_);
v___x_4380_ = v_reuseFailAlloc_4381_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
v___y_4332_ = v_a_4362_;
v___y_4333_ = v___x_4365_;
v_a_4334_ = v___x_4380_;
goto v___jp_4331_;
}
}
}
}
else
{
lean_object* v___x_4383_; lean_object* v___x_4384_; 
v___x_4383_ = lean_io_get_num_heartbeats();
lean_inc(v___y_4322_);
lean_inc_ref(v___y_4321_);
lean_inc(v___y_4320_);
lean_inc_ref(v___y_4319_);
v___x_4384_ = lean_apply_5(v_k_4318_, v___y_4319_, v___y_4320_, v___y_4321_, v___y_4322_, lean_box(0));
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v_a_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4392_; 
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
v_isSharedCheck_4392_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4392_ == 0)
{
v___x_4387_ = v___x_4384_;
v_isShared_4388_ = v_isSharedCheck_4392_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_a_4385_);
lean_dec(v___x_4384_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4392_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
lean_object* v___x_4390_; 
if (v_isShared_4388_ == 0)
{
lean_ctor_set_tag(v___x_4387_, 1);
v___x_4390_ = v___x_4387_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4391_; 
v_reuseFailAlloc_4391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4391_, 0, v_a_4385_);
v___x_4390_ = v_reuseFailAlloc_4391_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
v___y_4348_ = v_a_4362_;
v___y_4349_ = v___x_4383_;
v_a_4350_ = v___x_4390_;
goto v___jp_4347_;
}
}
}
else
{
lean_object* v_a_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4400_; 
v_a_4393_ = lean_ctor_get(v___x_4384_, 0);
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4384_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4395_ = v___x_4384_;
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_a_4393_);
lean_dec(v___x_4384_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v___x_4398_; 
if (v_isShared_4396_ == 0)
{
lean_ctor_set_tag(v___x_4395_, 0);
v___x_4398_ = v___x_4395_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v_a_4393_);
v___x_4398_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
v___y_4348_ = v_a_4362_;
v___y_4349_ = v___x_4383_;
v_a_4350_ = v___x_4398_;
goto v___jp_4347_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__5___boxed(lean_object* v___x_4405_, lean_object* v___x_4406_, lean_object* v_phase_4407_, lean_object* v_k_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_){
_start:
{
uint8_t v___x_31200__boxed_4414_; lean_object* v_res_4415_; 
v___x_31200__boxed_4414_ = lean_unbox(v___x_4406_);
v_res_4415_ = l_Lean_Elab_Tactic_NormCast_derive___lam__5(v___x_4405_, v___x_31200__boxed_4414_, v_phase_4407_, v_k_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_);
return v_res_4415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__6(lean_object* v___x_4416_, uint8_t v___x_4417_, lean_object* v_e_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_){
_start:
{
lean_object* v_a_4428_; lean_object* v___y_4432_; lean_object* v___x_4442_; 
lean_inc_ref(v_e_4418_);
v___x_4442_ = l_Lean_Elab_Tactic_NormCast_numeralToCoe(v_e_4418_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_);
if (lean_obj_tag(v___x_4442_) == 0)
{
lean_dec_ref(v_e_4418_);
lean_dec(v___x_4416_);
v___y_4432_ = v___x_4442_;
goto v___jp_4431_;
}
else
{
lean_object* v_a_4443_; uint8_t v___y_4445_; uint8_t v___x_4447_; 
v_a_4443_ = lean_ctor_get(v___x_4442_, 0);
lean_inc(v_a_4443_);
v___x_4447_ = l_Lean_Exception_isInterrupt(v_a_4443_);
if (v___x_4447_ == 0)
{
uint8_t v___x_4448_; 
v___x_4448_ = l_Lean_Exception_isRuntime(v_a_4443_);
v___y_4445_ = v___x_4448_;
goto v___jp_4444_;
}
else
{
lean_dec(v_a_4443_);
v___y_4445_ = v___x_4447_;
goto v___jp_4444_;
}
v___jp_4444_:
{
if (v___y_4445_ == 0)
{
lean_object* v___x_4446_; 
lean_dec_ref(v___x_4442_);
v___x_4446_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4446_, 0, v_e_4418_);
lean_ctor_set(v___x_4446_, 1, v___x_4416_);
lean_ctor_set_uint8(v___x_4446_, sizeof(void*)*2, v___x_4417_);
v_a_4428_ = v___x_4446_;
goto v___jp_4427_;
}
else
{
lean_dec_ref(v_e_4418_);
lean_dec(v___x_4416_);
v___y_4432_ = v___x_4442_;
goto v___jp_4431_;
}
}
}
v___jp_4427_:
{
lean_object* v___x_4429_; lean_object* v___x_4430_; 
v___x_4429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4429_, 0, v_a_4428_);
v___x_4430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4430_, 0, v___x_4429_);
return v___x_4430_;
}
v___jp_4431_:
{
if (lean_obj_tag(v___y_4432_) == 0)
{
lean_object* v_a_4433_; 
v_a_4433_ = lean_ctor_get(v___y_4432_, 0);
lean_inc(v_a_4433_);
lean_dec_ref(v___y_4432_);
v_a_4428_ = v_a_4433_;
goto v___jp_4427_;
}
else
{
lean_object* v_a_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4441_; 
v_a_4434_ = lean_ctor_get(v___y_4432_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___y_4432_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4436_ = v___y_4432_;
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_a_4434_);
lean_dec(v___y_4432_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v___x_4439_; 
if (v_isShared_4437_ == 0)
{
v___x_4439_ = v___x_4436_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_a_4434_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
return v___x_4439_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__6___boxed(lean_object* v___x_4449_, lean_object* v___x_4450_, lean_object* v_e_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_){
_start:
{
uint8_t v___x_31382__boxed_4460_; lean_object* v_res_4461_; 
v___x_31382__boxed_4460_ = lean_unbox(v___x_4450_);
v_res_4461_ = l_Lean_Elab_Tactic_NormCast_derive___lam__6(v___x_4449_, v___x_31382__boxed_4460_, v_e_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
return v_res_4461_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__0(void){
_start:
{
lean_object* v___x_4462_; 
v___x_4462_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4462_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1(void){
_start:
{
lean_object* v___x_4463_; lean_object* v___x_4464_; 
v___x_4463_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__0, &l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__0_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__0);
v___x_4464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4464_, 0, v___x_4463_);
return v___x_4464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__7(lean_object* v_config_4465_, lean_object* v___x_4466_, lean_object* v_a_4467_, lean_object* v___x_4468_, lean_object* v___f_4469_, lean_object* v___f_4470_, lean_object* v___f_4471_, lean_object* v___f_4472_, lean_object* v___f_4473_, uint8_t v___x_4474_, lean_object* v_a_4475_, lean_object* v___x_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_){
_start:
{
lean_object* v___x_4482_; 
v___x_4482_ = l_Lean_Meta_Simp_mkContext___redArg(v_config_4465_, v___x_4466_, v_a_4467_, v___y_4477_, v___y_4479_, v___y_4480_);
if (lean_obj_tag(v___x_4482_) == 0)
{
lean_object* v_a_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; size_t v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; 
v_a_4483_ = lean_ctor_get(v___x_4482_, 0);
lean_inc(v_a_4483_);
lean_dec_ref(v___x_4482_);
v___x_4484_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1, &l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1);
lean_inc(v___x_4468_);
v___x_4485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4484_);
lean_ctor_set(v___x_4485_, 1, v___x_4468_);
v___x_4486_ = lean_unsigned_to_nat(32u);
v___x_4487_ = lean_mk_empty_array_with_capacity(v___x_4486_);
v___x_4488_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8);
v___x_4489_ = ((size_t)5ULL);
lean_inc(v___x_4468_);
v___x_4490_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4490_, 0, v___x_4488_);
lean_ctor_set(v___x_4490_, 1, v___x_4487_);
lean_ctor_set(v___x_4490_, 2, v___x_4468_);
lean_ctor_set(v___x_4490_, 3, v___x_4468_);
lean_ctor_set_usize(v___x_4490_, 4, v___x_4489_);
v___x_4491_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4491_, 0, v___x_4484_);
lean_ctor_set(v___x_4491_, 1, v___x_4484_);
lean_ctor_set(v___x_4491_, 2, v___x_4484_);
lean_ctor_set(v___x_4491_, 3, v___x_4490_);
v___x_4492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4492_, 0, v___x_4485_);
lean_ctor_set(v___x_4492_, 1, v___x_4491_);
v___x_4493_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4493_, 0, v___f_4469_);
lean_ctor_set(v___x_4493_, 1, v___f_4470_);
lean_ctor_set(v___x_4493_, 2, v___f_4471_);
lean_ctor_set(v___x_4493_, 3, v___f_4472_);
lean_ctor_set(v___x_4493_, 4, v___f_4473_);
lean_ctor_set_uint8(v___x_4493_, sizeof(void*)*5, v___x_4474_);
lean_inc(v___y_4480_);
lean_inc_ref(v___y_4479_);
lean_inc(v___y_4478_);
lean_inc_ref(v___y_4477_);
v___x_4494_ = l_Lean_Meta_Simp_main(v_a_4475_, v_a_4483_, v___x_4492_, v___x_4493_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_);
if (lean_obj_tag(v___x_4494_) == 0)
{
lean_object* v_a_4495_; lean_object* v_fst_4496_; lean_object* v___x_4497_; 
v_a_4495_ = lean_ctor_get(v___x_4494_, 0);
lean_inc(v_a_4495_);
lean_dec_ref(v___x_4494_);
v_fst_4496_ = lean_ctor_get(v_a_4495_, 0);
lean_inc(v_fst_4496_);
lean_dec(v_a_4495_);
v___x_4497_ = l_Lean_Meta_Simp_Result_mkEqTrans(v___x_4476_, v_fst_4496_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_);
return v___x_4497_;
}
else
{
lean_object* v_a_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4505_; 
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec_ref(v___x_4476_);
v_a_4498_ = lean_ctor_get(v___x_4494_, 0);
v_isSharedCheck_4505_ = !lean_is_exclusive(v___x_4494_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4500_ = v___x_4494_;
v_isShared_4501_ = v_isSharedCheck_4505_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_a_4498_);
lean_dec(v___x_4494_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4505_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v___x_4503_; 
if (v_isShared_4501_ == 0)
{
v___x_4503_ = v___x_4500_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v_a_4498_);
v___x_4503_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
return v___x_4503_;
}
}
}
}
else
{
lean_object* v_a_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4513_; 
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec_ref(v___x_4476_);
lean_dec_ref(v_a_4475_);
lean_dec_ref(v___f_4473_);
lean_dec_ref(v___f_4472_);
lean_dec_ref(v___f_4471_);
lean_dec_ref(v___f_4470_);
lean_dec_ref(v___f_4469_);
lean_dec(v___x_4468_);
v_a_4506_ = lean_ctor_get(v___x_4482_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4482_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4508_ = v___x_4482_;
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_a_4506_);
lean_dec(v___x_4482_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4511_; 
if (v_isShared_4509_ == 0)
{
v___x_4511_ = v___x_4508_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4506_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
return v___x_4511_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__7___boxed(lean_object** _args){
lean_object* v_config_4514_ = _args[0];
lean_object* v___x_4515_ = _args[1];
lean_object* v_a_4516_ = _args[2];
lean_object* v___x_4517_ = _args[3];
lean_object* v___f_4518_ = _args[4];
lean_object* v___f_4519_ = _args[5];
lean_object* v___f_4520_ = _args[6];
lean_object* v___f_4521_ = _args[7];
lean_object* v___f_4522_ = _args[8];
lean_object* v___x_4523_ = _args[9];
lean_object* v_a_4524_ = _args[10];
lean_object* v___x_4525_ = _args[11];
lean_object* v___y_4526_ = _args[12];
lean_object* v___y_4527_ = _args[13];
lean_object* v___y_4528_ = _args[14];
lean_object* v___y_4529_ = _args[15];
lean_object* v___y_4530_ = _args[16];
_start:
{
uint8_t v___x_31473__boxed_4531_; lean_object* v_res_4532_; 
v___x_31473__boxed_4531_ = lean_unbox(v___x_4523_);
v_res_4532_ = l_Lean_Elab_Tactic_NormCast_derive___lam__7(v_config_4514_, v___x_4515_, v_a_4516_, v___x_4517_, v___f_4518_, v___f_4519_, v___f_4520_, v___f_4521_, v___f_4522_, v___x_31473__boxed_4531_, v_a_4524_, v___x_4525_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
return v_res_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__12(lean_object* v_up_4533_, lean_object* v_config_4534_, lean_object* v___x_4535_, lean_object* v_a_4536_, lean_object* v_a_4537_, lean_object* v___x_4538_, lean_object* v___f_4539_, lean_object* v___f_4540_, lean_object* v___f_4541_, lean_object* v___f_4542_, uint8_t v___x_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_){
_start:
{
lean_object* v___x_4549_; 
v___x_4549_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_up_4533_, v___y_4547_);
if (lean_obj_tag(v___x_4549_) == 0)
{
lean_object* v_a_4550_; lean_object* v___x_4551_; 
v_a_4550_ = lean_ctor_get(v___x_4549_, 0);
lean_inc(v_a_4550_);
lean_dec_ref(v___x_4549_);
v___x_4551_ = l_Lean_Meta_Simp_mkContext___redArg(v_config_4534_, v___x_4535_, v_a_4536_, v___y_4544_, v___y_4546_, v___y_4547_);
if (lean_obj_tag(v___x_4551_) == 0)
{
lean_object* v_a_4552_; lean_object* v_expr_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; size_t v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; lean_object* v___x_4565_; 
v_a_4552_ = lean_ctor_get(v___x_4551_, 0);
lean_inc(v_a_4552_);
lean_dec_ref(v___x_4551_);
v_expr_4553_ = lean_ctor_get(v_a_4537_, 0);
v___x_4554_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_upwardAndElim___boxed), 10, 1);
lean_closure_set(v___x_4554_, 0, v_a_4550_);
v___x_4555_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1, &l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1);
lean_inc(v___x_4538_);
v___x_4556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4556_, 0, v___x_4555_);
lean_ctor_set(v___x_4556_, 1, v___x_4538_);
v___x_4557_ = lean_unsigned_to_nat(32u);
v___x_4558_ = lean_mk_empty_array_with_capacity(v___x_4557_);
v___x_4559_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8);
v___x_4560_ = ((size_t)5ULL);
lean_inc(v___x_4538_);
v___x_4561_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4561_, 0, v___x_4559_);
lean_ctor_set(v___x_4561_, 1, v___x_4558_);
lean_ctor_set(v___x_4561_, 2, v___x_4538_);
lean_ctor_set(v___x_4561_, 3, v___x_4538_);
lean_ctor_set_usize(v___x_4561_, 4, v___x_4560_);
v___x_4562_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4562_, 0, v___x_4555_);
lean_ctor_set(v___x_4562_, 1, v___x_4555_);
lean_ctor_set(v___x_4562_, 2, v___x_4555_);
lean_ctor_set(v___x_4562_, 3, v___x_4561_);
v___x_4563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4563_, 0, v___x_4556_);
lean_ctor_set(v___x_4563_, 1, v___x_4562_);
v___x_4564_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4564_, 0, v___f_4539_);
lean_ctor_set(v___x_4564_, 1, v___x_4554_);
lean_ctor_set(v___x_4564_, 2, v___f_4540_);
lean_ctor_set(v___x_4564_, 3, v___f_4541_);
lean_ctor_set(v___x_4564_, 4, v___f_4542_);
lean_ctor_set_uint8(v___x_4564_, sizeof(void*)*5, v___x_4543_);
lean_inc(v___y_4547_);
lean_inc_ref(v___y_4546_);
lean_inc(v___y_4545_);
lean_inc_ref(v___y_4544_);
lean_inc_ref(v_expr_4553_);
v___x_4565_ = l_Lean_Meta_Simp_main(v_expr_4553_, v_a_4552_, v___x_4563_, v___x_4564_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_);
if (lean_obj_tag(v___x_4565_) == 0)
{
lean_object* v_a_4566_; lean_object* v_fst_4567_; lean_object* v___x_4568_; 
v_a_4566_ = lean_ctor_get(v___x_4565_, 0);
lean_inc(v_a_4566_);
lean_dec_ref(v___x_4565_);
v_fst_4567_ = lean_ctor_get(v_a_4566_, 0);
lean_inc(v_fst_4567_);
lean_dec(v_a_4566_);
v___x_4568_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_4537_, v_fst_4567_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_);
return v___x_4568_;
}
else
{
lean_object* v_a_4569_; lean_object* v___x_4571_; uint8_t v_isShared_4572_; uint8_t v_isSharedCheck_4576_; 
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
lean_dec(v___y_4545_);
lean_dec_ref(v___y_4544_);
lean_dec_ref(v_a_4537_);
v_a_4569_ = lean_ctor_get(v___x_4565_, 0);
v_isSharedCheck_4576_ = !lean_is_exclusive(v___x_4565_);
if (v_isSharedCheck_4576_ == 0)
{
v___x_4571_ = v___x_4565_;
v_isShared_4572_ = v_isSharedCheck_4576_;
goto v_resetjp_4570_;
}
else
{
lean_inc(v_a_4569_);
lean_dec(v___x_4565_);
v___x_4571_ = lean_box(0);
v_isShared_4572_ = v_isSharedCheck_4576_;
goto v_resetjp_4570_;
}
v_resetjp_4570_:
{
lean_object* v___x_4574_; 
if (v_isShared_4572_ == 0)
{
v___x_4574_ = v___x_4571_;
goto v_reusejp_4573_;
}
else
{
lean_object* v_reuseFailAlloc_4575_; 
v_reuseFailAlloc_4575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4575_, 0, v_a_4569_);
v___x_4574_ = v_reuseFailAlloc_4575_;
goto v_reusejp_4573_;
}
v_reusejp_4573_:
{
return v___x_4574_;
}
}
}
}
else
{
lean_object* v_a_4577_; lean_object* v___x_4579_; uint8_t v_isShared_4580_; uint8_t v_isSharedCheck_4584_; 
lean_dec(v_a_4550_);
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
lean_dec(v___y_4545_);
lean_dec_ref(v___y_4544_);
lean_dec_ref(v___f_4542_);
lean_dec_ref(v___f_4541_);
lean_dec_ref(v___f_4540_);
lean_dec_ref(v___f_4539_);
lean_dec(v___x_4538_);
lean_dec_ref(v_a_4537_);
v_a_4577_ = lean_ctor_get(v___x_4551_, 0);
v_isSharedCheck_4584_ = !lean_is_exclusive(v___x_4551_);
if (v_isSharedCheck_4584_ == 0)
{
v___x_4579_ = v___x_4551_;
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
else
{
lean_inc(v_a_4577_);
lean_dec(v___x_4551_);
v___x_4579_ = lean_box(0);
v_isShared_4580_ = v_isSharedCheck_4584_;
goto v_resetjp_4578_;
}
v_resetjp_4578_:
{
lean_object* v___x_4582_; 
if (v_isShared_4580_ == 0)
{
v___x_4582_ = v___x_4579_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4583_; 
v_reuseFailAlloc_4583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
v___x_4582_ = v_reuseFailAlloc_4583_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
return v___x_4582_;
}
}
}
}
else
{
lean_object* v_a_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4592_; 
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
lean_dec(v___y_4545_);
lean_dec_ref(v___y_4544_);
lean_dec_ref(v___f_4542_);
lean_dec_ref(v___f_4541_);
lean_dec_ref(v___f_4540_);
lean_dec_ref(v___f_4539_);
lean_dec(v___x_4538_);
lean_dec_ref(v_a_4537_);
lean_dec_ref(v_a_4536_);
lean_dec_ref(v___x_4535_);
lean_dec_ref(v_config_4534_);
v_a_4585_ = lean_ctor_get(v___x_4549_, 0);
v_isSharedCheck_4592_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4592_ == 0)
{
v___x_4587_ = v___x_4549_;
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_a_4585_);
lean_dec(v___x_4549_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4592_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v___x_4590_; 
if (v_isShared_4588_ == 0)
{
v___x_4590_ = v___x_4587_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4591_; 
v_reuseFailAlloc_4591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4591_, 0, v_a_4585_);
v___x_4590_ = v_reuseFailAlloc_4591_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
return v___x_4590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__12___boxed(lean_object* v_up_4593_, lean_object* v_config_4594_, lean_object* v___x_4595_, lean_object* v_a_4596_, lean_object* v_a_4597_, lean_object* v___x_4598_, lean_object* v___f_4599_, lean_object* v___f_4600_, lean_object* v___f_4601_, lean_object* v___f_4602_, lean_object* v___x_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_){
_start:
{
uint8_t v___x_31592__boxed_4609_; lean_object* v_res_4610_; 
v___x_31592__boxed_4609_ = lean_unbox(v___x_4603_);
v_res_4610_ = l_Lean_Elab_Tactic_NormCast_derive___lam__12(v_up_4593_, v_config_4594_, v___x_4595_, v_a_4596_, v_a_4597_, v___x_4598_, v___f_4599_, v___f_4600_, v___f_4601_, v___f_4602_, v___x_31592__boxed_4609_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_);
lean_dec_ref(v_up_4593_);
return v_res_4610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__8(lean_object* v_squash_4611_, lean_object* v_config_4612_, lean_object* v_a_4613_, lean_object* v_a_4614_, lean_object* v___x_4615_, lean_object* v_a_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_){
_start:
{
lean_object* v___x_4622_; 
v___x_4622_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_squash_4611_, v___y_4620_);
if (lean_obj_tag(v___x_4622_) == 0)
{
lean_object* v_a_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; 
v_a_4623_ = lean_ctor_get(v___x_4622_, 0);
lean_inc(v_a_4623_);
lean_dec_ref(v___x_4622_);
v___x_4624_ = lean_unsigned_to_nat(1u);
v___x_4625_ = lean_mk_empty_array_with_capacity(v___x_4624_);
v___x_4626_ = lean_array_push(v___x_4625_, v_a_4623_);
v___x_4627_ = l_Lean_Meta_Simp_mkContext___redArg(v_config_4612_, v___x_4626_, v_a_4613_, v___y_4617_, v___y_4619_, v___y_4620_);
if (lean_obj_tag(v___x_4627_) == 0)
{
lean_object* v_a_4628_; lean_object* v_expr_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; size_t v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4640_; 
v_a_4628_ = lean_ctor_get(v___x_4627_, 0);
lean_inc(v_a_4628_);
lean_dec_ref(v___x_4627_);
v_expr_4629_ = lean_ctor_get(v_a_4614_, 0);
v___x_4630_ = lean_box(0);
v___x_4631_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1, &l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1);
lean_inc(v___x_4615_);
v___x_4632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4632_, 0, v___x_4631_);
lean_ctor_set(v___x_4632_, 1, v___x_4615_);
v___x_4633_ = lean_unsigned_to_nat(32u);
v___x_4634_ = lean_mk_empty_array_with_capacity(v___x_4633_);
v___x_4635_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8);
v___x_4636_ = ((size_t)5ULL);
lean_inc(v___x_4615_);
v___x_4637_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4637_, 0, v___x_4635_);
lean_ctor_set(v___x_4637_, 1, v___x_4634_);
lean_ctor_set(v___x_4637_, 2, v___x_4615_);
lean_ctor_set(v___x_4637_, 3, v___x_4615_);
lean_ctor_set_usize(v___x_4637_, 4, v___x_4636_);
v___x_4638_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4638_, 0, v___x_4631_);
lean_ctor_set(v___x_4638_, 1, v___x_4631_);
lean_ctor_set(v___x_4638_, 2, v___x_4631_);
lean_ctor_set(v___x_4638_, 3, v___x_4637_);
v___x_4639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4639_, 0, v___x_4632_);
lean_ctor_set(v___x_4639_, 1, v___x_4638_);
lean_inc(v___y_4620_);
lean_inc_ref(v___y_4619_);
lean_inc(v___y_4618_);
lean_inc_ref(v___y_4617_);
lean_inc_ref(v_expr_4629_);
v___x_4640_ = l_Lean_Meta_simp(v_expr_4629_, v_a_4628_, v_a_4616_, v___x_4630_, v___x_4639_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_);
lean_dec_ref(v___x_4639_);
if (lean_obj_tag(v___x_4640_) == 0)
{
lean_object* v_a_4641_; lean_object* v_fst_4642_; lean_object* v___x_4643_; 
v_a_4641_ = lean_ctor_get(v___x_4640_, 0);
lean_inc(v_a_4641_);
lean_dec_ref(v___x_4640_);
v_fst_4642_ = lean_ctor_get(v_a_4641_, 0);
lean_inc(v_fst_4642_);
lean_dec(v_a_4641_);
v___x_4643_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_4614_, v_fst_4642_, v___y_4617_, v___y_4618_, v___y_4619_, v___y_4620_);
return v___x_4643_;
}
else
{
lean_object* v_a_4644_; lean_object* v___x_4646_; uint8_t v_isShared_4647_; uint8_t v_isSharedCheck_4651_; 
lean_dec(v___y_4620_);
lean_dec_ref(v___y_4619_);
lean_dec(v___y_4618_);
lean_dec_ref(v___y_4617_);
lean_dec_ref(v_a_4614_);
v_a_4644_ = lean_ctor_get(v___x_4640_, 0);
v_isSharedCheck_4651_ = !lean_is_exclusive(v___x_4640_);
if (v_isSharedCheck_4651_ == 0)
{
v___x_4646_ = v___x_4640_;
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
else
{
lean_inc(v_a_4644_);
lean_dec(v___x_4640_);
v___x_4646_ = lean_box(0);
v_isShared_4647_ = v_isSharedCheck_4651_;
goto v_resetjp_4645_;
}
v_resetjp_4645_:
{
lean_object* v___x_4649_; 
if (v_isShared_4647_ == 0)
{
v___x_4649_ = v___x_4646_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v_a_4644_);
v___x_4649_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
return v___x_4649_;
}
}
}
}
else
{
lean_object* v_a_4652_; lean_object* v___x_4654_; uint8_t v_isShared_4655_; uint8_t v_isSharedCheck_4659_; 
lean_dec(v___y_4620_);
lean_dec_ref(v___y_4619_);
lean_dec(v___y_4618_);
lean_dec_ref(v___y_4617_);
lean_dec_ref(v_a_4616_);
lean_dec(v___x_4615_);
lean_dec_ref(v_a_4614_);
v_a_4652_ = lean_ctor_get(v___x_4627_, 0);
v_isSharedCheck_4659_ = !lean_is_exclusive(v___x_4627_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4654_ = v___x_4627_;
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
else
{
lean_inc(v_a_4652_);
lean_dec(v___x_4627_);
v___x_4654_ = lean_box(0);
v_isShared_4655_ = v_isSharedCheck_4659_;
goto v_resetjp_4653_;
}
v_resetjp_4653_:
{
lean_object* v___x_4657_; 
if (v_isShared_4655_ == 0)
{
v___x_4657_ = v___x_4654_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v_a_4652_);
v___x_4657_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
return v___x_4657_;
}
}
}
}
else
{
lean_object* v_a_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4667_; 
lean_dec(v___y_4620_);
lean_dec_ref(v___y_4619_);
lean_dec(v___y_4618_);
lean_dec_ref(v___y_4617_);
lean_dec_ref(v_a_4616_);
lean_dec(v___x_4615_);
lean_dec_ref(v_a_4614_);
lean_dec_ref(v_a_4613_);
lean_dec_ref(v_config_4612_);
v_a_4660_ = lean_ctor_get(v___x_4622_, 0);
v_isSharedCheck_4667_ = !lean_is_exclusive(v___x_4622_);
if (v_isSharedCheck_4667_ == 0)
{
v___x_4662_ = v___x_4622_;
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_a_4660_);
lean_dec(v___x_4622_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4667_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
lean_object* v___x_4665_; 
if (v_isShared_4663_ == 0)
{
v___x_4665_ = v___x_4662_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v_a_4660_);
v___x_4665_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
return v___x_4665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__8___boxed(lean_object* v_squash_4668_, lean_object* v_config_4669_, lean_object* v_a_4670_, lean_object* v_a_4671_, lean_object* v___x_4672_, lean_object* v_a_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_){
_start:
{
lean_object* v_res_4679_; 
v_res_4679_ = l_Lean_Elab_Tactic_NormCast_derive___lam__8(v_squash_4668_, v_config_4669_, v_a_4670_, v_a_4671_, v___x_4672_, v_a_4673_, v___y_4674_, v___y_4675_, v___y_4676_, v___y_4677_);
lean_dec_ref(v_squash_4668_);
return v_res_4679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__18(lean_object* v_e_4680_, lean_object* v_x_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_){
_start:
{
lean_object* v___x_4687_; lean_object* v___x_4688_; 
v___x_4687_ = l_Lean_MessageData_ofExpr(v_e_4680_);
v___x_4688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4688_, 0, v___x_4687_);
return v___x_4688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__18___boxed(lean_object* v_e_4689_, lean_object* v_x_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_){
_start:
{
lean_object* v_res_4696_; 
v_res_4696_ = l_Lean_Elab_Tactic_NormCast_derive___lam__18(v_e_4689_, v_x_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
lean_dec(v___y_4694_);
lean_dec_ref(v___y_4693_);
lean_dec(v___y_4692_);
lean_dec_ref(v___y_4691_);
lean_dec_ref(v_x_4690_);
return v_res_4696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__10(lean_object* v___x_4697_, uint8_t v_hasTrace_4698_, lean_object* v_phase_4699_, lean_object* v_k_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_){
_start:
{
lean_object* v_options_4706_; uint8_t v_hasTrace_4707_; 
v_options_4706_ = lean_ctor_get(v___y_4703_, 2);
v_hasTrace_4707_ = lean_ctor_get_uint8(v_options_4706_, sizeof(void*)*1);
if (v_hasTrace_4707_ == 0)
{
lean_object* v___x_4708_; 
lean_dec_ref(v_phase_4699_);
lean_dec(v___x_4697_);
v___x_4708_ = lean_apply_5(v_k_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_, lean_box(0));
return v___x_4708_;
}
else
{
lean_object* v___x_4709_; lean_object* v_a_4710_; lean_object* v___f_4711_; lean_object* v___x_4712_; lean_object* v___y_4714_; lean_object* v___y_4715_; lean_object* v_a_4716_; lean_object* v___y_4730_; lean_object* v___y_4731_; lean_object* v_a_4732_; uint8_t v___x_4783_; 
lean_inc(v___x_4697_);
v___x_4709_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___x_4697_, v___y_4703_);
v_a_4710_ = lean_ctor_get(v___x_4709_, 0);
lean_inc(v_a_4710_);
lean_dec_ref(v___x_4709_);
v___f_4711_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4711_, 0, v_phase_4699_);
v___x_4712_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_4783_ = lean_unbox(v_a_4710_);
if (v___x_4783_ == 0)
{
lean_object* v___x_4784_; uint8_t v___x_4785_; 
v___x_4784_ = l_Lean_trace_profiler;
v___x_4785_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_4706_, v___x_4784_);
if (v___x_4785_ == 0)
{
lean_object* v___x_4786_; 
lean_dec_ref(v___f_4711_);
lean_dec(v_a_4710_);
lean_dec(v___x_4697_);
v___x_4786_ = lean_apply_5(v_k_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_, lean_box(0));
return v___x_4786_;
}
else
{
lean_inc_ref(v_options_4706_);
goto v___jp_4742_;
}
}
else
{
lean_inc_ref(v_options_4706_);
goto v___jp_4742_;
}
v___jp_4713_:
{
lean_object* v___x_4717_; double v___x_4718_; double v___x_4719_; double v___x_4720_; double v___x_4721_; double v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; uint8_t v___x_4727_; lean_object* v___x_4728_; 
v___x_4717_ = lean_io_mono_nanos_now();
v___x_4718_ = lean_float_of_nat(v___y_4714_);
v___x_4719_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1);
v___x_4720_ = lean_float_div(v___x_4718_, v___x_4719_);
v___x_4721_ = lean_float_of_nat(v___x_4717_);
v___x_4722_ = lean_float_div(v___x_4721_, v___x_4719_);
v___x_4723_ = lean_box_float(v___x_4720_);
v___x_4724_ = lean_box_float(v___x_4722_);
v___x_4725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4725_, 0, v___x_4723_);
lean_ctor_set(v___x_4725_, 1, v___x_4724_);
v___x_4726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4726_, 0, v_a_4716_);
lean_ctor_set(v___x_4726_, 1, v___x_4725_);
v___x_4727_ = lean_unbox(v_a_4710_);
lean_dec(v_a_4710_);
v___x_4728_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4697_, v_hasTrace_4698_, v___x_4712_, v_options_4706_, v___x_4727_, v___y_4715_, v___f_4711_, v___x_4726_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_);
lean_dec_ref(v_options_4706_);
return v___x_4728_;
}
v___jp_4729_:
{
lean_object* v___x_4733_; double v___x_4734_; double v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; uint8_t v___x_4740_; lean_object* v___x_4741_; 
v___x_4733_ = lean_io_get_num_heartbeats();
v___x_4734_ = lean_float_of_nat(v___y_4730_);
v___x_4735_ = lean_float_of_nat(v___x_4733_);
v___x_4736_ = lean_box_float(v___x_4734_);
v___x_4737_ = lean_box_float(v___x_4735_);
v___x_4738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4738_, 0, v___x_4736_);
lean_ctor_set(v___x_4738_, 1, v___x_4737_);
v___x_4739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4739_, 0, v_a_4732_);
lean_ctor_set(v___x_4739_, 1, v___x_4738_);
v___x_4740_ = lean_unbox(v_a_4710_);
lean_dec(v_a_4710_);
v___x_4741_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4697_, v_hasTrace_4698_, v___x_4712_, v_options_4706_, v___x_4740_, v___y_4731_, v___f_4711_, v___x_4739_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_);
lean_dec_ref(v_options_4706_);
return v___x_4741_;
}
v___jp_4742_:
{
lean_object* v___x_4743_; lean_object* v_a_4744_; lean_object* v___x_4745_; uint8_t v___x_4746_; 
v___x_4743_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg(v___y_4704_);
v_a_4744_ = lean_ctor_get(v___x_4743_, 0);
lean_inc(v_a_4744_);
lean_dec_ref(v___x_4743_);
v___x_4745_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4746_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_4706_, v___x_4745_);
if (v___x_4746_ == 0)
{
lean_object* v___x_4747_; lean_object* v___x_4748_; 
v___x_4747_ = lean_io_mono_nanos_now();
lean_inc(v___y_4704_);
lean_inc_ref(v___y_4703_);
lean_inc(v___y_4702_);
lean_inc_ref(v___y_4701_);
v___x_4748_ = lean_apply_5(v_k_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_, lean_box(0));
if (lean_obj_tag(v___x_4748_) == 0)
{
lean_object* v_a_4749_; lean_object* v___x_4751_; uint8_t v_isShared_4752_; uint8_t v_isSharedCheck_4756_; 
v_a_4749_ = lean_ctor_get(v___x_4748_, 0);
v_isSharedCheck_4756_ = !lean_is_exclusive(v___x_4748_);
if (v_isSharedCheck_4756_ == 0)
{
v___x_4751_ = v___x_4748_;
v_isShared_4752_ = v_isSharedCheck_4756_;
goto v_resetjp_4750_;
}
else
{
lean_inc(v_a_4749_);
lean_dec(v___x_4748_);
v___x_4751_ = lean_box(0);
v_isShared_4752_ = v_isSharedCheck_4756_;
goto v_resetjp_4750_;
}
v_resetjp_4750_:
{
lean_object* v___x_4754_; 
if (v_isShared_4752_ == 0)
{
lean_ctor_set_tag(v___x_4751_, 1);
v___x_4754_ = v___x_4751_;
goto v_reusejp_4753_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v_a_4749_);
v___x_4754_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4753_;
}
v_reusejp_4753_:
{
v___y_4714_ = v___x_4747_;
v___y_4715_ = v_a_4744_;
v_a_4716_ = v___x_4754_;
goto v___jp_4713_;
}
}
}
else
{
lean_object* v_a_4757_; lean_object* v___x_4759_; uint8_t v_isShared_4760_; uint8_t v_isSharedCheck_4764_; 
v_a_4757_ = lean_ctor_get(v___x_4748_, 0);
v_isSharedCheck_4764_ = !lean_is_exclusive(v___x_4748_);
if (v_isSharedCheck_4764_ == 0)
{
v___x_4759_ = v___x_4748_;
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
else
{
lean_inc(v_a_4757_);
lean_dec(v___x_4748_);
v___x_4759_ = lean_box(0);
v_isShared_4760_ = v_isSharedCheck_4764_;
goto v_resetjp_4758_;
}
v_resetjp_4758_:
{
lean_object* v___x_4762_; 
if (v_isShared_4760_ == 0)
{
lean_ctor_set_tag(v___x_4759_, 0);
v___x_4762_ = v___x_4759_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v_a_4757_);
v___x_4762_ = v_reuseFailAlloc_4763_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
v___y_4714_ = v___x_4747_;
v___y_4715_ = v_a_4744_;
v_a_4716_ = v___x_4762_;
goto v___jp_4713_;
}
}
}
}
else
{
lean_object* v___x_4765_; lean_object* v___x_4766_; 
v___x_4765_ = lean_io_get_num_heartbeats();
lean_inc(v___y_4704_);
lean_inc_ref(v___y_4703_);
lean_inc(v___y_4702_);
lean_inc_ref(v___y_4701_);
v___x_4766_ = lean_apply_5(v_k_4700_, v___y_4701_, v___y_4702_, v___y_4703_, v___y_4704_, lean_box(0));
if (lean_obj_tag(v___x_4766_) == 0)
{
lean_object* v_a_4767_; lean_object* v___x_4769_; uint8_t v_isShared_4770_; uint8_t v_isSharedCheck_4774_; 
v_a_4767_ = lean_ctor_get(v___x_4766_, 0);
v_isSharedCheck_4774_ = !lean_is_exclusive(v___x_4766_);
if (v_isSharedCheck_4774_ == 0)
{
v___x_4769_ = v___x_4766_;
v_isShared_4770_ = v_isSharedCheck_4774_;
goto v_resetjp_4768_;
}
else
{
lean_inc(v_a_4767_);
lean_dec(v___x_4766_);
v___x_4769_ = lean_box(0);
v_isShared_4770_ = v_isSharedCheck_4774_;
goto v_resetjp_4768_;
}
v_resetjp_4768_:
{
lean_object* v___x_4772_; 
if (v_isShared_4770_ == 0)
{
lean_ctor_set_tag(v___x_4769_, 1);
v___x_4772_ = v___x_4769_;
goto v_reusejp_4771_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v_a_4767_);
v___x_4772_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4771_;
}
v_reusejp_4771_:
{
v___y_4730_ = v___x_4765_;
v___y_4731_ = v_a_4744_;
v_a_4732_ = v___x_4772_;
goto v___jp_4729_;
}
}
}
else
{
lean_object* v_a_4775_; lean_object* v___x_4777_; uint8_t v_isShared_4778_; uint8_t v_isSharedCheck_4782_; 
v_a_4775_ = lean_ctor_get(v___x_4766_, 0);
v_isSharedCheck_4782_ = !lean_is_exclusive(v___x_4766_);
if (v_isSharedCheck_4782_ == 0)
{
v___x_4777_ = v___x_4766_;
v_isShared_4778_ = v_isSharedCheck_4782_;
goto v_resetjp_4776_;
}
else
{
lean_inc(v_a_4775_);
lean_dec(v___x_4766_);
v___x_4777_ = lean_box(0);
v_isShared_4778_ = v_isSharedCheck_4782_;
goto v_resetjp_4776_;
}
v_resetjp_4776_:
{
lean_object* v___x_4780_; 
if (v_isShared_4778_ == 0)
{
lean_ctor_set_tag(v___x_4777_, 0);
v___x_4780_ = v___x_4777_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v_a_4775_);
v___x_4780_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
v___y_4730_ = v___x_4765_;
v___y_4731_ = v_a_4744_;
v_a_4732_ = v___x_4780_;
goto v___jp_4729_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__10___boxed(lean_object* v___x_4787_, lean_object* v_hasTrace_4788_, lean_object* v_phase_4789_, lean_object* v_k_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_){
_start:
{
uint8_t v_hasTrace_boxed_4796_; lean_object* v_res_4797_; 
v_hasTrace_boxed_4796_ = lean_unbox(v_hasTrace_4788_);
v_res_4797_ = l_Lean_Elab_Tactic_NormCast_derive___lam__10(v___x_4787_, v_hasTrace_boxed_4796_, v_phase_4789_, v_k_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_);
return v_res_4797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__9(lean_object* v___x_4798_, uint8_t v_hasTrace_4799_, lean_object* v_e_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_){
_start:
{
lean_object* v_a_4810_; lean_object* v___y_4814_; lean_object* v___x_4824_; 
lean_inc_ref(v_e_4800_);
v___x_4824_ = l_Lean_Elab_Tactic_NormCast_numeralToCoe(v_e_4800_, v___y_4804_, v___y_4805_, v___y_4806_, v___y_4807_);
if (lean_obj_tag(v___x_4824_) == 0)
{
lean_dec_ref(v_e_4800_);
lean_dec(v___x_4798_);
v___y_4814_ = v___x_4824_;
goto v___jp_4813_;
}
else
{
lean_object* v_a_4825_; uint8_t v___y_4827_; uint8_t v___x_4829_; 
v_a_4825_ = lean_ctor_get(v___x_4824_, 0);
lean_inc(v_a_4825_);
v___x_4829_ = l_Lean_Exception_isInterrupt(v_a_4825_);
if (v___x_4829_ == 0)
{
uint8_t v___x_4830_; 
v___x_4830_ = l_Lean_Exception_isRuntime(v_a_4825_);
v___y_4827_ = v___x_4830_;
goto v___jp_4826_;
}
else
{
lean_dec(v_a_4825_);
v___y_4827_ = v___x_4829_;
goto v___jp_4826_;
}
v___jp_4826_:
{
if (v___y_4827_ == 0)
{
lean_object* v___x_4828_; 
lean_dec_ref(v___x_4824_);
v___x_4828_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4828_, 0, v_e_4800_);
lean_ctor_set(v___x_4828_, 1, v___x_4798_);
lean_ctor_set_uint8(v___x_4828_, sizeof(void*)*2, v_hasTrace_4799_);
v_a_4810_ = v___x_4828_;
goto v___jp_4809_;
}
else
{
lean_dec_ref(v_e_4800_);
lean_dec(v___x_4798_);
v___y_4814_ = v___x_4824_;
goto v___jp_4813_;
}
}
}
v___jp_4809_:
{
lean_object* v___x_4811_; lean_object* v___x_4812_; 
v___x_4811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4811_, 0, v_a_4810_);
v___x_4812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4812_, 0, v___x_4811_);
return v___x_4812_;
}
v___jp_4813_:
{
if (lean_obj_tag(v___y_4814_) == 0)
{
lean_object* v_a_4815_; 
v_a_4815_ = lean_ctor_get(v___y_4814_, 0);
lean_inc(v_a_4815_);
lean_dec_ref(v___y_4814_);
v_a_4810_ = v_a_4815_;
goto v___jp_4809_;
}
else
{
lean_object* v_a_4816_; lean_object* v___x_4818_; uint8_t v_isShared_4819_; uint8_t v_isSharedCheck_4823_; 
v_a_4816_ = lean_ctor_get(v___y_4814_, 0);
v_isSharedCheck_4823_ = !lean_is_exclusive(v___y_4814_);
if (v_isSharedCheck_4823_ == 0)
{
v___x_4818_ = v___y_4814_;
v_isShared_4819_ = v_isSharedCheck_4823_;
goto v_resetjp_4817_;
}
else
{
lean_inc(v_a_4816_);
lean_dec(v___y_4814_);
v___x_4818_ = lean_box(0);
v_isShared_4819_ = v_isSharedCheck_4823_;
goto v_resetjp_4817_;
}
v_resetjp_4817_:
{
lean_object* v___x_4821_; 
if (v_isShared_4819_ == 0)
{
v___x_4821_ = v___x_4818_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_a_4816_);
v___x_4821_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
return v___x_4821_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__9___boxed(lean_object* v___x_4831_, lean_object* v_hasTrace_4832_, lean_object* v_e_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_){
_start:
{
uint8_t v_hasTrace_boxed_4842_; lean_object* v_res_4843_; 
v_hasTrace_boxed_4842_ = lean_unbox(v_hasTrace_4832_);
v_res_4843_ = l_Lean_Elab_Tactic_NormCast_derive___lam__9(v___x_4831_, v_hasTrace_boxed_4842_, v_e_4833_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_);
lean_dec(v___y_4836_);
lean_dec_ref(v___y_4835_);
lean_dec(v___y_4834_);
return v_res_4843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__14(lean_object* v_config_4844_, lean_object* v___x_4845_, lean_object* v_a_4846_, lean_object* v___x_4847_, lean_object* v___f_4848_, lean_object* v___f_4849_, lean_object* v___f_4850_, lean_object* v___f_4851_, lean_object* v___f_4852_, uint8_t v_hasTrace_4853_, lean_object* v_a_4854_, lean_object* v___x_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_){
_start:
{
lean_object* v___x_4861_; 
v___x_4861_ = l_Lean_Meta_Simp_mkContext___redArg(v_config_4844_, v___x_4845_, v_a_4846_, v___y_4856_, v___y_4858_, v___y_4859_);
if (lean_obj_tag(v___x_4861_) == 0)
{
lean_object* v_a_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; size_t v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; 
v_a_4862_ = lean_ctor_get(v___x_4861_, 0);
lean_inc(v_a_4862_);
lean_dec_ref(v___x_4861_);
v___x_4863_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1, &l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1);
lean_inc(v___x_4847_);
v___x_4864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4864_, 0, v___x_4863_);
lean_ctor_set(v___x_4864_, 1, v___x_4847_);
v___x_4865_ = lean_unsigned_to_nat(32u);
v___x_4866_ = lean_mk_empty_array_with_capacity(v___x_4865_);
v___x_4867_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8);
v___x_4868_ = ((size_t)5ULL);
lean_inc(v___x_4847_);
v___x_4869_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4869_, 0, v___x_4867_);
lean_ctor_set(v___x_4869_, 1, v___x_4866_);
lean_ctor_set(v___x_4869_, 2, v___x_4847_);
lean_ctor_set(v___x_4869_, 3, v___x_4847_);
lean_ctor_set_usize(v___x_4869_, 4, v___x_4868_);
v___x_4870_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4870_, 0, v___x_4863_);
lean_ctor_set(v___x_4870_, 1, v___x_4863_);
lean_ctor_set(v___x_4870_, 2, v___x_4863_);
lean_ctor_set(v___x_4870_, 3, v___x_4869_);
v___x_4871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4871_, 0, v___x_4864_);
lean_ctor_set(v___x_4871_, 1, v___x_4870_);
v___x_4872_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4872_, 0, v___f_4848_);
lean_ctor_set(v___x_4872_, 1, v___f_4849_);
lean_ctor_set(v___x_4872_, 2, v___f_4850_);
lean_ctor_set(v___x_4872_, 3, v___f_4851_);
lean_ctor_set(v___x_4872_, 4, v___f_4852_);
lean_ctor_set_uint8(v___x_4872_, sizeof(void*)*5, v_hasTrace_4853_);
lean_inc(v___y_4859_);
lean_inc_ref(v___y_4858_);
lean_inc(v___y_4857_);
lean_inc_ref(v___y_4856_);
v___x_4873_ = l_Lean_Meta_Simp_main(v_a_4854_, v_a_4862_, v___x_4871_, v___x_4872_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_);
if (lean_obj_tag(v___x_4873_) == 0)
{
lean_object* v_a_4874_; lean_object* v_fst_4875_; lean_object* v___x_4876_; 
v_a_4874_ = lean_ctor_get(v___x_4873_, 0);
lean_inc(v_a_4874_);
lean_dec_ref(v___x_4873_);
v_fst_4875_ = lean_ctor_get(v_a_4874_, 0);
lean_inc(v_fst_4875_);
lean_dec(v_a_4874_);
v___x_4876_ = l_Lean_Meta_Simp_Result_mkEqTrans(v___x_4855_, v_fst_4875_, v___y_4856_, v___y_4857_, v___y_4858_, v___y_4859_);
return v___x_4876_;
}
else
{
lean_object* v_a_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4884_; 
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
lean_dec(v___y_4857_);
lean_dec_ref(v___y_4856_);
lean_dec_ref(v___x_4855_);
v_a_4877_ = lean_ctor_get(v___x_4873_, 0);
v_isSharedCheck_4884_ = !lean_is_exclusive(v___x_4873_);
if (v_isSharedCheck_4884_ == 0)
{
v___x_4879_ = v___x_4873_;
v_isShared_4880_ = v_isSharedCheck_4884_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_a_4877_);
lean_dec(v___x_4873_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4884_;
goto v_resetjp_4878_;
}
v_resetjp_4878_:
{
lean_object* v___x_4882_; 
if (v_isShared_4880_ == 0)
{
v___x_4882_ = v___x_4879_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4883_; 
v_reuseFailAlloc_4883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4883_, 0, v_a_4877_);
v___x_4882_ = v_reuseFailAlloc_4883_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
return v___x_4882_;
}
}
}
}
else
{
lean_object* v_a_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4892_; 
lean_dec(v___y_4859_);
lean_dec_ref(v___y_4858_);
lean_dec(v___y_4857_);
lean_dec_ref(v___y_4856_);
lean_dec_ref(v___x_4855_);
lean_dec_ref(v_a_4854_);
lean_dec_ref(v___f_4852_);
lean_dec_ref(v___f_4851_);
lean_dec_ref(v___f_4850_);
lean_dec_ref(v___f_4849_);
lean_dec_ref(v___f_4848_);
lean_dec(v___x_4847_);
v_a_4885_ = lean_ctor_get(v___x_4861_, 0);
v_isSharedCheck_4892_ = !lean_is_exclusive(v___x_4861_);
if (v_isSharedCheck_4892_ == 0)
{
v___x_4887_ = v___x_4861_;
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
else
{
lean_inc(v_a_4885_);
lean_dec(v___x_4861_);
v___x_4887_ = lean_box(0);
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
v_resetjp_4886_:
{
lean_object* v___x_4890_; 
if (v_isShared_4888_ == 0)
{
v___x_4890_ = v___x_4887_;
goto v_reusejp_4889_;
}
else
{
lean_object* v_reuseFailAlloc_4891_; 
v_reuseFailAlloc_4891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4891_, 0, v_a_4885_);
v___x_4890_ = v_reuseFailAlloc_4891_;
goto v_reusejp_4889_;
}
v_reusejp_4889_:
{
return v___x_4890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__14___boxed(lean_object** _args){
lean_object* v_config_4893_ = _args[0];
lean_object* v___x_4894_ = _args[1];
lean_object* v_a_4895_ = _args[2];
lean_object* v___x_4896_ = _args[3];
lean_object* v___f_4897_ = _args[4];
lean_object* v___f_4898_ = _args[5];
lean_object* v___f_4899_ = _args[6];
lean_object* v___f_4900_ = _args[7];
lean_object* v___f_4901_ = _args[8];
lean_object* v_hasTrace_4902_ = _args[9];
lean_object* v_a_4903_ = _args[10];
lean_object* v___x_4904_ = _args[11];
lean_object* v___y_4905_ = _args[12];
lean_object* v___y_4906_ = _args[13];
lean_object* v___y_4907_ = _args[14];
lean_object* v___y_4908_ = _args[15];
lean_object* v___y_4909_ = _args[16];
_start:
{
uint8_t v_hasTrace_boxed_4910_; lean_object* v_res_4911_; 
v_hasTrace_boxed_4910_ = lean_unbox(v_hasTrace_4902_);
v_res_4911_ = l_Lean_Elab_Tactic_NormCast_derive___lam__14(v_config_4893_, v___x_4894_, v_a_4895_, v___x_4896_, v___f_4897_, v___f_4898_, v___f_4899_, v___f_4900_, v___f_4901_, v_hasTrace_boxed_4910_, v_a_4903_, v___x_4904_, v___y_4905_, v___y_4906_, v___y_4907_, v___y_4908_);
return v_res_4911_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__15(lean_object* v_up_4912_, lean_object* v_config_4913_, lean_object* v___x_4914_, lean_object* v_a_4915_, lean_object* v_a_4916_, lean_object* v___x_4917_, lean_object* v___f_4918_, lean_object* v___f_4919_, lean_object* v___f_4920_, lean_object* v___f_4921_, uint8_t v_hasTrace_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_){
_start:
{
lean_object* v___x_4928_; 
v___x_4928_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_up_4912_, v___y_4926_);
if (lean_obj_tag(v___x_4928_) == 0)
{
lean_object* v_a_4929_; lean_object* v___x_4930_; 
v_a_4929_ = lean_ctor_get(v___x_4928_, 0);
lean_inc(v_a_4929_);
lean_dec_ref(v___x_4928_);
v___x_4930_ = l_Lean_Meta_Simp_mkContext___redArg(v_config_4913_, v___x_4914_, v_a_4915_, v___y_4923_, v___y_4925_, v___y_4926_);
if (lean_obj_tag(v___x_4930_) == 0)
{
lean_object* v_a_4931_; lean_object* v_expr_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; size_t v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; 
v_a_4931_ = lean_ctor_get(v___x_4930_, 0);
lean_inc(v_a_4931_);
lean_dec_ref(v___x_4930_);
v_expr_4932_ = lean_ctor_get(v_a_4916_, 0);
v___x_4933_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_upwardAndElim___boxed), 10, 1);
lean_closure_set(v___x_4933_, 0, v_a_4929_);
v___x_4934_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1, &l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1);
lean_inc(v___x_4917_);
v___x_4935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4935_, 0, v___x_4934_);
lean_ctor_set(v___x_4935_, 1, v___x_4917_);
v___x_4936_ = lean_unsigned_to_nat(32u);
v___x_4937_ = lean_mk_empty_array_with_capacity(v___x_4936_);
v___x_4938_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8);
v___x_4939_ = ((size_t)5ULL);
lean_inc(v___x_4917_);
v___x_4940_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4940_, 0, v___x_4938_);
lean_ctor_set(v___x_4940_, 1, v___x_4937_);
lean_ctor_set(v___x_4940_, 2, v___x_4917_);
lean_ctor_set(v___x_4940_, 3, v___x_4917_);
lean_ctor_set_usize(v___x_4940_, 4, v___x_4939_);
v___x_4941_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4941_, 0, v___x_4934_);
lean_ctor_set(v___x_4941_, 1, v___x_4934_);
lean_ctor_set(v___x_4941_, 2, v___x_4934_);
lean_ctor_set(v___x_4941_, 3, v___x_4940_);
v___x_4942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4942_, 0, v___x_4935_);
lean_ctor_set(v___x_4942_, 1, v___x_4941_);
v___x_4943_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4943_, 0, v___f_4918_);
lean_ctor_set(v___x_4943_, 1, v___x_4933_);
lean_ctor_set(v___x_4943_, 2, v___f_4919_);
lean_ctor_set(v___x_4943_, 3, v___f_4920_);
lean_ctor_set(v___x_4943_, 4, v___f_4921_);
lean_ctor_set_uint8(v___x_4943_, sizeof(void*)*5, v_hasTrace_4922_);
lean_inc(v___y_4926_);
lean_inc_ref(v___y_4925_);
lean_inc(v___y_4924_);
lean_inc_ref(v___y_4923_);
lean_inc_ref(v_expr_4932_);
v___x_4944_ = l_Lean_Meta_Simp_main(v_expr_4932_, v_a_4931_, v___x_4942_, v___x_4943_, v___y_4923_, v___y_4924_, v___y_4925_, v___y_4926_);
if (lean_obj_tag(v___x_4944_) == 0)
{
lean_object* v_a_4945_; lean_object* v_fst_4946_; lean_object* v___x_4947_; 
v_a_4945_ = lean_ctor_get(v___x_4944_, 0);
lean_inc(v_a_4945_);
lean_dec_ref(v___x_4944_);
v_fst_4946_ = lean_ctor_get(v_a_4945_, 0);
lean_inc(v_fst_4946_);
lean_dec(v_a_4945_);
v___x_4947_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_4916_, v_fst_4946_, v___y_4923_, v___y_4924_, v___y_4925_, v___y_4926_);
return v___x_4947_;
}
else
{
lean_object* v_a_4948_; lean_object* v___x_4950_; uint8_t v_isShared_4951_; uint8_t v_isSharedCheck_4955_; 
lean_dec(v___y_4926_);
lean_dec_ref(v___y_4925_);
lean_dec(v___y_4924_);
lean_dec_ref(v___y_4923_);
lean_dec_ref(v_a_4916_);
v_a_4948_ = lean_ctor_get(v___x_4944_, 0);
v_isSharedCheck_4955_ = !lean_is_exclusive(v___x_4944_);
if (v_isSharedCheck_4955_ == 0)
{
v___x_4950_ = v___x_4944_;
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
else
{
lean_inc(v_a_4948_);
lean_dec(v___x_4944_);
v___x_4950_ = lean_box(0);
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
v_resetjp_4949_:
{
lean_object* v___x_4953_; 
if (v_isShared_4951_ == 0)
{
v___x_4953_ = v___x_4950_;
goto v_reusejp_4952_;
}
else
{
lean_object* v_reuseFailAlloc_4954_; 
v_reuseFailAlloc_4954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4954_, 0, v_a_4948_);
v___x_4953_ = v_reuseFailAlloc_4954_;
goto v_reusejp_4952_;
}
v_reusejp_4952_:
{
return v___x_4953_;
}
}
}
}
else
{
lean_object* v_a_4956_; lean_object* v___x_4958_; uint8_t v_isShared_4959_; uint8_t v_isSharedCheck_4963_; 
lean_dec(v_a_4929_);
lean_dec(v___y_4926_);
lean_dec_ref(v___y_4925_);
lean_dec(v___y_4924_);
lean_dec_ref(v___y_4923_);
lean_dec_ref(v___f_4921_);
lean_dec_ref(v___f_4920_);
lean_dec_ref(v___f_4919_);
lean_dec_ref(v___f_4918_);
lean_dec(v___x_4917_);
lean_dec_ref(v_a_4916_);
v_a_4956_ = lean_ctor_get(v___x_4930_, 0);
v_isSharedCheck_4963_ = !lean_is_exclusive(v___x_4930_);
if (v_isSharedCheck_4963_ == 0)
{
v___x_4958_ = v___x_4930_;
v_isShared_4959_ = v_isSharedCheck_4963_;
goto v_resetjp_4957_;
}
else
{
lean_inc(v_a_4956_);
lean_dec(v___x_4930_);
v___x_4958_ = lean_box(0);
v_isShared_4959_ = v_isSharedCheck_4963_;
goto v_resetjp_4957_;
}
v_resetjp_4957_:
{
lean_object* v___x_4961_; 
if (v_isShared_4959_ == 0)
{
v___x_4961_ = v___x_4958_;
goto v_reusejp_4960_;
}
else
{
lean_object* v_reuseFailAlloc_4962_; 
v_reuseFailAlloc_4962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4962_, 0, v_a_4956_);
v___x_4961_ = v_reuseFailAlloc_4962_;
goto v_reusejp_4960_;
}
v_reusejp_4960_:
{
return v___x_4961_;
}
}
}
}
else
{
lean_object* v_a_4964_; lean_object* v___x_4966_; uint8_t v_isShared_4967_; uint8_t v_isSharedCheck_4971_; 
lean_dec(v___y_4926_);
lean_dec_ref(v___y_4925_);
lean_dec(v___y_4924_);
lean_dec_ref(v___y_4923_);
lean_dec_ref(v___f_4921_);
lean_dec_ref(v___f_4920_);
lean_dec_ref(v___f_4919_);
lean_dec_ref(v___f_4918_);
lean_dec(v___x_4917_);
lean_dec_ref(v_a_4916_);
lean_dec_ref(v_a_4915_);
lean_dec_ref(v___x_4914_);
lean_dec_ref(v_config_4913_);
v_a_4964_ = lean_ctor_get(v___x_4928_, 0);
v_isSharedCheck_4971_ = !lean_is_exclusive(v___x_4928_);
if (v_isSharedCheck_4971_ == 0)
{
v___x_4966_ = v___x_4928_;
v_isShared_4967_ = v_isSharedCheck_4971_;
goto v_resetjp_4965_;
}
else
{
lean_inc(v_a_4964_);
lean_dec(v___x_4928_);
v___x_4966_ = lean_box(0);
v_isShared_4967_ = v_isSharedCheck_4971_;
goto v_resetjp_4965_;
}
v_resetjp_4965_:
{
lean_object* v___x_4969_; 
if (v_isShared_4967_ == 0)
{
v___x_4969_ = v___x_4966_;
goto v_reusejp_4968_;
}
else
{
lean_object* v_reuseFailAlloc_4970_; 
v_reuseFailAlloc_4970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4970_, 0, v_a_4964_);
v___x_4969_ = v_reuseFailAlloc_4970_;
goto v_reusejp_4968_;
}
v_reusejp_4968_:
{
return v___x_4969_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__15___boxed(lean_object* v_up_4972_, lean_object* v_config_4973_, lean_object* v___x_4974_, lean_object* v_a_4975_, lean_object* v_a_4976_, lean_object* v___x_4977_, lean_object* v___f_4978_, lean_object* v___f_4979_, lean_object* v___f_4980_, lean_object* v___f_4981_, lean_object* v_hasTrace_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_){
_start:
{
uint8_t v_hasTrace_boxed_4988_; lean_object* v_res_4989_; 
v_hasTrace_boxed_4988_ = lean_unbox(v_hasTrace_4982_);
v_res_4989_ = l_Lean_Elab_Tactic_NormCast_derive___lam__15(v_up_4972_, v_config_4973_, v___x_4974_, v_a_4975_, v_a_4976_, v___x_4977_, v___f_4978_, v___f_4979_, v___f_4980_, v___f_4981_, v_hasTrace_boxed_4988_, v___y_4983_, v___y_4984_, v___y_4985_, v___y_4986_);
lean_dec_ref(v_up_4972_);
return v_res_4989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__16(lean_object* v___x_4990_, uint8_t v___x_4991_, lean_object* v___x_4992_, lean_object* v___x_4993_, lean_object* v_phase_4994_, lean_object* v_k_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_){
_start:
{
lean_object* v_options_5001_; uint8_t v_hasTrace_5002_; 
v_options_5001_ = lean_ctor_get(v___y_4998_, 2);
v_hasTrace_5002_ = lean_ctor_get_uint8(v_options_5001_, sizeof(void*)*1);
if (v_hasTrace_5002_ == 0)
{
lean_object* v___x_5003_; 
lean_dec_ref(v_phase_4994_);
lean_dec_ref(v___x_4992_);
lean_dec(v___x_4990_);
v___x_5003_ = lean_apply_5(v_k_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, lean_box(0));
return v___x_5003_;
}
else
{
lean_object* v___x_5004_; lean_object* v_a_5005_; lean_object* v___f_5006_; lean_object* v___y_5008_; lean_object* v___y_5009_; lean_object* v_a_5010_; lean_object* v___y_5024_; lean_object* v___y_5025_; lean_object* v_a_5026_; uint8_t v___x_5076_; 
lean_inc(v___x_4990_);
v___x_5004_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___x_4990_, v___y_4998_);
v_a_5005_ = lean_ctor_get(v___x_5004_, 0);
lean_inc(v_a_5005_);
lean_dec_ref(v___x_5004_);
v___f_5006_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__4___boxed), 7, 1);
lean_closure_set(v___f_5006_, 0, v_phase_4994_);
v___x_5076_ = lean_unbox(v_a_5005_);
if (v___x_5076_ == 0)
{
lean_object* v___x_5077_; uint8_t v___x_5078_; 
v___x_5077_ = l_Lean_trace_profiler;
v___x_5078_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_5001_, v___x_5077_);
if (v___x_5078_ == 0)
{
lean_object* v___x_5079_; 
lean_dec_ref(v___f_5006_);
lean_dec(v_a_5005_);
lean_dec_ref(v___x_4992_);
lean_dec(v___x_4990_);
v___x_5079_ = lean_apply_5(v_k_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, lean_box(0));
return v___x_5079_;
}
else
{
lean_inc_ref(v_options_5001_);
goto v___jp_5036_;
}
}
else
{
lean_inc_ref(v_options_5001_);
goto v___jp_5036_;
}
v___jp_5007_:
{
lean_object* v___x_5011_; double v___x_5012_; double v___x_5013_; double v___x_5014_; double v___x_5015_; double v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; lean_object* v___x_5020_; uint8_t v___x_5021_; lean_object* v___x_5022_; 
v___x_5011_ = lean_io_mono_nanos_now();
v___x_5012_ = lean_float_of_nat(v___y_5008_);
v___x_5013_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1);
v___x_5014_ = lean_float_div(v___x_5012_, v___x_5013_);
v___x_5015_ = lean_float_of_nat(v___x_5011_);
v___x_5016_ = lean_float_div(v___x_5015_, v___x_5013_);
v___x_5017_ = lean_box_float(v___x_5014_);
v___x_5018_ = lean_box_float(v___x_5016_);
v___x_5019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5019_, 0, v___x_5017_);
lean_ctor_set(v___x_5019_, 1, v___x_5018_);
v___x_5020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5020_, 0, v_a_5010_);
lean_ctor_set(v___x_5020_, 1, v___x_5019_);
v___x_5021_ = lean_unbox(v_a_5005_);
lean_dec(v_a_5005_);
v___x_5022_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4990_, v___x_4991_, v___x_4992_, v_options_5001_, v___x_5021_, v___y_5009_, v___f_5006_, v___x_5020_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_);
lean_dec_ref(v_options_5001_);
return v___x_5022_;
}
v___jp_5023_:
{
lean_object* v___x_5027_; double v___x_5028_; double v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; uint8_t v___x_5034_; lean_object* v___x_5035_; 
v___x_5027_ = lean_io_get_num_heartbeats();
v___x_5028_ = lean_float_of_nat(v___y_5024_);
v___x_5029_ = lean_float_of_nat(v___x_5027_);
v___x_5030_ = lean_box_float(v___x_5028_);
v___x_5031_ = lean_box_float(v___x_5029_);
v___x_5032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5032_, 0, v___x_5030_);
lean_ctor_set(v___x_5032_, 1, v___x_5031_);
v___x_5033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5033_, 0, v_a_5026_);
lean_ctor_set(v___x_5033_, 1, v___x_5032_);
v___x_5034_ = lean_unbox(v_a_5005_);
lean_dec(v_a_5005_);
v___x_5035_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4990_, v___x_4991_, v___x_4992_, v_options_5001_, v___x_5034_, v___y_5025_, v___f_5006_, v___x_5033_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_);
lean_dec_ref(v_options_5001_);
return v___x_5035_;
}
v___jp_5036_:
{
lean_object* v___x_5037_; lean_object* v_a_5038_; uint8_t v___x_5039_; 
v___x_5037_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg(v___y_4999_);
v_a_5038_ = lean_ctor_get(v___x_5037_, 0);
lean_inc(v_a_5038_);
lean_dec_ref(v___x_5037_);
v___x_5039_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_5001_, v___x_4993_);
if (v___x_5039_ == 0)
{
lean_object* v___x_5040_; lean_object* v___x_5041_; 
v___x_5040_ = lean_io_mono_nanos_now();
lean_inc(v___y_4999_);
lean_inc_ref(v___y_4998_);
lean_inc(v___y_4997_);
lean_inc_ref(v___y_4996_);
v___x_5041_ = lean_apply_5(v_k_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, lean_box(0));
if (lean_obj_tag(v___x_5041_) == 0)
{
lean_object* v_a_5042_; lean_object* v___x_5044_; uint8_t v_isShared_5045_; uint8_t v_isSharedCheck_5049_; 
v_a_5042_ = lean_ctor_get(v___x_5041_, 0);
v_isSharedCheck_5049_ = !lean_is_exclusive(v___x_5041_);
if (v_isSharedCheck_5049_ == 0)
{
v___x_5044_ = v___x_5041_;
v_isShared_5045_ = v_isSharedCheck_5049_;
goto v_resetjp_5043_;
}
else
{
lean_inc(v_a_5042_);
lean_dec(v___x_5041_);
v___x_5044_ = lean_box(0);
v_isShared_5045_ = v_isSharedCheck_5049_;
goto v_resetjp_5043_;
}
v_resetjp_5043_:
{
lean_object* v___x_5047_; 
if (v_isShared_5045_ == 0)
{
lean_ctor_set_tag(v___x_5044_, 1);
v___x_5047_ = v___x_5044_;
goto v_reusejp_5046_;
}
else
{
lean_object* v_reuseFailAlloc_5048_; 
v_reuseFailAlloc_5048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5048_, 0, v_a_5042_);
v___x_5047_ = v_reuseFailAlloc_5048_;
goto v_reusejp_5046_;
}
v_reusejp_5046_:
{
v___y_5008_ = v___x_5040_;
v___y_5009_ = v_a_5038_;
v_a_5010_ = v___x_5047_;
goto v___jp_5007_;
}
}
}
else
{
lean_object* v_a_5050_; lean_object* v___x_5052_; uint8_t v_isShared_5053_; uint8_t v_isSharedCheck_5057_; 
v_a_5050_ = lean_ctor_get(v___x_5041_, 0);
v_isSharedCheck_5057_ = !lean_is_exclusive(v___x_5041_);
if (v_isSharedCheck_5057_ == 0)
{
v___x_5052_ = v___x_5041_;
v_isShared_5053_ = v_isSharedCheck_5057_;
goto v_resetjp_5051_;
}
else
{
lean_inc(v_a_5050_);
lean_dec(v___x_5041_);
v___x_5052_ = lean_box(0);
v_isShared_5053_ = v_isSharedCheck_5057_;
goto v_resetjp_5051_;
}
v_resetjp_5051_:
{
lean_object* v___x_5055_; 
if (v_isShared_5053_ == 0)
{
lean_ctor_set_tag(v___x_5052_, 0);
v___x_5055_ = v___x_5052_;
goto v_reusejp_5054_;
}
else
{
lean_object* v_reuseFailAlloc_5056_; 
v_reuseFailAlloc_5056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5056_, 0, v_a_5050_);
v___x_5055_ = v_reuseFailAlloc_5056_;
goto v_reusejp_5054_;
}
v_reusejp_5054_:
{
v___y_5008_ = v___x_5040_;
v___y_5009_ = v_a_5038_;
v_a_5010_ = v___x_5055_;
goto v___jp_5007_;
}
}
}
}
else
{
lean_object* v___x_5058_; lean_object* v___x_5059_; 
v___x_5058_ = lean_io_get_num_heartbeats();
lean_inc(v___y_4999_);
lean_inc_ref(v___y_4998_);
lean_inc(v___y_4997_);
lean_inc_ref(v___y_4996_);
v___x_5059_ = lean_apply_5(v_k_4995_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, lean_box(0));
if (lean_obj_tag(v___x_5059_) == 0)
{
lean_object* v_a_5060_; lean_object* v___x_5062_; uint8_t v_isShared_5063_; uint8_t v_isSharedCheck_5067_; 
v_a_5060_ = lean_ctor_get(v___x_5059_, 0);
v_isSharedCheck_5067_ = !lean_is_exclusive(v___x_5059_);
if (v_isSharedCheck_5067_ == 0)
{
v___x_5062_ = v___x_5059_;
v_isShared_5063_ = v_isSharedCheck_5067_;
goto v_resetjp_5061_;
}
else
{
lean_inc(v_a_5060_);
lean_dec(v___x_5059_);
v___x_5062_ = lean_box(0);
v_isShared_5063_ = v_isSharedCheck_5067_;
goto v_resetjp_5061_;
}
v_resetjp_5061_:
{
lean_object* v___x_5065_; 
if (v_isShared_5063_ == 0)
{
lean_ctor_set_tag(v___x_5062_, 1);
v___x_5065_ = v___x_5062_;
goto v_reusejp_5064_;
}
else
{
lean_object* v_reuseFailAlloc_5066_; 
v_reuseFailAlloc_5066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5066_, 0, v_a_5060_);
v___x_5065_ = v_reuseFailAlloc_5066_;
goto v_reusejp_5064_;
}
v_reusejp_5064_:
{
v___y_5024_ = v___x_5058_;
v___y_5025_ = v_a_5038_;
v_a_5026_ = v___x_5065_;
goto v___jp_5023_;
}
}
}
else
{
lean_object* v_a_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5075_; 
v_a_5068_ = lean_ctor_get(v___x_5059_, 0);
v_isSharedCheck_5075_ = !lean_is_exclusive(v___x_5059_);
if (v_isSharedCheck_5075_ == 0)
{
v___x_5070_ = v___x_5059_;
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
else
{
lean_inc(v_a_5068_);
lean_dec(v___x_5059_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
lean_object* v___x_5073_; 
if (v_isShared_5071_ == 0)
{
lean_ctor_set_tag(v___x_5070_, 0);
v___x_5073_ = v___x_5070_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5074_; 
v_reuseFailAlloc_5074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5074_, 0, v_a_5068_);
v___x_5073_ = v_reuseFailAlloc_5074_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
v___y_5024_ = v___x_5058_;
v___y_5025_ = v_a_5038_;
v_a_5026_ = v___x_5073_;
goto v___jp_5023_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__16___boxed(lean_object* v___x_5080_, lean_object* v___x_5081_, lean_object* v___x_5082_, lean_object* v___x_5083_, lean_object* v_phase_5084_, lean_object* v_k_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_, lean_object* v___y_5090_){
_start:
{
uint8_t v___x_32356__boxed_5091_; lean_object* v_res_5092_; 
v___x_32356__boxed_5091_ = lean_unbox(v___x_5081_);
v_res_5092_ = l_Lean_Elab_Tactic_NormCast_derive___lam__16(v___x_5080_, v___x_32356__boxed_5091_, v___x_5082_, v___x_5083_, v_phase_5084_, v_k_5085_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_);
lean_dec_ref(v___x_5083_);
return v_res_5092_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__27(lean_object* v___x_5093_, uint8_t v_hasTrace_5094_, lean_object* v_phase_5095_, lean_object* v_k_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_, lean_object* v___y_5099_, lean_object* v___y_5100_){
_start:
{
lean_object* v_options_5102_; uint8_t v_hasTrace_5103_; 
v_options_5102_ = lean_ctor_get(v___y_5099_, 2);
v_hasTrace_5103_ = lean_ctor_get_uint8(v_options_5102_, sizeof(void*)*1);
if (v_hasTrace_5103_ == 0)
{
lean_object* v___x_5104_; 
lean_dec_ref(v_phase_5095_);
lean_dec(v___x_5093_);
v___x_5104_ = lean_apply_5(v_k_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_, lean_box(0));
return v___x_5104_;
}
else
{
lean_object* v___x_5105_; lean_object* v_a_5106_; lean_object* v___f_5107_; lean_object* v___x_5108_; lean_object* v___y_5110_; lean_object* v___y_5111_; lean_object* v_a_5112_; lean_object* v___y_5126_; lean_object* v___y_5127_; lean_object* v_a_5128_; uint8_t v___x_5179_; 
lean_inc(v___x_5093_);
v___x_5105_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___x_5093_, v___y_5099_);
v_a_5106_ = lean_ctor_get(v___x_5105_, 0);
lean_inc(v_a_5106_);
lean_dec_ref(v___x_5105_);
v___f_5107_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__4___boxed), 7, 1);
lean_closure_set(v___f_5107_, 0, v_phase_5095_);
v___x_5108_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_5179_ = lean_unbox(v_a_5106_);
if (v___x_5179_ == 0)
{
lean_object* v___x_5180_; uint8_t v___x_5181_; 
v___x_5180_ = l_Lean_trace_profiler;
v___x_5181_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_5102_, v___x_5180_);
if (v___x_5181_ == 0)
{
lean_object* v___x_5182_; 
lean_dec_ref(v___f_5107_);
lean_dec(v_a_5106_);
lean_dec(v___x_5093_);
v___x_5182_ = lean_apply_5(v_k_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_, lean_box(0));
return v___x_5182_;
}
else
{
lean_inc_ref(v_options_5102_);
goto v___jp_5138_;
}
}
else
{
lean_inc_ref(v_options_5102_);
goto v___jp_5138_;
}
v___jp_5109_:
{
lean_object* v___x_5113_; double v___x_5114_; double v___x_5115_; double v___x_5116_; double v___x_5117_; double v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; uint8_t v___x_5123_; lean_object* v___x_5124_; 
v___x_5113_ = lean_io_mono_nanos_now();
v___x_5114_ = lean_float_of_nat(v___y_5111_);
v___x_5115_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1);
v___x_5116_ = lean_float_div(v___x_5114_, v___x_5115_);
v___x_5117_ = lean_float_of_nat(v___x_5113_);
v___x_5118_ = lean_float_div(v___x_5117_, v___x_5115_);
v___x_5119_ = lean_box_float(v___x_5116_);
v___x_5120_ = lean_box_float(v___x_5118_);
v___x_5121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5121_, 0, v___x_5119_);
lean_ctor_set(v___x_5121_, 1, v___x_5120_);
v___x_5122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5122_, 0, v_a_5112_);
lean_ctor_set(v___x_5122_, 1, v___x_5121_);
v___x_5123_ = lean_unbox(v_a_5106_);
lean_dec(v_a_5106_);
v___x_5124_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_5093_, v_hasTrace_5094_, v___x_5108_, v_options_5102_, v___x_5123_, v___y_5110_, v___f_5107_, v___x_5122_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_);
lean_dec_ref(v_options_5102_);
return v___x_5124_;
}
v___jp_5125_:
{
lean_object* v___x_5129_; double v___x_5130_; double v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; uint8_t v___x_5136_; lean_object* v___x_5137_; 
v___x_5129_ = lean_io_get_num_heartbeats();
v___x_5130_ = lean_float_of_nat(v___y_5126_);
v___x_5131_ = lean_float_of_nat(v___x_5129_);
v___x_5132_ = lean_box_float(v___x_5130_);
v___x_5133_ = lean_box_float(v___x_5131_);
v___x_5134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5134_, 0, v___x_5132_);
lean_ctor_set(v___x_5134_, 1, v___x_5133_);
v___x_5135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5135_, 0, v_a_5128_);
lean_ctor_set(v___x_5135_, 1, v___x_5134_);
v___x_5136_ = lean_unbox(v_a_5106_);
lean_dec(v_a_5106_);
v___x_5137_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_5093_, v_hasTrace_5094_, v___x_5108_, v_options_5102_, v___x_5136_, v___y_5127_, v___f_5107_, v___x_5135_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_);
lean_dec_ref(v_options_5102_);
return v___x_5137_;
}
v___jp_5138_:
{
lean_object* v___x_5139_; lean_object* v_a_5140_; lean_object* v___x_5141_; uint8_t v___x_5142_; 
v___x_5139_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg(v___y_5100_);
v_a_5140_ = lean_ctor_get(v___x_5139_, 0);
lean_inc(v_a_5140_);
lean_dec_ref(v___x_5139_);
v___x_5141_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5142_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_5102_, v___x_5141_);
if (v___x_5142_ == 0)
{
lean_object* v___x_5143_; lean_object* v___x_5144_; 
v___x_5143_ = lean_io_mono_nanos_now();
lean_inc(v___y_5100_);
lean_inc_ref(v___y_5099_);
lean_inc(v___y_5098_);
lean_inc_ref(v___y_5097_);
v___x_5144_ = lean_apply_5(v_k_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_, lean_box(0));
if (lean_obj_tag(v___x_5144_) == 0)
{
lean_object* v_a_5145_; lean_object* v___x_5147_; uint8_t v_isShared_5148_; uint8_t v_isSharedCheck_5152_; 
v_a_5145_ = lean_ctor_get(v___x_5144_, 0);
v_isSharedCheck_5152_ = !lean_is_exclusive(v___x_5144_);
if (v_isSharedCheck_5152_ == 0)
{
v___x_5147_ = v___x_5144_;
v_isShared_5148_ = v_isSharedCheck_5152_;
goto v_resetjp_5146_;
}
else
{
lean_inc(v_a_5145_);
lean_dec(v___x_5144_);
v___x_5147_ = lean_box(0);
v_isShared_5148_ = v_isSharedCheck_5152_;
goto v_resetjp_5146_;
}
v_resetjp_5146_:
{
lean_object* v___x_5150_; 
if (v_isShared_5148_ == 0)
{
lean_ctor_set_tag(v___x_5147_, 1);
v___x_5150_ = v___x_5147_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5151_; 
v_reuseFailAlloc_5151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5151_, 0, v_a_5145_);
v___x_5150_ = v_reuseFailAlloc_5151_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
v___y_5110_ = v_a_5140_;
v___y_5111_ = v___x_5143_;
v_a_5112_ = v___x_5150_;
goto v___jp_5109_;
}
}
}
else
{
lean_object* v_a_5153_; lean_object* v___x_5155_; uint8_t v_isShared_5156_; uint8_t v_isSharedCheck_5160_; 
v_a_5153_ = lean_ctor_get(v___x_5144_, 0);
v_isSharedCheck_5160_ = !lean_is_exclusive(v___x_5144_);
if (v_isSharedCheck_5160_ == 0)
{
v___x_5155_ = v___x_5144_;
v_isShared_5156_ = v_isSharedCheck_5160_;
goto v_resetjp_5154_;
}
else
{
lean_inc(v_a_5153_);
lean_dec(v___x_5144_);
v___x_5155_ = lean_box(0);
v_isShared_5156_ = v_isSharedCheck_5160_;
goto v_resetjp_5154_;
}
v_resetjp_5154_:
{
lean_object* v___x_5158_; 
if (v_isShared_5156_ == 0)
{
lean_ctor_set_tag(v___x_5155_, 0);
v___x_5158_ = v___x_5155_;
goto v_reusejp_5157_;
}
else
{
lean_object* v_reuseFailAlloc_5159_; 
v_reuseFailAlloc_5159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5159_, 0, v_a_5153_);
v___x_5158_ = v_reuseFailAlloc_5159_;
goto v_reusejp_5157_;
}
v_reusejp_5157_:
{
v___y_5110_ = v_a_5140_;
v___y_5111_ = v___x_5143_;
v_a_5112_ = v___x_5158_;
goto v___jp_5109_;
}
}
}
}
else
{
lean_object* v___x_5161_; lean_object* v___x_5162_; 
v___x_5161_ = lean_io_get_num_heartbeats();
lean_inc(v___y_5100_);
lean_inc_ref(v___y_5099_);
lean_inc(v___y_5098_);
lean_inc_ref(v___y_5097_);
v___x_5162_ = lean_apply_5(v_k_5096_, v___y_5097_, v___y_5098_, v___y_5099_, v___y_5100_, lean_box(0));
if (lean_obj_tag(v___x_5162_) == 0)
{
lean_object* v_a_5163_; lean_object* v___x_5165_; uint8_t v_isShared_5166_; uint8_t v_isSharedCheck_5170_; 
v_a_5163_ = lean_ctor_get(v___x_5162_, 0);
v_isSharedCheck_5170_ = !lean_is_exclusive(v___x_5162_);
if (v_isSharedCheck_5170_ == 0)
{
v___x_5165_ = v___x_5162_;
v_isShared_5166_ = v_isSharedCheck_5170_;
goto v_resetjp_5164_;
}
else
{
lean_inc(v_a_5163_);
lean_dec(v___x_5162_);
v___x_5165_ = lean_box(0);
v_isShared_5166_ = v_isSharedCheck_5170_;
goto v_resetjp_5164_;
}
v_resetjp_5164_:
{
lean_object* v___x_5168_; 
if (v_isShared_5166_ == 0)
{
lean_ctor_set_tag(v___x_5165_, 1);
v___x_5168_ = v___x_5165_;
goto v_reusejp_5167_;
}
else
{
lean_object* v_reuseFailAlloc_5169_; 
v_reuseFailAlloc_5169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5169_, 0, v_a_5163_);
v___x_5168_ = v_reuseFailAlloc_5169_;
goto v_reusejp_5167_;
}
v_reusejp_5167_:
{
v___y_5126_ = v___x_5161_;
v___y_5127_ = v_a_5140_;
v_a_5128_ = v___x_5168_;
goto v___jp_5125_;
}
}
}
else
{
lean_object* v_a_5171_; lean_object* v___x_5173_; uint8_t v_isShared_5174_; uint8_t v_isSharedCheck_5178_; 
v_a_5171_ = lean_ctor_get(v___x_5162_, 0);
v_isSharedCheck_5178_ = !lean_is_exclusive(v___x_5162_);
if (v_isSharedCheck_5178_ == 0)
{
v___x_5173_ = v___x_5162_;
v_isShared_5174_ = v_isSharedCheck_5178_;
goto v_resetjp_5172_;
}
else
{
lean_inc(v_a_5171_);
lean_dec(v___x_5162_);
v___x_5173_ = lean_box(0);
v_isShared_5174_ = v_isSharedCheck_5178_;
goto v_resetjp_5172_;
}
v_resetjp_5172_:
{
lean_object* v___x_5176_; 
if (v_isShared_5174_ == 0)
{
lean_ctor_set_tag(v___x_5173_, 0);
v___x_5176_ = v___x_5173_;
goto v_reusejp_5175_;
}
else
{
lean_object* v_reuseFailAlloc_5177_; 
v_reuseFailAlloc_5177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5177_, 0, v_a_5171_);
v___x_5176_ = v_reuseFailAlloc_5177_;
goto v_reusejp_5175_;
}
v_reusejp_5175_:
{
v___y_5126_ = v___x_5161_;
v___y_5127_ = v_a_5140_;
v_a_5128_ = v___x_5176_;
goto v___jp_5125_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__27___boxed(lean_object* v___x_5183_, lean_object* v_hasTrace_5184_, lean_object* v_phase_5185_, lean_object* v_k_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_, lean_object* v___y_5190_, lean_object* v___y_5191_){
_start:
{
uint8_t v_hasTrace_boxed_5192_; lean_object* v_res_5193_; 
v_hasTrace_boxed_5192_ = lean_unbox(v_hasTrace_5184_);
v_res_5193_ = l_Lean_Elab_Tactic_NormCast_derive___lam__27(v___x_5183_, v_hasTrace_boxed_5192_, v_phase_5185_, v_k_5186_, v___y_5187_, v___y_5188_, v___y_5189_, v___y_5190_);
return v_res_5193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive(lean_object* v_e_5212_, lean_object* v_config_5213_, lean_object* v_a_5214_, lean_object* v_a_5215_, lean_object* v_a_5216_, lean_object* v_a_5217_){
_start:
{
lean_object* v_options_5219_; uint8_t v_hasTrace_5220_; lean_object* v___x_5221_; 
v_options_5219_ = lean_ctor_get(v_a_5216_, 2);
v_hasTrace_5220_ = lean_ctor_get_uint8(v_options_5219_, sizeof(void*)*1);
v___x_5221_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__2_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_));
if (v_hasTrace_5220_ == 0)
{
lean_object* v___x_5222_; lean_object* v_a_5223_; lean_object* v___x_5224_; 
v___x_5222_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_e_5212_, v_a_5215_);
v_a_5223_ = lean_ctor_get(v___x_5222_, 0);
lean_inc(v_a_5223_);
lean_dec_ref(v___x_5222_);
v___x_5224_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_5217_);
if (lean_obj_tag(v___x_5224_) == 0)
{
lean_object* v_a_5225_; lean_object* v___f_5226_; lean_object* v___f_5227_; lean_object* v___x_5228_; lean_object* v___f_5229_; lean_object* v___f_5230_; uint8_t v___x_5231_; lean_object* v___f_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___f_5238_; lean_object* v___x_5239_; 
v_a_5225_ = lean_ctor_get(v___x_5224_, 0);
lean_inc(v_a_5225_);
lean_dec_ref(v___x_5224_);
v___f_5226_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__0));
v___f_5227_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__1));
v___x_5228_ = lean_box(0);
v___f_5229_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__2));
v___f_5230_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__3));
v___x_5231_ = 1;
v___f_5232_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__4));
lean_inc(v_a_5223_);
v___x_5233_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5233_, 0, v_a_5223_);
lean_ctor_set(v___x_5233_, 1, v___x_5228_);
lean_ctor_set_uint8(v___x_5233_, sizeof(void*)*2, v___x_5231_);
v___x_5234_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__5));
v___x_5235_ = lean_unsigned_to_nat(0u);
v___x_5236_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__6));
v___x_5237_ = lean_box(v___x_5231_);
lean_inc(v_a_5225_);
lean_inc_ref(v_config_5213_);
v___f_5238_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__7___boxed), 17, 12);
lean_closure_set(v___f_5238_, 0, v_config_5213_);
lean_closure_set(v___f_5238_, 1, v___x_5236_);
lean_closure_set(v___f_5238_, 2, v_a_5225_);
lean_closure_set(v___f_5238_, 3, v___x_5235_);
lean_closure_set(v___f_5238_, 4, v___f_5226_);
lean_closure_set(v___f_5238_, 5, v___f_5232_);
lean_closure_set(v___f_5238_, 6, v___f_5229_);
lean_closure_set(v___f_5238_, 7, v___f_5227_);
lean_closure_set(v___f_5238_, 8, v___f_5230_);
lean_closure_set(v___f_5238_, 9, v___x_5237_);
lean_closure_set(v___f_5238_, 10, v_a_5223_);
lean_closure_set(v___f_5238_, 11, v___x_5233_);
lean_inc(v_a_5217_);
lean_inc_ref(v_a_5216_);
lean_inc(v_a_5215_);
lean_inc_ref(v_a_5214_);
v___x_5239_ = l_Lean_Elab_Tactic_NormCast_derive___lam__5(v___x_5221_, v___x_5231_, v___x_5234_, v___f_5238_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_);
if (lean_obj_tag(v___x_5239_) == 0)
{
lean_object* v_a_5240_; lean_object* v___x_5241_; lean_object* v_up_5242_; lean_object* v_squash_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___f_5246_; lean_object* v___x_5247_; 
v_a_5240_ = lean_ctor_get(v___x_5239_, 0);
lean_inc(v_a_5240_);
lean_dec_ref(v___x_5239_);
v___x_5241_ = l_Lean_Meta_NormCast_normCastExt;
v_up_5242_ = lean_ctor_get(v___x_5241_, 0);
lean_inc_ref(v_up_5242_);
v_squash_5243_ = lean_ctor_get(v___x_5241_, 2);
lean_inc_ref(v_squash_5243_);
v___x_5244_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__7));
v___x_5245_ = lean_box(v___x_5231_);
lean_inc(v_a_5225_);
lean_inc_ref(v_config_5213_);
v___f_5246_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__12___boxed), 16, 11);
lean_closure_set(v___f_5246_, 0, v_up_5242_);
lean_closure_set(v___f_5246_, 1, v_config_5213_);
lean_closure_set(v___f_5246_, 2, v___x_5236_);
lean_closure_set(v___f_5246_, 3, v_a_5225_);
lean_closure_set(v___f_5246_, 4, v_a_5240_);
lean_closure_set(v___f_5246_, 5, v___x_5235_);
lean_closure_set(v___f_5246_, 6, v___f_5226_);
lean_closure_set(v___f_5246_, 7, v___f_5229_);
lean_closure_set(v___f_5246_, 8, v___f_5227_);
lean_closure_set(v___f_5246_, 9, v___f_5230_);
lean_closure_set(v___f_5246_, 10, v___x_5245_);
lean_inc(v_a_5217_);
lean_inc_ref(v_a_5216_);
lean_inc(v_a_5215_);
lean_inc_ref(v_a_5214_);
v___x_5247_ = l_Lean_Elab_Tactic_NormCast_derive___lam__5(v___x_5221_, v___x_5231_, v___x_5244_, v___f_5246_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_);
if (lean_obj_tag(v___x_5247_) == 0)
{
lean_object* v_a_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; 
v_a_5248_ = lean_ctor_get(v___x_5247_, 0);
lean_inc(v_a_5248_);
lean_dec_ref(v___x_5247_);
v___x_5249_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__9));
v___x_5250_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_5236_, v___x_5249_, v_hasTrace_5220_, v_a_5216_, v_a_5217_);
if (lean_obj_tag(v___x_5250_) == 0)
{
lean_object* v_a_5251_; lean_object* v___f_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; 
v_a_5251_ = lean_ctor_get(v___x_5250_, 0);
lean_inc(v_a_5251_);
lean_dec_ref(v___x_5250_);
v___f_5252_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__8___boxed), 11, 6);
lean_closure_set(v___f_5252_, 0, v_squash_5243_);
lean_closure_set(v___f_5252_, 1, v_config_5213_);
lean_closure_set(v___f_5252_, 2, v_a_5225_);
lean_closure_set(v___f_5252_, 3, v_a_5248_);
lean_closure_set(v___f_5252_, 4, v___x_5235_);
lean_closure_set(v___f_5252_, 5, v_a_5251_);
v___x_5253_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__10));
v___x_5254_ = l_Lean_Elab_Tactic_NormCast_derive___lam__5(v___x_5221_, v___x_5231_, v___x_5253_, v___f_5252_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_);
return v___x_5254_;
}
else
{
lean_object* v_a_5255_; lean_object* v___x_5257_; uint8_t v_isShared_5258_; uint8_t v_isSharedCheck_5262_; 
lean_dec(v_a_5248_);
lean_dec_ref(v_squash_5243_);
lean_dec(v_a_5225_);
lean_dec(v_a_5217_);
lean_dec_ref(v_a_5216_);
lean_dec(v_a_5215_);
lean_dec_ref(v_a_5214_);
lean_dec_ref(v_config_5213_);
v_a_5255_ = lean_ctor_get(v___x_5250_, 0);
v_isSharedCheck_5262_ = !lean_is_exclusive(v___x_5250_);
if (v_isSharedCheck_5262_ == 0)
{
v___x_5257_ = v___x_5250_;
v_isShared_5258_ = v_isSharedCheck_5262_;
goto v_resetjp_5256_;
}
else
{
lean_inc(v_a_5255_);
lean_dec(v___x_5250_);
v___x_5257_ = lean_box(0);
v_isShared_5258_ = v_isSharedCheck_5262_;
goto v_resetjp_5256_;
}
v_resetjp_5256_:
{
lean_object* v___x_5260_; 
if (v_isShared_5258_ == 0)
{
v___x_5260_ = v___x_5257_;
goto v_reusejp_5259_;
}
else
{
lean_object* v_reuseFailAlloc_5261_; 
v_reuseFailAlloc_5261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5261_, 0, v_a_5255_);
v___x_5260_ = v_reuseFailAlloc_5261_;
goto v_reusejp_5259_;
}
v_reusejp_5259_:
{
return v___x_5260_;
}
}
}
}
else
{
lean_dec_ref(v_squash_5243_);
lean_dec(v_a_5225_);
lean_dec(v_a_5217_);
lean_dec_ref(v_a_5216_);
lean_dec(v_a_5215_);
lean_dec_ref(v_a_5214_);
lean_dec_ref(v_config_5213_);
return v___x_5247_;
}
}
else
{
lean_dec(v_a_5225_);
lean_dec(v_a_5217_);
lean_dec_ref(v_a_5216_);
lean_dec(v_a_5215_);
lean_dec_ref(v_a_5214_);
lean_dec_ref(v_config_5213_);
return v___x_5239_;
}
}
else
{
lean_object* v_a_5263_; lean_object* v___x_5265_; uint8_t v_isShared_5266_; uint8_t v_isSharedCheck_5270_; 
lean_dec(v_a_5223_);
lean_dec(v_a_5217_);
lean_dec_ref(v_a_5216_);
lean_dec(v_a_5215_);
lean_dec_ref(v_a_5214_);
lean_dec_ref(v_config_5213_);
v_a_5263_ = lean_ctor_get(v___x_5224_, 0);
v_isSharedCheck_5270_ = !lean_is_exclusive(v___x_5224_);
if (v_isSharedCheck_5270_ == 0)
{
v___x_5265_ = v___x_5224_;
v_isShared_5266_ = v_isSharedCheck_5270_;
goto v_resetjp_5264_;
}
else
{
lean_inc(v_a_5263_);
lean_dec(v___x_5224_);
v___x_5265_ = lean_box(0);
v_isShared_5266_ = v_isSharedCheck_5270_;
goto v_resetjp_5264_;
}
v_resetjp_5264_:
{
lean_object* v___x_5268_; 
if (v_isShared_5266_ == 0)
{
v___x_5268_ = v___x_5265_;
goto v_reusejp_5267_;
}
else
{
lean_object* v_reuseFailAlloc_5269_; 
v_reuseFailAlloc_5269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5269_, 0, v_a_5263_);
v___x_5268_ = v_reuseFailAlloc_5269_;
goto v_reusejp_5267_;
}
v_reusejp_5267_:
{
return v___x_5268_;
}
}
}
}
else
{
lean_object* v___x_5271_; lean_object* v_a_5272_; lean_object* v___x_5274_; uint8_t v_isShared_5275_; uint8_t v_isSharedCheck_5467_; 
v___x_5271_ = l_Lean_isTracingEnabledFor___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___x_5221_, v_a_5216_);
v_a_5272_ = lean_ctor_get(v___x_5271_, 0);
v_isSharedCheck_5467_ = !lean_is_exclusive(v___x_5271_);
if (v_isSharedCheck_5467_ == 0)
{
v___x_5274_ = v___x_5271_;
v_isShared_5275_ = v_isSharedCheck_5467_;
goto v_resetjp_5273_;
}
else
{
lean_inc(v_a_5272_);
lean_dec(v___x_5271_);
v___x_5274_ = lean_box(0);
v_isShared_5275_ = v_isSharedCheck_5467_;
goto v_resetjp_5273_;
}
v_resetjp_5273_:
{
lean_object* v___f_5276_; lean_object* v___f_5277_; lean_object* v___f_5278_; lean_object* v___x_5279_; lean_object* v___y_5281_; lean_object* v___y_5282_; lean_object* v_a_5283_; lean_object* v___y_5294_; lean_object* v___y_5295_; lean_object* v_a_5296_; lean_object* v___y_5301_; lean_object* v___y_5302_; lean_object* v_a_5303_; lean_object* v___y_5317_; lean_object* v___y_5318_; lean_object* v_a_5319_; uint8_t v___x_5417_; 
v___f_5276_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__0));
v___f_5277_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__1));
lean_inc_ref(v_e_5212_);
v___f_5278_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__18___boxed), 7, 1);
lean_closure_set(v___f_5278_, 0, v_e_5212_);
v___x_5279_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_5417_ = lean_unbox(v_a_5272_);
if (v___x_5417_ == 0)
{
lean_object* v___x_5418_; uint8_t v___x_5419_; 
v___x_5418_ = l_Lean_trace_profiler;
v___x_5419_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_5219_, v___x_5418_);
if (v___x_5419_ == 0)
{
lean_object* v___x_5420_; lean_object* v_a_5421_; lean_object* v___x_5422_; 
lean_dec_ref(v___f_5278_);
lean_del_object(v___x_5274_);
lean_dec(v_a_5272_);
v___x_5420_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_e_5212_, v_a_5215_);
v_a_5421_ = lean_ctor_get(v___x_5420_, 0);
lean_inc(v_a_5421_);
lean_dec_ref(v___x_5420_);
v___x_5422_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_5217_);
if (lean_obj_tag(v___x_5422_) == 0)
{
lean_object* v_a_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___f_5426_; lean_object* v___f_5427_; lean_object* v___f_5428_; lean_object* v___x_5429_; lean_object* v___x_5430_; lean_object* v___x_5431_; lean_object* v___x_5432_; lean_object* v___x_5433_; lean_object* v___f_5434_; lean_object* v___x_5435_; 
v_a_5423_ = lean_ctor_get(v___x_5422_, 0);
lean_inc(v_a_5423_);
lean_dec_ref(v___x_5422_);
v___x_5424_ = lean_box(0);
v___x_5425_ = lean_box(v_hasTrace_5220_);
v___f_5426_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__9___boxed), 11, 2);
lean_closure_set(v___f_5426_, 0, v___x_5424_);
lean_closure_set(v___f_5426_, 1, v___x_5425_);
v___f_5427_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__2));
v___f_5428_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__3));
lean_inc(v_a_5421_);
v___x_5429_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5429_, 0, v_a_5421_);
lean_ctor_set(v___x_5429_, 1, v___x_5424_);
lean_ctor_set_uint8(v___x_5429_, sizeof(void*)*2, v_hasTrace_5220_);
v___x_5430_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__5));
v___x_5431_ = lean_unsigned_to_nat(0u);
v___x_5432_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__6));
v___x_5433_ = lean_box(v_hasTrace_5220_);
lean_inc(v_a_5423_);
lean_inc_ref(v_config_5213_);
v___f_5434_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__14___boxed), 17, 12);
lean_closure_set(v___f_5434_, 0, v_config_5213_);
lean_closure_set(v___f_5434_, 1, v___x_5432_);
lean_closure_set(v___f_5434_, 2, v_a_5423_);
lean_closure_set(v___f_5434_, 3, v___x_5431_);
lean_closure_set(v___f_5434_, 4, v___f_5276_);
lean_closure_set(v___f_5434_, 5, v___f_5426_);
lean_closure_set(v___f_5434_, 6, v___f_5427_);
lean_closure_set(v___f_5434_, 7, v___f_5277_);
lean_closure_set(v___f_5434_, 8, v___f_5428_);
lean_closure_set(v___f_5434_, 9, v___x_5433_);
lean_closure_set(v___f_5434_, 10, v_a_5421_);
lean_closure_set(v___f_5434_, 11, v___x_5429_);
lean_inc(v_a_5217_);
lean_inc_ref(v_a_5216_);
lean_inc(v_a_5215_);
lean_inc_ref(v_a_5214_);
v___x_5435_ = l_Lean_Elab_Tactic_NormCast_derive___lam__27(v___x_5221_, v_hasTrace_5220_, v___x_5430_, v___f_5434_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_);
if (lean_obj_tag(v___x_5435_) == 0)
{
lean_object* v_a_5436_; lean_object* v___x_5437_; lean_object* v_up_5438_; lean_object* v_squash_5439_; lean_object* v___x_5440_; lean_object* v___x_5441_; lean_object* v___f_5442_; lean_object* v___x_5443_; 
v_a_5436_ = lean_ctor_get(v___x_5435_, 0);
lean_inc(v_a_5436_);
lean_dec_ref(v___x_5435_);
v___x_5437_ = l_Lean_Meta_NormCast_normCastExt;
v_up_5438_ = lean_ctor_get(v___x_5437_, 0);
lean_inc_ref(v_up_5438_);
v_squash_5439_ = lean_ctor_get(v___x_5437_, 2);
lean_inc_ref(v_squash_5439_);
v___x_5440_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__7));
v___x_5441_ = lean_box(v_hasTrace_5220_);
lean_inc(v_a_5423_);
lean_inc_ref(v_config_5213_);
v___f_5442_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__15___boxed), 16, 11);
lean_closure_set(v___f_5442_, 0, v_up_5438_);
lean_closure_set(v___f_5442_, 1, v_config_5213_);
lean_closure_set(v___f_5442_, 2, v___x_5432_);
lean_closure_set(v___f_5442_, 3, v_a_5423_);
lean_closure_set(v___f_5442_, 4, v_a_5436_);
lean_closure_set(v___f_5442_, 5, v___x_5431_);
lean_closure_set(v___f_5442_, 6, v___f_5276_);
lean_closure_set(v___f_5442_, 7, v___f_5427_);
lean_closure_set(v___f_5442_, 8, v___f_5277_);
lean_closure_set(v___f_5442_, 9, v___f_5428_);
lean_closure_set(v___f_5442_, 10, v___x_5441_);
lean_inc(v_a_5217_);
lean_inc_ref(v_a_5216_);
lean_inc(v_a_5215_);
lean_inc_ref(v_a_5214_);
v___x_5443_ = l_Lean_Elab_Tactic_NormCast_derive___lam__27(v___x_5221_, v_hasTrace_5220_, v___x_5440_, v___f_5442_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_);
if (lean_obj_tag(v___x_5443_) == 0)
{
lean_object* v_a_5444_; lean_object* v___x_5445_; lean_object* v___x_5446_; 
v_a_5444_ = lean_ctor_get(v___x_5443_, 0);
lean_inc(v_a_5444_);
lean_dec_ref(v___x_5443_);
v___x_5445_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__9));
v___x_5446_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_5432_, v___x_5445_, v___x_5419_, v_a_5216_, v_a_5217_);
if (lean_obj_tag(v___x_5446_) == 0)
{
lean_object* v_a_5447_; lean_object* v___f_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; 
v_a_5447_ = lean_ctor_get(v___x_5446_, 0);
lean_inc(v_a_5447_);
lean_dec_ref(v___x_5446_);
v___f_5448_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__8___boxed), 11, 6);
lean_closure_set(v___f_5448_, 0, v_squash_5439_);
lean_closure_set(v___f_5448_, 1, v_config_5213_);
lean_closure_set(v___f_5448_, 2, v_a_5423_);
lean_closure_set(v___f_5448_, 3, v_a_5444_);
lean_closure_set(v___f_5448_, 4, v___x_5431_);
lean_closure_set(v___f_5448_, 5, v_a_5447_);
v___x_5449_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__10));
v___x_5450_ = l_Lean_Elab_Tactic_NormCast_derive___lam__27(v___x_5221_, v_hasTrace_5220_, v___x_5449_, v___f_5448_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_);
return v___x_5450_;
}
else
{
lean_object* v_a_5451_; lean_object* v___x_5453_; uint8_t v_isShared_5454_; uint8_t v_isSharedCheck_5458_; 
lean_dec(v_a_5444_);
lean_dec_ref(v_squash_5439_);
lean_dec(v_a_5423_);
lean_dec(v_a_5217_);
lean_dec_ref(v_a_5216_);
lean_dec(v_a_5215_);
lean_dec_ref(v_a_5214_);
lean_dec_ref(v_config_5213_);
v_a_5451_ = lean_ctor_get(v___x_5446_, 0);
v_isSharedCheck_5458_ = !lean_is_exclusive(v___x_5446_);
if (v_isSharedCheck_5458_ == 0)
{
v___x_5453_ = v___x_5446_;
v_isShared_5454_ = v_isSharedCheck_5458_;
goto v_resetjp_5452_;
}
else
{
lean_inc(v_a_5451_);
lean_dec(v___x_5446_);
v___x_5453_ = lean_box(0);
v_isShared_5454_ = v_isSharedCheck_5458_;
goto v_resetjp_5452_;
}
v_resetjp_5452_:
{
lean_object* v___x_5456_; 
if (v_isShared_5454_ == 0)
{
v___x_5456_ = v___x_5453_;
goto v_reusejp_5455_;
}
else
{
lean_object* v_reuseFailAlloc_5457_; 
v_reuseFailAlloc_5457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5457_, 0, v_a_5451_);
v___x_5456_ = v_reuseFailAlloc_5457_;
goto v_reusejp_5455_;
}
v_reusejp_5455_:
{
return v___x_5456_;
}
}
}
}
else
{
lean_dec_ref(v_squash_5439_);
lean_dec(v_a_5423_);
lean_dec(v_a_5217_);
lean_dec_ref(v_a_5216_);
lean_dec(v_a_5215_);
lean_dec_ref(v_a_5214_);
lean_dec_ref(v_config_5213_);
return v___x_5443_;
}
}
else
{
lean_dec(v_a_5423_);
lean_dec(v_a_5217_);
lean_dec_ref(v_a_5216_);
lean_dec(v_a_5215_);
lean_dec_ref(v_a_5214_);
lean_dec_ref(v_config_5213_);
return v___x_5435_;
}
}
else
{
lean_object* v_a_5459_; lean_object* v___x_5461_; uint8_t v_isShared_5462_; uint8_t v_isSharedCheck_5466_; 
lean_dec(v_a_5421_);
lean_dec(v_a_5217_);
lean_dec_ref(v_a_5216_);
lean_dec(v_a_5215_);
lean_dec_ref(v_a_5214_);
lean_dec_ref(v_config_5213_);
v_a_5459_ = lean_ctor_get(v___x_5422_, 0);
v_isSharedCheck_5466_ = !lean_is_exclusive(v___x_5422_);
if (v_isSharedCheck_5466_ == 0)
{
v___x_5461_ = v___x_5422_;
v_isShared_5462_ = v_isSharedCheck_5466_;
goto v_resetjp_5460_;
}
else
{
lean_inc(v_a_5459_);
lean_dec(v___x_5422_);
v___x_5461_ = lean_box(0);
v_isShared_5462_ = v_isSharedCheck_5466_;
goto v_resetjp_5460_;
}
v_resetjp_5460_:
{
lean_object* v___x_5464_; 
if (v_isShared_5462_ == 0)
{
v___x_5464_ = v___x_5461_;
goto v_reusejp_5463_;
}
else
{
lean_object* v_reuseFailAlloc_5465_; 
v_reuseFailAlloc_5465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5465_, 0, v_a_5459_);
v___x_5464_ = v_reuseFailAlloc_5465_;
goto v_reusejp_5463_;
}
v_reusejp_5463_:
{
return v___x_5464_;
}
}
}
}
else
{
lean_inc_ref(v_options_5219_);
goto v___jp_5321_;
}
}
else
{
lean_inc_ref(v_options_5219_);
goto v___jp_5321_;
}
v___jp_5280_:
{
lean_object* v___x_5284_; double v___x_5285_; double v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; uint8_t v___x_5291_; lean_object* v___x_5292_; 
v___x_5284_ = lean_io_get_num_heartbeats();
v___x_5285_ = lean_float_of_nat(v___y_5282_);
v___x_5286_ = lean_float_of_nat(v___x_5284_);
v___x_5287_ = lean_box_float(v___x_5285_);
v___x_5288_ = lean_box_float(v___x_5286_);
v___x_5289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5289_, 0, v___x_5287_);
lean_ctor_set(v___x_5289_, 1, v___x_5288_);
v___x_5290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5290_, 0, v_a_5283_);
lean_ctor_set(v___x_5290_, 1, v___x_5289_);
v___x_5291_ = lean_unbox(v_a_5272_);
lean_dec(v_a_5272_);
v___x_5292_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_5221_, v_hasTrace_5220_, v___x_5279_, v_options_5219_, v___x_5291_, v___y_5281_, v___f_5278_, v___x_5290_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_);
lean_dec_ref(v_options_5219_);
return v___x_5292_;
}
v___jp_5293_:
{
lean_object* v___x_5298_; 
if (v_isShared_5275_ == 0)
{
lean_ctor_set(v___x_5274_, 0, v_a_5296_);
v___x_5298_ = v___x_5274_;
goto v_reusejp_5297_;
}
else
{
lean_object* v_reuseFailAlloc_5299_; 
v_reuseFailAlloc_5299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5299_, 0, v_a_5296_);
v___x_5298_ = v_reuseFailAlloc_5299_;
goto v_reusejp_5297_;
}
v_reusejp_5297_:
{
v___y_5281_ = v___y_5294_;
v___y_5282_ = v___y_5295_;
v_a_5283_ = v___x_5298_;
goto v___jp_5280_;
}
}
v___jp_5300_:
{
lean_object* v___x_5304_; double v___x_5305_; double v___x_5306_; double v___x_5307_; double v___x_5308_; double v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; uint8_t v___x_5314_; lean_object* v___x_5315_; 
v___x_5304_ = lean_io_mono_nanos_now();
v___x_5305_ = lean_float_of_nat(v___y_5301_);
v___x_5306_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1);
v___x_5307_ = lean_float_div(v___x_5305_, v___x_5306_);
v___x_5308_ = lean_float_of_nat(v___x_5304_);
v___x_5309_ = lean_float_div(v___x_5308_, v___x_5306_);
v___x_5310_ = lean_box_float(v___x_5307_);
v___x_5311_ = lean_box_float(v___x_5309_);
v___x_5312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5312_, 0, v___x_5310_);
lean_ctor_set(v___x_5312_, 1, v___x_5311_);
v___x_5313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5313_, 0, v_a_5303_);
lean_ctor_set(v___x_5313_, 1, v___x_5312_);
v___x_5314_ = lean_unbox(v_a_5272_);
lean_dec(v_a_5272_);
v___x_5315_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_5221_, v_hasTrace_5220_, v___x_5279_, v_options_5219_, v___x_5314_, v___y_5302_, v___f_5278_, v___x_5313_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_);
lean_dec_ref(v_options_5219_);
return v___x_5315_;
}
v___jp_5316_:
{
lean_object* v___x_5320_; 
v___x_5320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5320_, 0, v_a_5319_);
v___y_5301_ = v___y_5317_;
v___y_5302_ = v___y_5318_;
v_a_5303_ = v___x_5320_;
goto v___jp_5300_;
}
v___jp_5321_:
{
lean_object* v___x_5322_; lean_object* v_a_5323_; lean_object* v___x_5324_; uint8_t v___x_5325_; 
v___x_5322_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___redArg(v_a_5217_);
v_a_5323_ = lean_ctor_get(v___x_5322_, 0);
lean_inc(v_a_5323_);
lean_dec_ref(v___x_5322_);
v___x_5324_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5325_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_options_5219_, v___x_5324_);
if (v___x_5325_ == 0)
{
lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v_a_5328_; lean_object* v___x_5329_; 
lean_del_object(v___x_5274_);
v___x_5326_ = lean_io_mono_nanos_now();
v___x_5327_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_e_5212_, v_a_5215_);
v_a_5328_ = lean_ctor_get(v___x_5327_, 0);
lean_inc(v_a_5328_);
lean_dec_ref(v___x_5327_);
v___x_5329_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_5217_);
if (lean_obj_tag(v___x_5329_) == 0)
{
lean_object* v_a_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___f_5333_; lean_object* v___f_5334_; lean_object* v___f_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___f_5341_; lean_object* v___x_5342_; 
v_a_5330_ = lean_ctor_get(v___x_5329_, 0);
lean_inc(v_a_5330_);
lean_dec_ref(v___x_5329_);
v___x_5331_ = lean_box(0);
v___x_5332_ = lean_box(v_hasTrace_5220_);
v___f_5333_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__9___boxed), 11, 2);
lean_closure_set(v___f_5333_, 0, v___x_5331_);
lean_closure_set(v___f_5333_, 1, v___x_5332_);
v___f_5334_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__2));
v___f_5335_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__3));
lean_inc(v_a_5328_);
v___x_5336_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5336_, 0, v_a_5328_);
lean_ctor_set(v___x_5336_, 1, v___x_5331_);
lean_ctor_set_uint8(v___x_5336_, sizeof(void*)*2, v_hasTrace_5220_);
v___x_5337_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__5));
v___x_5338_ = lean_unsigned_to_nat(0u);
v___x_5339_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__6));
v___x_5340_ = lean_box(v_hasTrace_5220_);
lean_inc(v_a_5330_);
lean_inc_ref(v_config_5213_);
v___f_5341_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__14___boxed), 17, 12);
lean_closure_set(v___f_5341_, 0, v_config_5213_);
lean_closure_set(v___f_5341_, 1, v___x_5339_);
lean_closure_set(v___f_5341_, 2, v_a_5330_);
lean_closure_set(v___f_5341_, 3, v___x_5338_);
lean_closure_set(v___f_5341_, 4, v___f_5276_);
lean_closure_set(v___f_5341_, 5, v___f_5333_);
lean_closure_set(v___f_5341_, 6, v___f_5334_);
lean_closure_set(v___f_5341_, 7, v___f_5277_);
lean_closure_set(v___f_5341_, 8, v___f_5335_);
lean_closure_set(v___f_5341_, 9, v___x_5340_);
lean_closure_set(v___f_5341_, 10, v_a_5328_);
lean_closure_set(v___f_5341_, 11, v___x_5336_);
lean_inc(v_a_5217_);
lean_inc_ref(v_a_5216_);
lean_inc(v_a_5215_);
lean_inc_ref(v_a_5214_);
v___x_5342_ = l_Lean_Elab_Tactic_NormCast_derive___lam__10(v___x_5221_, v_hasTrace_5220_, v___x_5337_, v___f_5341_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_);
if (lean_obj_tag(v___x_5342_) == 0)
{
lean_object* v_a_5343_; lean_object* v___x_5344_; lean_object* v_up_5345_; lean_object* v_squash_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; lean_object* v___f_5349_; lean_object* v___x_5350_; 
v_a_5343_ = lean_ctor_get(v___x_5342_, 0);
lean_inc(v_a_5343_);
lean_dec_ref(v___x_5342_);
v___x_5344_ = l_Lean_Meta_NormCast_normCastExt;
v_up_5345_ = lean_ctor_get(v___x_5344_, 0);
lean_inc_ref(v_up_5345_);
v_squash_5346_ = lean_ctor_get(v___x_5344_, 2);
lean_inc_ref(v_squash_5346_);
v___x_5347_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__7));
v___x_5348_ = lean_box(v_hasTrace_5220_);
lean_inc(v_a_5330_);
lean_inc_ref(v_config_5213_);
v___f_5349_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__15___boxed), 16, 11);
lean_closure_set(v___f_5349_, 0, v_up_5345_);
lean_closure_set(v___f_5349_, 1, v_config_5213_);
lean_closure_set(v___f_5349_, 2, v___x_5339_);
lean_closure_set(v___f_5349_, 3, v_a_5330_);
lean_closure_set(v___f_5349_, 4, v_a_5343_);
lean_closure_set(v___f_5349_, 5, v___x_5338_);
lean_closure_set(v___f_5349_, 6, v___f_5276_);
lean_closure_set(v___f_5349_, 7, v___f_5334_);
lean_closure_set(v___f_5349_, 8, v___f_5277_);
lean_closure_set(v___f_5349_, 9, v___f_5335_);
lean_closure_set(v___f_5349_, 10, v___x_5348_);
lean_inc(v_a_5217_);
lean_inc_ref(v_a_5216_);
lean_inc(v_a_5215_);
lean_inc_ref(v_a_5214_);
v___x_5350_ = l_Lean_Elab_Tactic_NormCast_derive___lam__10(v___x_5221_, v_hasTrace_5220_, v___x_5347_, v___f_5349_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_);
if (lean_obj_tag(v___x_5350_) == 0)
{
lean_object* v_a_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; 
v_a_5351_ = lean_ctor_get(v___x_5350_, 0);
lean_inc(v_a_5351_);
lean_dec_ref(v___x_5350_);
v___x_5352_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__9));
v___x_5353_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_5339_, v___x_5352_, v___x_5325_, v_a_5216_, v_a_5217_);
if (lean_obj_tag(v___x_5353_) == 0)
{
lean_object* v_a_5354_; lean_object* v___f_5355_; lean_object* v___x_5356_; lean_object* v___x_5357_; 
v_a_5354_ = lean_ctor_get(v___x_5353_, 0);
lean_inc(v_a_5354_);
lean_dec_ref(v___x_5353_);
v___f_5355_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__8___boxed), 11, 6);
lean_closure_set(v___f_5355_, 0, v_squash_5346_);
lean_closure_set(v___f_5355_, 1, v_config_5213_);
lean_closure_set(v___f_5355_, 2, v_a_5330_);
lean_closure_set(v___f_5355_, 3, v_a_5351_);
lean_closure_set(v___f_5355_, 4, v___x_5338_);
lean_closure_set(v___f_5355_, 5, v_a_5354_);
v___x_5356_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__10));
lean_inc(v_a_5217_);
lean_inc_ref(v_a_5216_);
lean_inc(v_a_5215_);
lean_inc_ref(v_a_5214_);
v___x_5357_ = l_Lean_Elab_Tactic_NormCast_derive___lam__10(v___x_5221_, v_hasTrace_5220_, v___x_5356_, v___f_5355_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_);
if (lean_obj_tag(v___x_5357_) == 0)
{
lean_object* v_a_5358_; lean_object* v___x_5360_; uint8_t v_isShared_5361_; uint8_t v_isSharedCheck_5365_; 
v_a_5358_ = lean_ctor_get(v___x_5357_, 0);
v_isSharedCheck_5365_ = !lean_is_exclusive(v___x_5357_);
if (v_isSharedCheck_5365_ == 0)
{
v___x_5360_ = v___x_5357_;
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
else
{
lean_inc(v_a_5358_);
lean_dec(v___x_5357_);
v___x_5360_ = lean_box(0);
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
v_resetjp_5359_:
{
lean_object* v___x_5363_; 
if (v_isShared_5361_ == 0)
{
lean_ctor_set_tag(v___x_5360_, 1);
v___x_5363_ = v___x_5360_;
goto v_reusejp_5362_;
}
else
{
lean_object* v_reuseFailAlloc_5364_; 
v_reuseFailAlloc_5364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5364_, 0, v_a_5358_);
v___x_5363_ = v_reuseFailAlloc_5364_;
goto v_reusejp_5362_;
}
v_reusejp_5362_:
{
v___y_5301_ = v___x_5326_;
v___y_5302_ = v_a_5323_;
v_a_5303_ = v___x_5363_;
goto v___jp_5300_;
}
}
}
else
{
lean_object* v_a_5366_; 
v_a_5366_ = lean_ctor_get(v___x_5357_, 0);
lean_inc(v_a_5366_);
lean_dec_ref(v___x_5357_);
v___y_5317_ = v___x_5326_;
v___y_5318_ = v_a_5323_;
v_a_5319_ = v_a_5366_;
goto v___jp_5316_;
}
}
else
{
lean_object* v_a_5367_; 
lean_dec(v_a_5351_);
lean_dec_ref(v_squash_5346_);
lean_dec(v_a_5330_);
lean_dec_ref(v_config_5213_);
v_a_5367_ = lean_ctor_get(v___x_5353_, 0);
lean_inc(v_a_5367_);
lean_dec_ref(v___x_5353_);
v___y_5317_ = v___x_5326_;
v___y_5318_ = v_a_5323_;
v_a_5319_ = v_a_5367_;
goto v___jp_5316_;
}
}
else
{
lean_object* v_a_5368_; 
lean_dec_ref(v_squash_5346_);
lean_dec(v_a_5330_);
lean_dec_ref(v_config_5213_);
v_a_5368_ = lean_ctor_get(v___x_5350_, 0);
lean_inc(v_a_5368_);
lean_dec_ref(v___x_5350_);
v___y_5317_ = v___x_5326_;
v___y_5318_ = v_a_5323_;
v_a_5319_ = v_a_5368_;
goto v___jp_5316_;
}
}
else
{
lean_object* v_a_5369_; 
lean_dec(v_a_5330_);
lean_dec_ref(v_config_5213_);
v_a_5369_ = lean_ctor_get(v___x_5342_, 0);
lean_inc(v_a_5369_);
lean_dec_ref(v___x_5342_);
v___y_5317_ = v___x_5326_;
v___y_5318_ = v_a_5323_;
v_a_5319_ = v_a_5369_;
goto v___jp_5316_;
}
}
else
{
lean_object* v_a_5370_; 
lean_dec(v_a_5328_);
lean_dec_ref(v_config_5213_);
v_a_5370_ = lean_ctor_get(v___x_5329_, 0);
lean_inc(v_a_5370_);
lean_dec_ref(v___x_5329_);
v___y_5317_ = v___x_5326_;
v___y_5318_ = v_a_5323_;
v_a_5319_ = v_a_5370_;
goto v___jp_5316_;
}
}
else
{
lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v_a_5373_; lean_object* v___x_5374_; 
v___x_5371_ = lean_io_get_num_heartbeats();
v___x_5372_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_e_5212_, v_a_5215_);
v_a_5373_ = lean_ctor_get(v___x_5372_, 0);
lean_inc(v_a_5373_);
lean_dec_ref(v___x_5372_);
v___x_5374_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_5217_);
if (lean_obj_tag(v___x_5374_) == 0)
{
lean_object* v_a_5375_; lean_object* v___x_5376_; lean_object* v___x_5377_; lean_object* v___f_5378_; lean_object* v___f_5379_; lean_object* v___f_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___f_5386_; lean_object* v___x_5387_; 
v_a_5375_ = lean_ctor_get(v___x_5374_, 0);
lean_inc(v_a_5375_);
lean_dec_ref(v___x_5374_);
v___x_5376_ = lean_box(0);
v___x_5377_ = lean_box(v___x_5325_);
v___f_5378_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__6___boxed), 11, 2);
lean_closure_set(v___f_5378_, 0, v___x_5376_);
lean_closure_set(v___f_5378_, 1, v___x_5377_);
v___f_5379_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__2));
v___f_5380_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__3));
lean_inc(v_a_5373_);
v___x_5381_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5381_, 0, v_a_5373_);
lean_ctor_set(v___x_5381_, 1, v___x_5376_);
lean_ctor_set_uint8(v___x_5381_, sizeof(void*)*2, v___x_5325_);
v___x_5382_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__5));
v___x_5383_ = lean_unsigned_to_nat(0u);
v___x_5384_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__6));
v___x_5385_ = lean_box(v___x_5325_);
lean_inc(v_a_5375_);
lean_inc_ref(v_config_5213_);
v___f_5386_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__7___boxed), 17, 12);
lean_closure_set(v___f_5386_, 0, v_config_5213_);
lean_closure_set(v___f_5386_, 1, v___x_5384_);
lean_closure_set(v___f_5386_, 2, v_a_5375_);
lean_closure_set(v___f_5386_, 3, v___x_5383_);
lean_closure_set(v___f_5386_, 4, v___f_5276_);
lean_closure_set(v___f_5386_, 5, v___f_5378_);
lean_closure_set(v___f_5386_, 6, v___f_5379_);
lean_closure_set(v___f_5386_, 7, v___f_5277_);
lean_closure_set(v___f_5386_, 8, v___f_5380_);
lean_closure_set(v___f_5386_, 9, v___x_5385_);
lean_closure_set(v___f_5386_, 10, v_a_5373_);
lean_closure_set(v___f_5386_, 11, v___x_5381_);
lean_inc(v_a_5217_);
lean_inc_ref(v_a_5216_);
lean_inc(v_a_5215_);
lean_inc_ref(v_a_5214_);
v___x_5387_ = l_Lean_Elab_Tactic_NormCast_derive___lam__16(v___x_5221_, v___x_5325_, v___x_5279_, v___x_5324_, v___x_5382_, v___f_5386_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_);
if (lean_obj_tag(v___x_5387_) == 0)
{
lean_object* v_a_5388_; lean_object* v___x_5389_; lean_object* v_up_5390_; lean_object* v_squash_5391_; lean_object* v___x_5392_; lean_object* v___x_5393_; lean_object* v___f_5394_; lean_object* v___x_5395_; 
v_a_5388_ = lean_ctor_get(v___x_5387_, 0);
lean_inc(v_a_5388_);
lean_dec_ref(v___x_5387_);
v___x_5389_ = l_Lean_Meta_NormCast_normCastExt;
v_up_5390_ = lean_ctor_get(v___x_5389_, 0);
lean_inc_ref(v_up_5390_);
v_squash_5391_ = lean_ctor_get(v___x_5389_, 2);
lean_inc_ref(v_squash_5391_);
v___x_5392_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__7));
v___x_5393_ = lean_box(v___x_5325_);
lean_inc(v_a_5375_);
lean_inc_ref(v_config_5213_);
v___f_5394_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__12___boxed), 16, 11);
lean_closure_set(v___f_5394_, 0, v_up_5390_);
lean_closure_set(v___f_5394_, 1, v_config_5213_);
lean_closure_set(v___f_5394_, 2, v___x_5384_);
lean_closure_set(v___f_5394_, 3, v_a_5375_);
lean_closure_set(v___f_5394_, 4, v_a_5388_);
lean_closure_set(v___f_5394_, 5, v___x_5383_);
lean_closure_set(v___f_5394_, 6, v___f_5276_);
lean_closure_set(v___f_5394_, 7, v___f_5379_);
lean_closure_set(v___f_5394_, 8, v___f_5277_);
lean_closure_set(v___f_5394_, 9, v___f_5380_);
lean_closure_set(v___f_5394_, 10, v___x_5393_);
lean_inc(v_a_5217_);
lean_inc_ref(v_a_5216_);
lean_inc(v_a_5215_);
lean_inc_ref(v_a_5214_);
v___x_5395_ = l_Lean_Elab_Tactic_NormCast_derive___lam__16(v___x_5221_, v___x_5325_, v___x_5279_, v___x_5324_, v___x_5392_, v___f_5394_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_);
if (lean_obj_tag(v___x_5395_) == 0)
{
lean_object* v_a_5396_; lean_object* v___x_5397_; uint8_t v___x_5398_; lean_object* v___x_5399_; 
v_a_5396_ = lean_ctor_get(v___x_5395_, 0);
lean_inc(v_a_5396_);
lean_dec_ref(v___x_5395_);
v___x_5397_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__9));
v___x_5398_ = 0;
v___x_5399_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_5384_, v___x_5397_, v___x_5398_, v_a_5216_, v_a_5217_);
if (lean_obj_tag(v___x_5399_) == 0)
{
lean_object* v_a_5400_; lean_object* v___f_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; 
v_a_5400_ = lean_ctor_get(v___x_5399_, 0);
lean_inc(v_a_5400_);
lean_dec_ref(v___x_5399_);
v___f_5401_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__8___boxed), 11, 6);
lean_closure_set(v___f_5401_, 0, v_squash_5391_);
lean_closure_set(v___f_5401_, 1, v_config_5213_);
lean_closure_set(v___f_5401_, 2, v_a_5375_);
lean_closure_set(v___f_5401_, 3, v_a_5396_);
lean_closure_set(v___f_5401_, 4, v___x_5383_);
lean_closure_set(v___f_5401_, 5, v_a_5400_);
v___x_5402_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__10));
lean_inc(v_a_5217_);
lean_inc_ref(v_a_5216_);
lean_inc(v_a_5215_);
lean_inc_ref(v_a_5214_);
v___x_5403_ = l_Lean_Elab_Tactic_NormCast_derive___lam__16(v___x_5221_, v___x_5325_, v___x_5279_, v___x_5324_, v___x_5402_, v___f_5401_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_);
if (lean_obj_tag(v___x_5403_) == 0)
{
lean_object* v_a_5404_; lean_object* v___x_5406_; uint8_t v_isShared_5407_; uint8_t v_isSharedCheck_5411_; 
lean_del_object(v___x_5274_);
v_a_5404_ = lean_ctor_get(v___x_5403_, 0);
v_isSharedCheck_5411_ = !lean_is_exclusive(v___x_5403_);
if (v_isSharedCheck_5411_ == 0)
{
v___x_5406_ = v___x_5403_;
v_isShared_5407_ = v_isSharedCheck_5411_;
goto v_resetjp_5405_;
}
else
{
lean_inc(v_a_5404_);
lean_dec(v___x_5403_);
v___x_5406_ = lean_box(0);
v_isShared_5407_ = v_isSharedCheck_5411_;
goto v_resetjp_5405_;
}
v_resetjp_5405_:
{
lean_object* v___x_5409_; 
if (v_isShared_5407_ == 0)
{
lean_ctor_set_tag(v___x_5406_, 1);
v___x_5409_ = v___x_5406_;
goto v_reusejp_5408_;
}
else
{
lean_object* v_reuseFailAlloc_5410_; 
v_reuseFailAlloc_5410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5410_, 0, v_a_5404_);
v___x_5409_ = v_reuseFailAlloc_5410_;
goto v_reusejp_5408_;
}
v_reusejp_5408_:
{
v___y_5281_ = v_a_5323_;
v___y_5282_ = v___x_5371_;
v_a_5283_ = v___x_5409_;
goto v___jp_5280_;
}
}
}
else
{
lean_object* v_a_5412_; 
v_a_5412_ = lean_ctor_get(v___x_5403_, 0);
lean_inc(v_a_5412_);
lean_dec_ref(v___x_5403_);
v___y_5294_ = v_a_5323_;
v___y_5295_ = v___x_5371_;
v_a_5296_ = v_a_5412_;
goto v___jp_5293_;
}
}
else
{
lean_object* v_a_5413_; 
lean_dec(v_a_5396_);
lean_dec_ref(v_squash_5391_);
lean_dec(v_a_5375_);
lean_dec_ref(v_config_5213_);
v_a_5413_ = lean_ctor_get(v___x_5399_, 0);
lean_inc(v_a_5413_);
lean_dec_ref(v___x_5399_);
v___y_5294_ = v_a_5323_;
v___y_5295_ = v___x_5371_;
v_a_5296_ = v_a_5413_;
goto v___jp_5293_;
}
}
else
{
lean_object* v_a_5414_; 
lean_dec_ref(v_squash_5391_);
lean_dec(v_a_5375_);
lean_dec_ref(v_config_5213_);
v_a_5414_ = lean_ctor_get(v___x_5395_, 0);
lean_inc(v_a_5414_);
lean_dec_ref(v___x_5395_);
v___y_5294_ = v_a_5323_;
v___y_5295_ = v___x_5371_;
v_a_5296_ = v_a_5414_;
goto v___jp_5293_;
}
}
else
{
lean_object* v_a_5415_; 
lean_dec(v_a_5375_);
lean_dec_ref(v_config_5213_);
v_a_5415_ = lean_ctor_get(v___x_5387_, 0);
lean_inc(v_a_5415_);
lean_dec_ref(v___x_5387_);
v___y_5294_ = v_a_5323_;
v___y_5295_ = v___x_5371_;
v_a_5296_ = v_a_5415_;
goto v___jp_5293_;
}
}
else
{
lean_object* v_a_5416_; 
lean_dec(v_a_5373_);
lean_dec_ref(v_config_5213_);
v_a_5416_ = lean_ctor_get(v___x_5374_, 0);
lean_inc(v_a_5416_);
lean_dec_ref(v___x_5374_);
v___y_5294_ = v_a_5323_;
v___y_5295_ = v___x_5371_;
v_a_5296_ = v_a_5416_;
goto v___jp_5293_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___boxed(lean_object* v_e_5468_, lean_object* v_config_5469_, lean_object* v_a_5470_, lean_object* v_a_5471_, lean_object* v_a_5472_, lean_object* v_a_5473_, lean_object* v_a_5474_){
_start:
{
lean_object* v_res_5475_; 
v_res_5475_ = l_Lean_Elab_Tactic_NormCast_derive(v_e_5468_, v_config_5469_, v_a_5470_, v_a_5471_, v_a_5472_, v_a_5473_);
return v_res_5475_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; 
v___x_5476_ = lean_box(0);
v___x_5477_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_5478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5478_, 0, v___x_5477_);
lean_ctor_set(v___x_5478_, 1, v___x_5476_);
return v___x_5478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg(){
_start:
{
lean_object* v___x_5480_; lean_object* v___x_5481_; 
v___x_5480_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0);
v___x_5481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5481_, 0, v___x_5480_);
return v___x_5481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___boxed(lean_object* v___y_5482_){
_start:
{
lean_object* v_res_5483_; 
v_res_5483_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg();
return v_res_5483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0(lean_object* v_00_u03b1_5484_, lean_object* v___y_5485_, lean_object* v___y_5486_, lean_object* v___y_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_, lean_object* v___y_5490_){
_start:
{
lean_object* v___x_5492_; 
v___x_5492_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg();
return v___x_5492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___boxed(lean_object* v_00_u03b1_5493_, lean_object* v___y_5494_, lean_object* v___y_5495_, lean_object* v___y_5496_, lean_object* v___y_5497_, lean_object* v___y_5498_, lean_object* v___y_5499_, lean_object* v___y_5500_){
_start:
{
lean_object* v_res_5501_; 
v_res_5501_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0(v_00_u03b1_5493_, v___y_5494_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_);
lean_dec(v___y_5499_);
lean_dec_ref(v___y_5498_);
lean_dec(v___y_5497_);
lean_dec_ref(v___y_5496_);
lean_dec(v___y_5495_);
lean_dec_ref(v___y_5494_);
return v_res_5501_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg(lean_object* v_e_5502_, lean_object* v___y_5503_){
_start:
{
uint8_t v___x_5505_; 
v___x_5505_ = l_Lean_Expr_hasMVar(v_e_5502_);
if (v___x_5505_ == 0)
{
lean_object* v___x_5506_; 
v___x_5506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5506_, 0, v_e_5502_);
return v___x_5506_;
}
else
{
lean_object* v___x_5507_; lean_object* v_mctx_5508_; lean_object* v___x_5509_; lean_object* v_fst_5510_; lean_object* v_snd_5511_; lean_object* v___x_5512_; lean_object* v_cache_5513_; lean_object* v_zetaDeltaFVarIds_5514_; lean_object* v_postponed_5515_; lean_object* v_diag_5516_; lean_object* v___x_5518_; uint8_t v_isShared_5519_; uint8_t v_isSharedCheck_5525_; 
v___x_5507_ = lean_st_ref_get(v___y_5503_);
v_mctx_5508_ = lean_ctor_get(v___x_5507_, 0);
lean_inc_ref(v_mctx_5508_);
lean_dec(v___x_5507_);
v___x_5509_ = l_Lean_instantiateMVarsCore(v_mctx_5508_, v_e_5502_);
v_fst_5510_ = lean_ctor_get(v___x_5509_, 0);
lean_inc(v_fst_5510_);
v_snd_5511_ = lean_ctor_get(v___x_5509_, 1);
lean_inc(v_snd_5511_);
lean_dec_ref(v___x_5509_);
v___x_5512_ = lean_st_ref_take(v___y_5503_);
v_cache_5513_ = lean_ctor_get(v___x_5512_, 1);
v_zetaDeltaFVarIds_5514_ = lean_ctor_get(v___x_5512_, 2);
v_postponed_5515_ = lean_ctor_get(v___x_5512_, 3);
v_diag_5516_ = lean_ctor_get(v___x_5512_, 4);
v_isSharedCheck_5525_ = !lean_is_exclusive(v___x_5512_);
if (v_isSharedCheck_5525_ == 0)
{
lean_object* v_unused_5526_; 
v_unused_5526_ = lean_ctor_get(v___x_5512_, 0);
lean_dec(v_unused_5526_);
v___x_5518_ = v___x_5512_;
v_isShared_5519_ = v_isSharedCheck_5525_;
goto v_resetjp_5517_;
}
else
{
lean_inc(v_diag_5516_);
lean_inc(v_postponed_5515_);
lean_inc(v_zetaDeltaFVarIds_5514_);
lean_inc(v_cache_5513_);
lean_dec(v___x_5512_);
v___x_5518_ = lean_box(0);
v_isShared_5519_ = v_isSharedCheck_5525_;
goto v_resetjp_5517_;
}
v_resetjp_5517_:
{
lean_object* v___x_5521_; 
if (v_isShared_5519_ == 0)
{
lean_ctor_set(v___x_5518_, 0, v_snd_5511_);
v___x_5521_ = v___x_5518_;
goto v_reusejp_5520_;
}
else
{
lean_object* v_reuseFailAlloc_5524_; 
v_reuseFailAlloc_5524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5524_, 0, v_snd_5511_);
lean_ctor_set(v_reuseFailAlloc_5524_, 1, v_cache_5513_);
lean_ctor_set(v_reuseFailAlloc_5524_, 2, v_zetaDeltaFVarIds_5514_);
lean_ctor_set(v_reuseFailAlloc_5524_, 3, v_postponed_5515_);
lean_ctor_set(v_reuseFailAlloc_5524_, 4, v_diag_5516_);
v___x_5521_ = v_reuseFailAlloc_5524_;
goto v_reusejp_5520_;
}
v_reusejp_5520_:
{
lean_object* v___x_5522_; lean_object* v___x_5523_; 
v___x_5522_ = lean_st_ref_set(v___y_5503_, v___x_5521_);
v___x_5523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5523_, 0, v_fst_5510_);
return v___x_5523_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg___boxed(lean_object* v_e_5527_, lean_object* v___y_5528_, lean_object* v___y_5529_){
_start:
{
lean_object* v_res_5530_; 
v_res_5530_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg(v_e_5527_, v___y_5528_);
lean_dec(v___y_5528_);
return v_res_5530_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1(lean_object* v_e_5531_, lean_object* v___y_5532_, lean_object* v___y_5533_, lean_object* v___y_5534_, lean_object* v___y_5535_, lean_object* v___y_5536_, lean_object* v___y_5537_){
_start:
{
lean_object* v___x_5539_; 
v___x_5539_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg(v_e_5531_, v___y_5535_);
return v___x_5539_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___boxed(lean_object* v_e_5540_, lean_object* v___y_5541_, lean_object* v___y_5542_, lean_object* v___y_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_, lean_object* v___y_5546_, lean_object* v___y_5547_){
_start:
{
lean_object* v_res_5548_; 
v_res_5548_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1(v_e_5540_, v___y_5541_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_);
lean_dec(v___y_5546_);
lean_dec_ref(v___y_5545_);
lean_dec(v___y_5544_);
lean_dec_ref(v___y_5543_);
lean_dec(v___y_5542_);
lean_dec_ref(v___y_5541_);
return v_res_5548_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__2(void){
_start:
{
lean_object* v___x_5552_; lean_object* v___x_5553_; 
v___x_5552_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__1));
v___x_5553_ = l_Lean_MessageData_ofFormat(v___x_5552_);
return v___x_5553_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5554_; lean_object* v___x_5555_; 
v___x_5554_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__2, &l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__2);
v___x_5555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5555_, 0, v___x_5554_);
return v___x_5555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0(uint8_t v___x_5556_, lean_object* v___x_5557_, lean_object* v_expectedType_5558_, lean_object* v___y_5559_, lean_object* v___y_5560_, lean_object* v___y_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_){
_start:
{
lean_object* v___y_5567_; lean_object* v___y_5568_; lean_object* v___y_5569_; lean_object* v___y_5570_; lean_object* v___y_5571_; lean_object* v___y_5572_; lean_object* v___y_5573_; lean_object* v___y_5596_; lean_object* v___y_5597_; lean_object* v___y_5598_; lean_object* v___y_5599_; lean_object* v___y_5600_; lean_object* v___y_5601_; lean_object* v___y_5602_; lean_object* v___y_5603_; lean_object* v___y_5604_; lean_object* v___y_5639_; lean_object* v___y_5640_; lean_object* v___y_5641_; lean_object* v___y_5642_; lean_object* v___y_5643_; lean_object* v___y_5644_; lean_object* v___x_5689_; lean_object* v_a_5690_; uint8_t v___x_5691_; 
lean_inc_ref(v_expectedType_5558_);
v___x_5689_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg(v_expectedType_5558_, v___y_5562_);
v_a_5690_ = lean_ctor_get(v___x_5689_, 0);
lean_inc(v_a_5690_);
lean_dec_ref(v___x_5689_);
v___x_5691_ = l_Lean_Expr_hasExprMVar(v_a_5690_);
lean_dec(v_a_5690_);
if (v___x_5691_ == 0)
{
v___y_5639_ = v___y_5559_;
v___y_5640_ = v___y_5560_;
v___y_5641_ = v___y_5561_;
v___y_5642_ = v___y_5562_;
v___y_5643_ = v___y_5563_;
v___y_5644_ = v___y_5564_;
goto v___jp_5638_;
}
else
{
lean_object* v___x_5692_; 
v___x_5692_ = l_Lean_Elab_Term_tryPostpone(v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_);
if (lean_obj_tag(v___x_5692_) == 0)
{
lean_dec_ref(v___x_5692_);
v___y_5639_ = v___y_5559_;
v___y_5640_ = v___y_5560_;
v___y_5641_ = v___y_5561_;
v___y_5642_ = v___y_5562_;
v___y_5643_ = v___y_5563_;
v___y_5644_ = v___y_5564_;
goto v___jp_5638_;
}
else
{
lean_object* v_a_5693_; lean_object* v___x_5695_; uint8_t v_isShared_5696_; uint8_t v_isSharedCheck_5700_; 
lean_dec(v___y_5564_);
lean_dec_ref(v___y_5563_);
lean_dec(v___y_5562_);
lean_dec_ref(v___y_5561_);
lean_dec(v___y_5560_);
lean_dec_ref(v___y_5559_);
lean_dec_ref(v_expectedType_5558_);
lean_dec(v___x_5557_);
v_a_5693_ = lean_ctor_get(v___x_5692_, 0);
v_isSharedCheck_5700_ = !lean_is_exclusive(v___x_5692_);
if (v_isSharedCheck_5700_ == 0)
{
v___x_5695_ = v___x_5692_;
v_isShared_5696_ = v_isSharedCheck_5700_;
goto v_resetjp_5694_;
}
else
{
lean_inc(v_a_5693_);
lean_dec(v___x_5692_);
v___x_5695_ = lean_box(0);
v_isShared_5696_ = v_isSharedCheck_5700_;
goto v_resetjp_5694_;
}
v_resetjp_5694_:
{
lean_object* v___x_5698_; 
if (v_isShared_5696_ == 0)
{
v___x_5698_ = v___x_5695_;
goto v_reusejp_5697_;
}
else
{
lean_object* v_reuseFailAlloc_5699_; 
v_reuseFailAlloc_5699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5699_, 0, v_a_5693_);
v___x_5698_ = v_reuseFailAlloc_5699_;
goto v_reusejp_5697_;
}
v_reusejp_5697_:
{
return v___x_5698_;
}
}
}
}
v___jp_5566_:
{
lean_object* v___x_5574_; 
lean_inc(v___y_5573_);
lean_inc_ref(v___y_5572_);
lean_inc(v___y_5571_);
lean_inc_ref(v___y_5570_);
v___x_5574_ = l_Lean_Meta_Simp_Result_mkEqSymm(v_expectedType_5558_, v___y_5568_, v___y_5570_, v___y_5571_, v___y_5572_, v___y_5573_);
if (lean_obj_tag(v___x_5574_) == 0)
{
lean_object* v_a_5575_; lean_object* v___x_5576_; 
v_a_5575_ = lean_ctor_get(v___x_5574_, 0);
lean_inc(v_a_5575_);
lean_dec_ref(v___x_5574_);
lean_inc(v___y_5573_);
lean_inc_ref(v___y_5572_);
lean_inc(v___y_5571_);
lean_inc_ref(v___y_5570_);
v___x_5576_ = l_Lean_Meta_Simp_Result_mkEqTrans(v___y_5567_, v_a_5575_, v___y_5570_, v___y_5571_, v___y_5572_, v___y_5573_);
if (lean_obj_tag(v___x_5576_) == 0)
{
lean_object* v_a_5577_; lean_object* v___x_5578_; 
v_a_5577_ = lean_ctor_get(v___x_5576_, 0);
lean_inc(v_a_5577_);
lean_dec_ref(v___x_5576_);
v___x_5578_ = l_Lean_Meta_Simp_Result_mkCast(v_a_5577_, v___y_5569_, v___y_5570_, v___y_5571_, v___y_5572_, v___y_5573_);
return v___x_5578_;
}
else
{
lean_object* v_a_5579_; lean_object* v___x_5581_; uint8_t v_isShared_5582_; uint8_t v_isSharedCheck_5586_; 
lean_dec(v___y_5573_);
lean_dec_ref(v___y_5572_);
lean_dec(v___y_5571_);
lean_dec_ref(v___y_5570_);
lean_dec_ref(v___y_5569_);
v_a_5579_ = lean_ctor_get(v___x_5576_, 0);
v_isSharedCheck_5586_ = !lean_is_exclusive(v___x_5576_);
if (v_isSharedCheck_5586_ == 0)
{
v___x_5581_ = v___x_5576_;
v_isShared_5582_ = v_isSharedCheck_5586_;
goto v_resetjp_5580_;
}
else
{
lean_inc(v_a_5579_);
lean_dec(v___x_5576_);
v___x_5581_ = lean_box(0);
v_isShared_5582_ = v_isSharedCheck_5586_;
goto v_resetjp_5580_;
}
v_resetjp_5580_:
{
lean_object* v___x_5584_; 
if (v_isShared_5582_ == 0)
{
v___x_5584_ = v___x_5581_;
goto v_reusejp_5583_;
}
else
{
lean_object* v_reuseFailAlloc_5585_; 
v_reuseFailAlloc_5585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5585_, 0, v_a_5579_);
v___x_5584_ = v_reuseFailAlloc_5585_;
goto v_reusejp_5583_;
}
v_reusejp_5583_:
{
return v___x_5584_;
}
}
}
}
else
{
lean_object* v_a_5587_; lean_object* v___x_5589_; uint8_t v_isShared_5590_; uint8_t v_isSharedCheck_5594_; 
lean_dec(v___y_5573_);
lean_dec_ref(v___y_5572_);
lean_dec(v___y_5571_);
lean_dec_ref(v___y_5570_);
lean_dec_ref(v___y_5569_);
lean_dec_ref(v___y_5567_);
v_a_5587_ = lean_ctor_get(v___x_5574_, 0);
v_isSharedCheck_5594_ = !lean_is_exclusive(v___x_5574_);
if (v_isSharedCheck_5594_ == 0)
{
v___x_5589_ = v___x_5574_;
v_isShared_5590_ = v_isSharedCheck_5594_;
goto v_resetjp_5588_;
}
else
{
lean_inc(v_a_5587_);
lean_dec(v___x_5574_);
v___x_5589_ = lean_box(0);
v_isShared_5590_ = v_isSharedCheck_5594_;
goto v_resetjp_5588_;
}
v_resetjp_5588_:
{
lean_object* v___x_5592_; 
if (v_isShared_5590_ == 0)
{
v___x_5592_ = v___x_5589_;
goto v_reusejp_5591_;
}
else
{
lean_object* v_reuseFailAlloc_5593_; 
v_reuseFailAlloc_5593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5593_, 0, v_a_5587_);
v___x_5592_ = v_reuseFailAlloc_5593_;
goto v_reusejp_5591_;
}
v_reusejp_5591_:
{
return v___x_5592_;
}
}
}
}
v___jp_5595_:
{
lean_object* v___x_5605_; 
lean_inc(v___y_5604_);
lean_inc_ref(v___y_5603_);
lean_inc(v___y_5602_);
lean_inc_ref(v___y_5601_);
v___x_5605_ = l_Lean_Elab_Tactic_NormCast_derive(v___y_5596_, v___y_5597_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_);
if (lean_obj_tag(v___x_5605_) == 0)
{
lean_object* v_a_5606_; lean_object* v_expr_5607_; lean_object* v___x_5608_; 
v_a_5606_ = lean_ctor_get(v___x_5605_, 0);
lean_inc(v_a_5606_);
lean_dec_ref(v___x_5605_);
v_expr_5607_ = lean_ctor_get(v_a_5606_, 0);
lean_inc(v___y_5604_);
lean_inc_ref(v___y_5603_);
lean_inc(v___y_5602_);
lean_inc_ref(v___y_5601_);
lean_inc_ref(v___y_5598_);
lean_inc_ref(v_expr_5607_);
v___x_5608_ = l_Lean_Meta_isExprDefEq(v_expr_5607_, v___y_5598_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_);
if (lean_obj_tag(v___x_5608_) == 0)
{
lean_object* v_a_5609_; uint8_t v___x_5610_; 
v_a_5609_ = lean_ctor_get(v___x_5608_, 0);
lean_inc(v_a_5609_);
lean_dec_ref(v___x_5608_);
v___x_5610_ = lean_unbox(v_a_5609_);
lean_dec(v_a_5609_);
if (v___x_5610_ == 0)
{
lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v___x_5613_; 
v___x_5611_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__3, &l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__3);
v___x_5612_ = lean_box(0);
lean_inc(v___y_5604_);
lean_inc_ref(v___y_5603_);
lean_inc(v___y_5602_);
lean_inc_ref(v___y_5601_);
lean_inc_ref(v___y_5600_);
lean_inc_ref(v_expr_5607_);
v___x_5613_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_5611_, v___y_5598_, v_expr_5607_, v___y_5600_, v___x_5612_, v___y_5601_, v___y_5602_, v___y_5603_, v___y_5604_);
if (lean_obj_tag(v___x_5613_) == 0)
{
lean_dec_ref(v___x_5613_);
v___y_5567_ = v_a_5606_;
v___y_5568_ = v___y_5599_;
v___y_5569_ = v___y_5600_;
v___y_5570_ = v___y_5601_;
v___y_5571_ = v___y_5602_;
v___y_5572_ = v___y_5603_;
v___y_5573_ = v___y_5604_;
goto v___jp_5566_;
}
else
{
lean_object* v_a_5614_; lean_object* v___x_5616_; uint8_t v_isShared_5617_; uint8_t v_isSharedCheck_5621_; 
lean_dec(v_a_5606_);
lean_dec(v___y_5604_);
lean_dec_ref(v___y_5603_);
lean_dec(v___y_5602_);
lean_dec_ref(v___y_5601_);
lean_dec_ref(v___y_5600_);
lean_dec_ref(v___y_5599_);
lean_dec_ref(v_expectedType_5558_);
v_a_5614_ = lean_ctor_get(v___x_5613_, 0);
v_isSharedCheck_5621_ = !lean_is_exclusive(v___x_5613_);
if (v_isSharedCheck_5621_ == 0)
{
v___x_5616_ = v___x_5613_;
v_isShared_5617_ = v_isSharedCheck_5621_;
goto v_resetjp_5615_;
}
else
{
lean_inc(v_a_5614_);
lean_dec(v___x_5613_);
v___x_5616_ = lean_box(0);
v_isShared_5617_ = v_isSharedCheck_5621_;
goto v_resetjp_5615_;
}
v_resetjp_5615_:
{
lean_object* v___x_5619_; 
if (v_isShared_5617_ == 0)
{
v___x_5619_ = v___x_5616_;
goto v_reusejp_5618_;
}
else
{
lean_object* v_reuseFailAlloc_5620_; 
v_reuseFailAlloc_5620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5620_, 0, v_a_5614_);
v___x_5619_ = v_reuseFailAlloc_5620_;
goto v_reusejp_5618_;
}
v_reusejp_5618_:
{
return v___x_5619_;
}
}
}
}
else
{
lean_dec_ref(v___y_5598_);
v___y_5567_ = v_a_5606_;
v___y_5568_ = v___y_5599_;
v___y_5569_ = v___y_5600_;
v___y_5570_ = v___y_5601_;
v___y_5571_ = v___y_5602_;
v___y_5572_ = v___y_5603_;
v___y_5573_ = v___y_5604_;
goto v___jp_5566_;
}
}
else
{
lean_object* v_a_5622_; lean_object* v___x_5624_; uint8_t v_isShared_5625_; uint8_t v_isSharedCheck_5629_; 
lean_dec(v_a_5606_);
lean_dec(v___y_5604_);
lean_dec_ref(v___y_5603_);
lean_dec(v___y_5602_);
lean_dec_ref(v___y_5601_);
lean_dec_ref(v___y_5600_);
lean_dec_ref(v___y_5599_);
lean_dec_ref(v___y_5598_);
lean_dec_ref(v_expectedType_5558_);
v_a_5622_ = lean_ctor_get(v___x_5608_, 0);
v_isSharedCheck_5629_ = !lean_is_exclusive(v___x_5608_);
if (v_isSharedCheck_5629_ == 0)
{
v___x_5624_ = v___x_5608_;
v_isShared_5625_ = v_isSharedCheck_5629_;
goto v_resetjp_5623_;
}
else
{
lean_inc(v_a_5622_);
lean_dec(v___x_5608_);
v___x_5624_ = lean_box(0);
v_isShared_5625_ = v_isSharedCheck_5629_;
goto v_resetjp_5623_;
}
v_resetjp_5623_:
{
lean_object* v___x_5627_; 
if (v_isShared_5625_ == 0)
{
v___x_5627_ = v___x_5624_;
goto v_reusejp_5626_;
}
else
{
lean_object* v_reuseFailAlloc_5628_; 
v_reuseFailAlloc_5628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5628_, 0, v_a_5622_);
v___x_5627_ = v_reuseFailAlloc_5628_;
goto v_reusejp_5626_;
}
v_reusejp_5626_:
{
return v___x_5627_;
}
}
}
}
else
{
lean_object* v_a_5630_; lean_object* v___x_5632_; uint8_t v_isShared_5633_; uint8_t v_isSharedCheck_5637_; 
lean_dec(v___y_5604_);
lean_dec_ref(v___y_5603_);
lean_dec(v___y_5602_);
lean_dec_ref(v___y_5601_);
lean_dec_ref(v___y_5600_);
lean_dec_ref(v___y_5599_);
lean_dec_ref(v___y_5598_);
lean_dec_ref(v_expectedType_5558_);
v_a_5630_ = lean_ctor_get(v___x_5605_, 0);
v_isSharedCheck_5637_ = !lean_is_exclusive(v___x_5605_);
if (v_isSharedCheck_5637_ == 0)
{
v___x_5632_ = v___x_5605_;
v_isShared_5633_ = v_isSharedCheck_5637_;
goto v_resetjp_5631_;
}
else
{
lean_inc(v_a_5630_);
lean_dec(v___x_5605_);
v___x_5632_ = lean_box(0);
v_isShared_5633_ = v_isSharedCheck_5637_;
goto v_resetjp_5631_;
}
v_resetjp_5631_:
{
lean_object* v___x_5635_; 
if (v_isShared_5633_ == 0)
{
v___x_5635_ = v___x_5632_;
goto v_reusejp_5634_;
}
else
{
lean_object* v_reuseFailAlloc_5636_; 
v_reuseFailAlloc_5636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5636_, 0, v_a_5630_);
v___x_5635_ = v_reuseFailAlloc_5636_;
goto v_reusejp_5634_;
}
v_reusejp_5634_:
{
return v___x_5635_;
}
}
}
}
v___jp_5638_:
{
lean_object* v___x_5645_; lean_object* v___x_5646_; uint8_t v___x_5647_; uint8_t v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; 
v___x_5645_ = lean_unsigned_to_nat(100000u);
v___x_5646_ = lean_unsigned_to_nat(2u);
v___x_5647_ = 0;
v___x_5648_ = 0;
v___x_5649_ = lean_box(0);
v___x_5650_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_5650_, 0, v___x_5645_);
lean_ctor_set(v___x_5650_, 1, v___x_5646_);
lean_ctor_set(v___x_5650_, 2, v___x_5649_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3, v___x_5647_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 1, v___x_5556_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 2, v___x_5647_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 3, v___x_5647_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 4, v___x_5647_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 5, v___x_5647_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 6, v___x_5648_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 7, v___x_5647_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 8, v___x_5647_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 9, v___x_5647_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 10, v___x_5647_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 11, v___x_5647_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 12, v___x_5556_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 13, v___x_5556_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 14, v___x_5647_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 15, v___x_5647_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 16, v___x_5647_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 17, v___x_5556_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 18, v___x_5556_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 19, v___x_5556_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 20, v___x_5556_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 21, v___x_5556_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 22, v___x_5556_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 23, v___x_5556_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 24, v___x_5556_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 25, v___x_5556_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 26, v___x_5647_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 27, v___x_5647_);
lean_ctor_set_uint8(v___x_5650_, sizeof(void*)*3 + 28, v___x_5647_);
lean_inc(v___y_5644_);
lean_inc_ref(v___y_5643_);
lean_inc(v___y_5642_);
lean_inc_ref(v___y_5641_);
lean_inc_ref(v___x_5650_);
lean_inc_ref(v_expectedType_5558_);
v___x_5651_ = l_Lean_Elab_Tactic_NormCast_derive(v_expectedType_5558_, v___x_5650_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_);
if (lean_obj_tag(v___x_5651_) == 0)
{
lean_object* v_a_5652_; lean_object* v_expr_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; 
v_a_5652_ = lean_ctor_get(v___x_5651_, 0);
lean_inc(v_a_5652_);
lean_dec_ref(v___x_5651_);
v_expr_5653_ = lean_ctor_get(v_a_5652_, 0);
lean_inc_ref(v_expr_5653_);
lean_inc_ref(v_expr_5653_);
v___x_5654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5654_, 0, v_expr_5653_);
lean_inc(v___y_5644_);
lean_inc_ref(v___y_5643_);
lean_inc(v___y_5642_);
lean_inc_ref(v___y_5641_);
lean_inc(v___y_5640_);
lean_inc_ref(v___y_5639_);
v___x_5655_ = l_Lean_Elab_Term_elabTerm(v___x_5557_, v___x_5654_, v___x_5556_, v___x_5556_, v___y_5639_, v___y_5640_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_);
if (lean_obj_tag(v___x_5655_) == 0)
{
lean_object* v_a_5656_; uint8_t v___x_5657_; lean_object* v___x_5658_; 
v_a_5656_ = lean_ctor_get(v___x_5655_, 0);
lean_inc(v_a_5656_);
lean_dec_ref(v___x_5655_);
v___x_5657_ = 0;
lean_inc(v___y_5644_);
lean_inc_ref(v___y_5643_);
lean_inc(v___y_5642_);
lean_inc_ref(v___y_5641_);
lean_inc(v___y_5640_);
lean_inc_ref(v___y_5639_);
v___x_5658_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_5657_, v___x_5647_, v___y_5639_, v___y_5640_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_);
if (lean_obj_tag(v___x_5658_) == 0)
{
lean_object* v___x_5659_; 
lean_dec_ref(v___x_5658_);
lean_inc(v___y_5644_);
lean_inc_ref(v___y_5643_);
lean_inc(v___y_5642_);
lean_inc_ref(v___y_5641_);
lean_inc(v_a_5656_);
v___x_5659_ = lean_infer_type(v_a_5656_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_);
if (lean_obj_tag(v___x_5659_) == 0)
{
lean_object* v_a_5660_; lean_object* v___x_5661_; lean_object* v_a_5662_; uint8_t v___x_5663_; 
v_a_5660_ = lean_ctor_get(v___x_5659_, 0);
lean_inc(v_a_5660_);
lean_dec_ref(v___x_5659_);
v___x_5661_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg(v_a_5660_, v___y_5642_);
v_a_5662_ = lean_ctor_get(v___x_5661_, 0);
lean_inc(v_a_5662_);
lean_dec_ref(v___x_5661_);
v___x_5663_ = l_Lean_Expr_hasExprMVar(v_a_5662_);
if (v___x_5663_ == 0)
{
lean_dec(v___y_5640_);
lean_dec_ref(v___y_5639_);
v___y_5596_ = v_a_5662_;
v___y_5597_ = v___x_5650_;
v___y_5598_ = v_expr_5653_;
v___y_5599_ = v_a_5652_;
v___y_5600_ = v_a_5656_;
v___y_5601_ = v___y_5641_;
v___y_5602_ = v___y_5642_;
v___y_5603_ = v___y_5643_;
v___y_5604_ = v___y_5644_;
goto v___jp_5595_;
}
else
{
lean_object* v___x_5664_; 
v___x_5664_ = l_Lean_Elab_Term_tryPostpone(v___y_5639_, v___y_5640_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_);
lean_dec(v___y_5640_);
lean_dec_ref(v___y_5639_);
if (lean_obj_tag(v___x_5664_) == 0)
{
lean_dec_ref(v___x_5664_);
v___y_5596_ = v_a_5662_;
v___y_5597_ = v___x_5650_;
v___y_5598_ = v_expr_5653_;
v___y_5599_ = v_a_5652_;
v___y_5600_ = v_a_5656_;
v___y_5601_ = v___y_5641_;
v___y_5602_ = v___y_5642_;
v___y_5603_ = v___y_5643_;
v___y_5604_ = v___y_5644_;
goto v___jp_5595_;
}
else
{
lean_object* v_a_5665_; lean_object* v___x_5667_; uint8_t v_isShared_5668_; uint8_t v_isSharedCheck_5672_; 
lean_dec(v_a_5662_);
lean_dec(v_a_5656_);
lean_dec_ref(v_expr_5653_);
lean_dec(v_a_5652_);
lean_dec_ref(v___x_5650_);
lean_dec(v___y_5644_);
lean_dec_ref(v___y_5643_);
lean_dec(v___y_5642_);
lean_dec_ref(v___y_5641_);
lean_dec_ref(v_expectedType_5558_);
v_a_5665_ = lean_ctor_get(v___x_5664_, 0);
v_isSharedCheck_5672_ = !lean_is_exclusive(v___x_5664_);
if (v_isSharedCheck_5672_ == 0)
{
v___x_5667_ = v___x_5664_;
v_isShared_5668_ = v_isSharedCheck_5672_;
goto v_resetjp_5666_;
}
else
{
lean_inc(v_a_5665_);
lean_dec(v___x_5664_);
v___x_5667_ = lean_box(0);
v_isShared_5668_ = v_isSharedCheck_5672_;
goto v_resetjp_5666_;
}
v_resetjp_5666_:
{
lean_object* v___x_5670_; 
if (v_isShared_5668_ == 0)
{
v___x_5670_ = v___x_5667_;
goto v_reusejp_5669_;
}
else
{
lean_object* v_reuseFailAlloc_5671_; 
v_reuseFailAlloc_5671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5671_, 0, v_a_5665_);
v___x_5670_ = v_reuseFailAlloc_5671_;
goto v_reusejp_5669_;
}
v_reusejp_5669_:
{
return v___x_5670_;
}
}
}
}
}
else
{
lean_dec(v_a_5656_);
lean_dec_ref(v_expr_5653_);
lean_dec(v_a_5652_);
lean_dec_ref(v___x_5650_);
lean_dec(v___y_5644_);
lean_dec_ref(v___y_5643_);
lean_dec(v___y_5642_);
lean_dec_ref(v___y_5641_);
lean_dec(v___y_5640_);
lean_dec_ref(v___y_5639_);
lean_dec_ref(v_expectedType_5558_);
return v___x_5659_;
}
}
else
{
lean_object* v_a_5673_; lean_object* v___x_5675_; uint8_t v_isShared_5676_; uint8_t v_isSharedCheck_5680_; 
lean_dec(v_a_5656_);
lean_dec_ref(v_expr_5653_);
lean_dec(v_a_5652_);
lean_dec_ref(v___x_5650_);
lean_dec(v___y_5644_);
lean_dec_ref(v___y_5643_);
lean_dec(v___y_5642_);
lean_dec_ref(v___y_5641_);
lean_dec(v___y_5640_);
lean_dec_ref(v___y_5639_);
lean_dec_ref(v_expectedType_5558_);
v_a_5673_ = lean_ctor_get(v___x_5658_, 0);
v_isSharedCheck_5680_ = !lean_is_exclusive(v___x_5658_);
if (v_isSharedCheck_5680_ == 0)
{
v___x_5675_ = v___x_5658_;
v_isShared_5676_ = v_isSharedCheck_5680_;
goto v_resetjp_5674_;
}
else
{
lean_inc(v_a_5673_);
lean_dec(v___x_5658_);
v___x_5675_ = lean_box(0);
v_isShared_5676_ = v_isSharedCheck_5680_;
goto v_resetjp_5674_;
}
v_resetjp_5674_:
{
lean_object* v___x_5678_; 
if (v_isShared_5676_ == 0)
{
v___x_5678_ = v___x_5675_;
goto v_reusejp_5677_;
}
else
{
lean_object* v_reuseFailAlloc_5679_; 
v_reuseFailAlloc_5679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5679_, 0, v_a_5673_);
v___x_5678_ = v_reuseFailAlloc_5679_;
goto v_reusejp_5677_;
}
v_reusejp_5677_:
{
return v___x_5678_;
}
}
}
}
else
{
lean_dec_ref(v_expr_5653_);
lean_dec(v_a_5652_);
lean_dec_ref(v___x_5650_);
lean_dec(v___y_5644_);
lean_dec_ref(v___y_5643_);
lean_dec(v___y_5642_);
lean_dec_ref(v___y_5641_);
lean_dec(v___y_5640_);
lean_dec_ref(v___y_5639_);
lean_dec_ref(v_expectedType_5558_);
return v___x_5655_;
}
}
else
{
lean_object* v_a_5681_; lean_object* v___x_5683_; uint8_t v_isShared_5684_; uint8_t v_isSharedCheck_5688_; 
lean_dec_ref(v___x_5650_);
lean_dec(v___y_5644_);
lean_dec_ref(v___y_5643_);
lean_dec(v___y_5642_);
lean_dec_ref(v___y_5641_);
lean_dec(v___y_5640_);
lean_dec_ref(v___y_5639_);
lean_dec_ref(v_expectedType_5558_);
lean_dec(v___x_5557_);
v_a_5681_ = lean_ctor_get(v___x_5651_, 0);
v_isSharedCheck_5688_ = !lean_is_exclusive(v___x_5651_);
if (v_isSharedCheck_5688_ == 0)
{
v___x_5683_ = v___x_5651_;
v_isShared_5684_ = v_isSharedCheck_5688_;
goto v_resetjp_5682_;
}
else
{
lean_inc(v_a_5681_);
lean_dec(v___x_5651_);
v___x_5683_ = lean_box(0);
v_isShared_5684_ = v_isSharedCheck_5688_;
goto v_resetjp_5682_;
}
v_resetjp_5682_:
{
lean_object* v___x_5686_; 
if (v_isShared_5684_ == 0)
{
v___x_5686_ = v___x_5683_;
goto v_reusejp_5685_;
}
else
{
lean_object* v_reuseFailAlloc_5687_; 
v_reuseFailAlloc_5687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5687_, 0, v_a_5681_);
v___x_5686_ = v_reuseFailAlloc_5687_;
goto v_reusejp_5685_;
}
v_reusejp_5685_:
{
return v___x_5686_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___boxed(lean_object* v___x_5701_, lean_object* v___x_5702_, lean_object* v_expectedType_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_){
_start:
{
uint8_t v___x_4156__boxed_5711_; lean_object* v_res_5712_; 
v___x_4156__boxed_5711_ = lean_unbox(v___x_5701_);
v_res_5712_ = l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0(v___x_4156__boxed_5711_, v___x_5702_, v_expectedType_5703_, v___y_5704_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_, v___y_5709_);
return v_res_5712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast(lean_object* v_stx_5717_, lean_object* v_expectedType_x3f_5718_, lean_object* v_a_5719_, lean_object* v_a_5720_, lean_object* v_a_5721_, lean_object* v_a_5722_, lean_object* v_a_5723_, lean_object* v_a_5724_){
_start:
{
lean_object* v___x_5726_; uint8_t v___x_5727_; 
v___x_5726_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabModCast___closed__1));
lean_inc(v_stx_5717_);
v___x_5727_ = l_Lean_Syntax_isOfKind(v_stx_5717_, v___x_5726_);
if (v___x_5727_ == 0)
{
lean_object* v___x_5728_; 
lean_dec(v_a_5724_);
lean_dec_ref(v_a_5723_);
lean_dec(v_a_5722_);
lean_dec_ref(v_a_5721_);
lean_dec(v_a_5720_);
lean_dec_ref(v_a_5719_);
lean_dec(v_expectedType_x3f_5718_);
lean_dec(v_stx_5717_);
v___x_5728_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg();
return v___x_5728_;
}
else
{
lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___f_5732_; lean_object* v___x_5733_; 
v___x_5729_ = lean_unsigned_to_nat(1u);
v___x_5730_ = l_Lean_Syntax_getArg(v_stx_5717_, v___x_5729_);
lean_dec(v_stx_5717_);
v___x_5731_ = lean_box(v___x_5727_);
v___f_5732_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___boxed), 10, 2);
lean_closure_set(v___f_5732_, 0, v___x_5731_);
lean_closure_set(v___f_5732_, 1, v___x_5730_);
v___x_5733_ = l_Lean_Elab_Term_withExpectedType(v_expectedType_x3f_5718_, v___f_5732_, v_a_5719_, v_a_5720_, v_a_5721_, v_a_5722_, v_a_5723_, v_a_5724_);
return v___x_5733_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___boxed(lean_object* v_stx_5734_, lean_object* v_expectedType_x3f_5735_, lean_object* v_a_5736_, lean_object* v_a_5737_, lean_object* v_a_5738_, lean_object* v_a_5739_, lean_object* v_a_5740_, lean_object* v_a_5741_, lean_object* v_a_5742_){
_start:
{
lean_object* v_res_5743_; 
v_res_5743_ = l_Lean_Elab_Tactic_NormCast_elabModCast(v_stx_5734_, v_expectedType_x3f_5735_, v_a_5736_, v_a_5737_, v_a_5738_, v_a_5739_, v_a_5740_, v_a_5741_);
return v_res_5743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1(){
_start:
{
lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; 
v___x_5752_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5753_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabModCast___closed__1));
v___x_5754_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1));
v___x_5755_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_elabModCast___boxed), 9, 0);
v___x_5756_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5752_, v___x_5753_, v___x_5754_, v___x_5755_);
return v___x_5756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___boxed(lean_object* v_a_5757_){
_start:
{
lean_object* v_res_5758_; 
v_res_5758_ = l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1();
return v_res_5758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3(){
_start:
{
lean_object* v___x_5785_; lean_object* v___x_5786_; lean_object* v___x_5787_; 
v___x_5785_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1));
v___x_5786_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__6));
v___x_5787_ = l_Lean_addBuiltinDeclarationRanges(v___x_5785_, v___x_5786_);
return v___x_5787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___boxed(lean_object* v_a_5788_){
_start:
{
lean_object* v_res_5789_; 
v_res_5789_ = l_Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3();
return v_res_5789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___lam__0(lean_object* v_cfg_5790_, lean_object* v___y_5791_, lean_object* v___y_5792_, lean_object* v___y_5793_, lean_object* v___y_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_, lean_object* v___y_5797_, lean_object* v___y_5798_){
_start:
{
lean_object* v___x_5800_; 
v___x_5800_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_5792_, v___y_5795_, v___y_5796_, v___y_5797_, v___y_5798_);
if (lean_obj_tag(v___x_5800_) == 0)
{
lean_object* v_a_5801_; lean_object* v___x_5802_; 
v_a_5801_ = lean_ctor_get(v___x_5800_, 0);
lean_inc(v_a_5801_);
lean_dec_ref(v___x_5800_);
lean_inc(v_a_5801_);
v___x_5802_ = l_Lean_MVarId_getType(v_a_5801_, v___y_5795_, v___y_5796_, v___y_5797_, v___y_5798_);
if (lean_obj_tag(v___x_5802_) == 0)
{
lean_object* v_a_5803_; lean_object* v___x_5804_; lean_object* v_a_5805_; lean_object* v___x_5806_; 
v_a_5803_ = lean_ctor_get(v___x_5802_, 0);
lean_inc(v_a_5803_);
lean_dec_ref(v___x_5802_);
v___x_5804_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_a_5803_, v___y_5796_);
v_a_5805_ = lean_ctor_get(v___x_5804_, 0);
lean_inc(v_a_5805_);
lean_dec_ref(v___x_5804_);
lean_inc(v___y_5798_);
lean_inc_ref(v___y_5797_);
lean_inc(v___y_5796_);
lean_inc_ref(v___y_5795_);
lean_inc(v_a_5805_);
v___x_5806_ = l_Lean_Elab_Tactic_NormCast_derive(v_a_5805_, v_cfg_5790_, v___y_5795_, v___y_5796_, v___y_5797_, v___y_5798_);
if (lean_obj_tag(v___x_5806_) == 0)
{
lean_object* v_a_5807_; lean_object* v___x_5808_; 
v_a_5807_ = lean_ctor_get(v___x_5806_, 0);
lean_inc(v_a_5807_);
lean_dec_ref(v___x_5806_);
lean_inc(v___y_5798_);
lean_inc_ref(v___y_5797_);
lean_inc(v___y_5796_);
lean_inc_ref(v___y_5795_);
v___x_5808_ = l_Lean_Meta_applySimpResultToTarget(v_a_5801_, v_a_5805_, v_a_5807_, v___y_5795_, v___y_5796_, v___y_5797_, v___y_5798_);
lean_dec(v_a_5805_);
if (lean_obj_tag(v___x_5808_) == 0)
{
lean_object* v_a_5809_; lean_object* v___x_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; 
v_a_5809_ = lean_ctor_get(v___x_5808_, 0);
lean_inc(v_a_5809_);
lean_dec_ref(v___x_5808_);
v___x_5810_ = lean_box(0);
v___x_5811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5811_, 0, v_a_5809_);
lean_ctor_set(v___x_5811_, 1, v___x_5810_);
v___x_5812_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_5811_, v___y_5792_, v___y_5795_, v___y_5796_, v___y_5797_, v___y_5798_);
lean_dec(v___y_5798_);
lean_dec_ref(v___y_5797_);
lean_dec(v___y_5796_);
lean_dec_ref(v___y_5795_);
return v___x_5812_;
}
else
{
lean_object* v_a_5813_; lean_object* v___x_5815_; uint8_t v_isShared_5816_; uint8_t v_isSharedCheck_5820_; 
lean_dec(v___y_5798_);
lean_dec_ref(v___y_5797_);
lean_dec(v___y_5796_);
lean_dec_ref(v___y_5795_);
v_a_5813_ = lean_ctor_get(v___x_5808_, 0);
v_isSharedCheck_5820_ = !lean_is_exclusive(v___x_5808_);
if (v_isSharedCheck_5820_ == 0)
{
v___x_5815_ = v___x_5808_;
v_isShared_5816_ = v_isSharedCheck_5820_;
goto v_resetjp_5814_;
}
else
{
lean_inc(v_a_5813_);
lean_dec(v___x_5808_);
v___x_5815_ = lean_box(0);
v_isShared_5816_ = v_isSharedCheck_5820_;
goto v_resetjp_5814_;
}
v_resetjp_5814_:
{
lean_object* v___x_5818_; 
if (v_isShared_5816_ == 0)
{
v___x_5818_ = v___x_5815_;
goto v_reusejp_5817_;
}
else
{
lean_object* v_reuseFailAlloc_5819_; 
v_reuseFailAlloc_5819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5819_, 0, v_a_5813_);
v___x_5818_ = v_reuseFailAlloc_5819_;
goto v_reusejp_5817_;
}
v_reusejp_5817_:
{
return v___x_5818_;
}
}
}
}
else
{
lean_object* v_a_5821_; lean_object* v___x_5823_; uint8_t v_isShared_5824_; uint8_t v_isSharedCheck_5828_; 
lean_dec(v_a_5805_);
lean_dec(v_a_5801_);
lean_dec(v___y_5798_);
lean_dec_ref(v___y_5797_);
lean_dec(v___y_5796_);
lean_dec_ref(v___y_5795_);
v_a_5821_ = lean_ctor_get(v___x_5806_, 0);
v_isSharedCheck_5828_ = !lean_is_exclusive(v___x_5806_);
if (v_isSharedCheck_5828_ == 0)
{
v___x_5823_ = v___x_5806_;
v_isShared_5824_ = v_isSharedCheck_5828_;
goto v_resetjp_5822_;
}
else
{
lean_inc(v_a_5821_);
lean_dec(v___x_5806_);
v___x_5823_ = lean_box(0);
v_isShared_5824_ = v_isSharedCheck_5828_;
goto v_resetjp_5822_;
}
v_resetjp_5822_:
{
lean_object* v___x_5826_; 
if (v_isShared_5824_ == 0)
{
v___x_5826_ = v___x_5823_;
goto v_reusejp_5825_;
}
else
{
lean_object* v_reuseFailAlloc_5827_; 
v_reuseFailAlloc_5827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5827_, 0, v_a_5821_);
v___x_5826_ = v_reuseFailAlloc_5827_;
goto v_reusejp_5825_;
}
v_reusejp_5825_:
{
return v___x_5826_;
}
}
}
}
else
{
lean_object* v_a_5829_; lean_object* v___x_5831_; uint8_t v_isShared_5832_; uint8_t v_isSharedCheck_5836_; 
lean_dec(v_a_5801_);
lean_dec(v___y_5798_);
lean_dec_ref(v___y_5797_);
lean_dec(v___y_5796_);
lean_dec_ref(v___y_5795_);
lean_dec_ref(v_cfg_5790_);
v_a_5829_ = lean_ctor_get(v___x_5802_, 0);
v_isSharedCheck_5836_ = !lean_is_exclusive(v___x_5802_);
if (v_isSharedCheck_5836_ == 0)
{
v___x_5831_ = v___x_5802_;
v_isShared_5832_ = v_isSharedCheck_5836_;
goto v_resetjp_5830_;
}
else
{
lean_inc(v_a_5829_);
lean_dec(v___x_5802_);
v___x_5831_ = lean_box(0);
v_isShared_5832_ = v_isSharedCheck_5836_;
goto v_resetjp_5830_;
}
v_resetjp_5830_:
{
lean_object* v___x_5834_; 
if (v_isShared_5832_ == 0)
{
v___x_5834_ = v___x_5831_;
goto v_reusejp_5833_;
}
else
{
lean_object* v_reuseFailAlloc_5835_; 
v_reuseFailAlloc_5835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5835_, 0, v_a_5829_);
v___x_5834_ = v_reuseFailAlloc_5835_;
goto v_reusejp_5833_;
}
v_reusejp_5833_:
{
return v___x_5834_;
}
}
}
}
else
{
lean_object* v_a_5837_; lean_object* v___x_5839_; uint8_t v_isShared_5840_; uint8_t v_isSharedCheck_5844_; 
lean_dec(v___y_5798_);
lean_dec_ref(v___y_5797_);
lean_dec(v___y_5796_);
lean_dec_ref(v___y_5795_);
lean_dec_ref(v_cfg_5790_);
v_a_5837_ = lean_ctor_get(v___x_5800_, 0);
v_isSharedCheck_5844_ = !lean_is_exclusive(v___x_5800_);
if (v_isSharedCheck_5844_ == 0)
{
v___x_5839_ = v___x_5800_;
v_isShared_5840_ = v_isSharedCheck_5844_;
goto v_resetjp_5838_;
}
else
{
lean_inc(v_a_5837_);
lean_dec(v___x_5800_);
v___x_5839_ = lean_box(0);
v_isShared_5840_ = v_isSharedCheck_5844_;
goto v_resetjp_5838_;
}
v_resetjp_5838_:
{
lean_object* v___x_5842_; 
if (v_isShared_5840_ == 0)
{
v___x_5842_ = v___x_5839_;
goto v_reusejp_5841_;
}
else
{
lean_object* v_reuseFailAlloc_5843_; 
v_reuseFailAlloc_5843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5843_, 0, v_a_5837_);
v___x_5842_ = v_reuseFailAlloc_5843_;
goto v_reusejp_5841_;
}
v_reusejp_5841_:
{
return v___x_5842_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___lam__0___boxed(lean_object* v_cfg_5845_, lean_object* v___y_5846_, lean_object* v___y_5847_, lean_object* v___y_5848_, lean_object* v___y_5849_, lean_object* v___y_5850_, lean_object* v___y_5851_, lean_object* v___y_5852_, lean_object* v___y_5853_, lean_object* v___y_5854_){
_start:
{
lean_object* v_res_5855_; 
v_res_5855_ = l_Lean_Elab_Tactic_NormCast_normCastTarget___lam__0(v_cfg_5845_, v___y_5846_, v___y_5847_, v___y_5848_, v___y_5849_, v___y_5850_, v___y_5851_, v___y_5852_, v___y_5853_);
lean_dec(v___y_5849_);
lean_dec_ref(v___y_5848_);
lean_dec(v___y_5847_);
lean_dec_ref(v___y_5846_);
return v_res_5855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget(lean_object* v_cfg_5856_, lean_object* v_a_5857_, lean_object* v_a_5858_, lean_object* v_a_5859_, lean_object* v_a_5860_, lean_object* v_a_5861_, lean_object* v_a_5862_, lean_object* v_a_5863_, lean_object* v_a_5864_){
_start:
{
lean_object* v___f_5866_; lean_object* v___x_5867_; 
v___f_5866_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_normCastTarget___lam__0___boxed), 10, 1);
lean_closure_set(v___f_5866_, 0, v_cfg_5856_);
v___x_5867_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_5866_, v_a_5857_, v_a_5858_, v_a_5859_, v_a_5860_, v_a_5861_, v_a_5862_, v_a_5863_, v_a_5864_);
return v___x_5867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___boxed(lean_object* v_cfg_5868_, lean_object* v_a_5869_, lean_object* v_a_5870_, lean_object* v_a_5871_, lean_object* v_a_5872_, lean_object* v_a_5873_, lean_object* v_a_5874_, lean_object* v_a_5875_, lean_object* v_a_5876_, lean_object* v_a_5877_){
_start:
{
lean_object* v_res_5878_; 
v_res_5878_ = l_Lean_Elab_Tactic_NormCast_normCastTarget(v_cfg_5868_, v_a_5869_, v_a_5870_, v_a_5871_, v_a_5872_, v_a_5873_, v_a_5874_, v_a_5875_, v_a_5876_);
return v_res_5878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp___lam__0(lean_object* v_fvarId_5879_, lean_object* v_cfg_5880_, lean_object* v___y_5881_, lean_object* v___y_5882_, lean_object* v___y_5883_, lean_object* v___y_5884_, lean_object* v___y_5885_, lean_object* v___y_5886_, lean_object* v___y_5887_, lean_object* v___y_5888_){
_start:
{
lean_object* v___x_5890_; 
v___x_5890_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_5882_, v___y_5885_, v___y_5886_, v___y_5887_, v___y_5888_);
if (lean_obj_tag(v___x_5890_) == 0)
{
lean_object* v_a_5891_; lean_object* v___x_5892_; 
v_a_5891_ = lean_ctor_get(v___x_5890_, 0);
lean_inc(v_a_5891_);
lean_dec_ref(v___x_5890_);
lean_inc_ref(v___y_5885_);
lean_inc(v_fvarId_5879_);
v___x_5892_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_5879_, v___y_5885_, v___y_5887_, v___y_5888_);
if (lean_obj_tag(v___x_5892_) == 0)
{
lean_object* v_a_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v_a_5896_; lean_object* v___x_5897_; 
v_a_5893_ = lean_ctor_get(v___x_5892_, 0);
lean_inc(v_a_5893_);
lean_dec_ref(v___x_5892_);
v___x_5894_ = l_Lean_LocalDecl_type(v_a_5893_);
lean_dec(v_a_5893_);
v___x_5895_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v___x_5894_, v___y_5886_);
v_a_5896_ = lean_ctor_get(v___x_5895_, 0);
lean_inc(v_a_5896_);
lean_dec_ref(v___x_5895_);
lean_inc(v___y_5888_);
lean_inc_ref(v___y_5887_);
lean_inc(v___y_5886_);
lean_inc_ref(v___y_5885_);
v___x_5897_ = l_Lean_Elab_Tactic_NormCast_derive(v_a_5896_, v_cfg_5880_, v___y_5885_, v___y_5886_, v___y_5887_, v___y_5888_);
if (lean_obj_tag(v___x_5897_) == 0)
{
lean_object* v_a_5898_; uint8_t v___x_5899_; lean_object* v___x_5900_; 
v_a_5898_ = lean_ctor_get(v___x_5897_, 0);
lean_inc(v_a_5898_);
lean_dec_ref(v___x_5897_);
v___x_5899_ = 0;
lean_inc(v___y_5888_);
lean_inc_ref(v___y_5887_);
lean_inc(v___y_5886_);
lean_inc_ref(v___y_5885_);
v___x_5900_ = l_Lean_Meta_applySimpResultToLocalDecl(v_a_5891_, v_fvarId_5879_, v_a_5898_, v___x_5899_, v___y_5885_, v___y_5886_, v___y_5887_, v___y_5888_);
if (lean_obj_tag(v___x_5900_) == 0)
{
lean_object* v_a_5901_; 
v_a_5901_ = lean_ctor_get(v___x_5900_, 0);
lean_inc(v_a_5901_);
lean_dec_ref(v___x_5900_);
if (lean_obj_tag(v_a_5901_) == 0)
{
lean_object* v___x_5902_; lean_object* v___x_5903_; 
v___x_5902_ = lean_box(0);
v___x_5903_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_5902_, v___y_5882_, v___y_5885_, v___y_5886_, v___y_5887_, v___y_5888_);
lean_dec(v___y_5888_);
lean_dec_ref(v___y_5887_);
lean_dec(v___y_5886_);
lean_dec_ref(v___y_5885_);
return v___x_5903_;
}
else
{
lean_object* v_val_5904_; lean_object* v_snd_5905_; lean_object* v___x_5907_; uint8_t v_isShared_5908_; uint8_t v_isSharedCheck_5914_; 
v_val_5904_ = lean_ctor_get(v_a_5901_, 0);
lean_inc(v_val_5904_);
lean_dec_ref(v_a_5901_);
v_snd_5905_ = lean_ctor_get(v_val_5904_, 1);
v_isSharedCheck_5914_ = !lean_is_exclusive(v_val_5904_);
if (v_isSharedCheck_5914_ == 0)
{
lean_object* v_unused_5915_; 
v_unused_5915_ = lean_ctor_get(v_val_5904_, 0);
lean_dec(v_unused_5915_);
v___x_5907_ = v_val_5904_;
v_isShared_5908_ = v_isSharedCheck_5914_;
goto v_resetjp_5906_;
}
else
{
lean_inc(v_snd_5905_);
lean_dec(v_val_5904_);
v___x_5907_ = lean_box(0);
v_isShared_5908_ = v_isSharedCheck_5914_;
goto v_resetjp_5906_;
}
v_resetjp_5906_:
{
lean_object* v___x_5909_; lean_object* v___x_5911_; 
v___x_5909_ = lean_box(0);
if (v_isShared_5908_ == 0)
{
lean_ctor_set_tag(v___x_5907_, 1);
lean_ctor_set(v___x_5907_, 1, v___x_5909_);
lean_ctor_set(v___x_5907_, 0, v_snd_5905_);
v___x_5911_ = v___x_5907_;
goto v_reusejp_5910_;
}
else
{
lean_object* v_reuseFailAlloc_5913_; 
v_reuseFailAlloc_5913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5913_, 0, v_snd_5905_);
lean_ctor_set(v_reuseFailAlloc_5913_, 1, v___x_5909_);
v___x_5911_ = v_reuseFailAlloc_5913_;
goto v_reusejp_5910_;
}
v_reusejp_5910_:
{
lean_object* v___x_5912_; 
v___x_5912_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_5911_, v___y_5882_, v___y_5885_, v___y_5886_, v___y_5887_, v___y_5888_);
lean_dec(v___y_5888_);
lean_dec_ref(v___y_5887_);
lean_dec(v___y_5886_);
lean_dec_ref(v___y_5885_);
return v___x_5912_;
}
}
}
}
else
{
lean_object* v_a_5916_; lean_object* v___x_5918_; uint8_t v_isShared_5919_; uint8_t v_isSharedCheck_5923_; 
lean_dec(v___y_5888_);
lean_dec_ref(v___y_5887_);
lean_dec(v___y_5886_);
lean_dec_ref(v___y_5885_);
v_a_5916_ = lean_ctor_get(v___x_5900_, 0);
v_isSharedCheck_5923_ = !lean_is_exclusive(v___x_5900_);
if (v_isSharedCheck_5923_ == 0)
{
v___x_5918_ = v___x_5900_;
v_isShared_5919_ = v_isSharedCheck_5923_;
goto v_resetjp_5917_;
}
else
{
lean_inc(v_a_5916_);
lean_dec(v___x_5900_);
v___x_5918_ = lean_box(0);
v_isShared_5919_ = v_isSharedCheck_5923_;
goto v_resetjp_5917_;
}
v_resetjp_5917_:
{
lean_object* v___x_5921_; 
if (v_isShared_5919_ == 0)
{
v___x_5921_ = v___x_5918_;
goto v_reusejp_5920_;
}
else
{
lean_object* v_reuseFailAlloc_5922_; 
v_reuseFailAlloc_5922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5922_, 0, v_a_5916_);
v___x_5921_ = v_reuseFailAlloc_5922_;
goto v_reusejp_5920_;
}
v_reusejp_5920_:
{
return v___x_5921_;
}
}
}
}
else
{
lean_object* v_a_5924_; lean_object* v___x_5926_; uint8_t v_isShared_5927_; uint8_t v_isSharedCheck_5931_; 
lean_dec(v_a_5891_);
lean_dec(v___y_5888_);
lean_dec_ref(v___y_5887_);
lean_dec(v___y_5886_);
lean_dec_ref(v___y_5885_);
lean_dec(v_fvarId_5879_);
v_a_5924_ = lean_ctor_get(v___x_5897_, 0);
v_isSharedCheck_5931_ = !lean_is_exclusive(v___x_5897_);
if (v_isSharedCheck_5931_ == 0)
{
v___x_5926_ = v___x_5897_;
v_isShared_5927_ = v_isSharedCheck_5931_;
goto v_resetjp_5925_;
}
else
{
lean_inc(v_a_5924_);
lean_dec(v___x_5897_);
v___x_5926_ = lean_box(0);
v_isShared_5927_ = v_isSharedCheck_5931_;
goto v_resetjp_5925_;
}
v_resetjp_5925_:
{
lean_object* v___x_5929_; 
if (v_isShared_5927_ == 0)
{
v___x_5929_ = v___x_5926_;
goto v_reusejp_5928_;
}
else
{
lean_object* v_reuseFailAlloc_5930_; 
v_reuseFailAlloc_5930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5930_, 0, v_a_5924_);
v___x_5929_ = v_reuseFailAlloc_5930_;
goto v_reusejp_5928_;
}
v_reusejp_5928_:
{
return v___x_5929_;
}
}
}
}
else
{
lean_object* v_a_5932_; lean_object* v___x_5934_; uint8_t v_isShared_5935_; uint8_t v_isSharedCheck_5939_; 
lean_dec(v_a_5891_);
lean_dec(v___y_5888_);
lean_dec_ref(v___y_5887_);
lean_dec(v___y_5886_);
lean_dec_ref(v___y_5885_);
lean_dec_ref(v_cfg_5880_);
lean_dec(v_fvarId_5879_);
v_a_5932_ = lean_ctor_get(v___x_5892_, 0);
v_isSharedCheck_5939_ = !lean_is_exclusive(v___x_5892_);
if (v_isSharedCheck_5939_ == 0)
{
v___x_5934_ = v___x_5892_;
v_isShared_5935_ = v_isSharedCheck_5939_;
goto v_resetjp_5933_;
}
else
{
lean_inc(v_a_5932_);
lean_dec(v___x_5892_);
v___x_5934_ = lean_box(0);
v_isShared_5935_ = v_isSharedCheck_5939_;
goto v_resetjp_5933_;
}
v_resetjp_5933_:
{
lean_object* v___x_5937_; 
if (v_isShared_5935_ == 0)
{
v___x_5937_ = v___x_5934_;
goto v_reusejp_5936_;
}
else
{
lean_object* v_reuseFailAlloc_5938_; 
v_reuseFailAlloc_5938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5938_, 0, v_a_5932_);
v___x_5937_ = v_reuseFailAlloc_5938_;
goto v_reusejp_5936_;
}
v_reusejp_5936_:
{
return v___x_5937_;
}
}
}
}
else
{
lean_object* v_a_5940_; lean_object* v___x_5942_; uint8_t v_isShared_5943_; uint8_t v_isSharedCheck_5947_; 
lean_dec(v___y_5888_);
lean_dec_ref(v___y_5887_);
lean_dec(v___y_5886_);
lean_dec_ref(v___y_5885_);
lean_dec_ref(v_cfg_5880_);
lean_dec(v_fvarId_5879_);
v_a_5940_ = lean_ctor_get(v___x_5890_, 0);
v_isSharedCheck_5947_ = !lean_is_exclusive(v___x_5890_);
if (v_isSharedCheck_5947_ == 0)
{
v___x_5942_ = v___x_5890_;
v_isShared_5943_ = v_isSharedCheck_5947_;
goto v_resetjp_5941_;
}
else
{
lean_inc(v_a_5940_);
lean_dec(v___x_5890_);
v___x_5942_ = lean_box(0);
v_isShared_5943_ = v_isSharedCheck_5947_;
goto v_resetjp_5941_;
}
v_resetjp_5941_:
{
lean_object* v___x_5945_; 
if (v_isShared_5943_ == 0)
{
v___x_5945_ = v___x_5942_;
goto v_reusejp_5944_;
}
else
{
lean_object* v_reuseFailAlloc_5946_; 
v_reuseFailAlloc_5946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5946_, 0, v_a_5940_);
v___x_5945_ = v_reuseFailAlloc_5946_;
goto v_reusejp_5944_;
}
v_reusejp_5944_:
{
return v___x_5945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp___lam__0___boxed(lean_object* v_fvarId_5948_, lean_object* v_cfg_5949_, lean_object* v___y_5950_, lean_object* v___y_5951_, lean_object* v___y_5952_, lean_object* v___y_5953_, lean_object* v___y_5954_, lean_object* v___y_5955_, lean_object* v___y_5956_, lean_object* v___y_5957_, lean_object* v___y_5958_){
_start:
{
lean_object* v_res_5959_; 
v_res_5959_ = l_Lean_Elab_Tactic_NormCast_normCastHyp___lam__0(v_fvarId_5948_, v_cfg_5949_, v___y_5950_, v___y_5951_, v___y_5952_, v___y_5953_, v___y_5954_, v___y_5955_, v___y_5956_, v___y_5957_);
lean_dec(v___y_5953_);
lean_dec_ref(v___y_5952_);
lean_dec(v___y_5951_);
lean_dec_ref(v___y_5950_);
return v_res_5959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp(lean_object* v_cfg_5960_, lean_object* v_fvarId_5961_, lean_object* v_a_5962_, lean_object* v_a_5963_, lean_object* v_a_5964_, lean_object* v_a_5965_, lean_object* v_a_5966_, lean_object* v_a_5967_, lean_object* v_a_5968_, lean_object* v_a_5969_){
_start:
{
lean_object* v___f_5971_; lean_object* v___x_5972_; 
v___f_5971_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_normCastHyp___lam__0___boxed), 11, 2);
lean_closure_set(v___f_5971_, 0, v_fvarId_5961_);
lean_closure_set(v___f_5971_, 1, v_cfg_5960_);
v___x_5972_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_5971_, v_a_5962_, v_a_5963_, v_a_5964_, v_a_5965_, v_a_5966_, v_a_5967_, v_a_5968_, v_a_5969_);
return v___x_5972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp___boxed(lean_object* v_cfg_5973_, lean_object* v_fvarId_5974_, lean_object* v_a_5975_, lean_object* v_a_5976_, lean_object* v_a_5977_, lean_object* v_a_5978_, lean_object* v_a_5979_, lean_object* v_a_5980_, lean_object* v_a_5981_, lean_object* v_a_5982_, lean_object* v_a_5983_){
_start:
{
lean_object* v_res_5984_; 
v_res_5984_ = l_Lean_Elab_Tactic_NormCast_normCastHyp(v_cfg_5973_, v_fvarId_5974_, v_a_5975_, v_a_5976_, v_a_5977_, v_a_5978_, v_a_5979_, v_a_5980_, v_a_5981_, v_a_5982_);
return v_res_5984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg(){
_start:
{
lean_object* v___x_5986_; lean_object* v___x_5987_; 
v___x_5986_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0);
v___x_5987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5987_, 0, v___x_5986_);
return v___x_5987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg___boxed(lean_object* v___y_5988_){
_start:
{
lean_object* v_res_5989_; 
v_res_5989_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg();
return v_res_5989_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0(lean_object* v_00_u03b1_5990_, lean_object* v___y_5991_, lean_object* v___y_5992_, lean_object* v___y_5993_, lean_object* v___y_5994_, lean_object* v___y_5995_, lean_object* v___y_5996_, lean_object* v___y_5997_, lean_object* v___y_5998_){
_start:
{
lean_object* v___x_6000_; 
v___x_6000_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg();
return v___x_6000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___boxed(lean_object* v_00_u03b1_6001_, lean_object* v___y_6002_, lean_object* v___y_6003_, lean_object* v___y_6004_, lean_object* v___y_6005_, lean_object* v___y_6006_, lean_object* v___y_6007_, lean_object* v___y_6008_, lean_object* v___y_6009_, lean_object* v___y_6010_){
_start:
{
lean_object* v_res_6011_; 
v_res_6011_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0(v_00_u03b1_6001_, v___y_6002_, v___y_6003_, v___y_6004_, v___y_6005_, v___y_6006_, v___y_6007_, v___y_6008_, v___y_6009_);
lean_dec(v___y_6009_);
lean_dec_ref(v___y_6008_);
lean_dec(v___y_6007_);
lean_dec_ref(v___y_6006_);
lean_dec(v___y_6005_);
lean_dec_ref(v___y_6004_);
lean_dec(v___y_6003_);
lean_dec_ref(v___y_6002_);
return v_res_6011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1(lean_object* v_a_6012_, lean_object* v_as_6013_, size_t v_i_6014_, size_t v_stop_6015_, lean_object* v_b_6016_, lean_object* v___y_6017_, lean_object* v___y_6018_, lean_object* v___y_6019_, lean_object* v___y_6020_, lean_object* v___y_6021_, lean_object* v___y_6022_, lean_object* v___y_6023_, lean_object* v___y_6024_){
_start:
{
uint8_t v___x_6026_; 
v___x_6026_ = lean_usize_dec_eq(v_i_6014_, v_stop_6015_);
if (v___x_6026_ == 0)
{
lean_object* v___x_6027_; lean_object* v___x_6028_; 
v___x_6027_ = lean_array_uget_borrowed(v_as_6013_, v_i_6014_);
lean_inc(v___y_6024_);
lean_inc_ref(v___y_6023_);
lean_inc(v___y_6022_);
lean_inc_ref(v___y_6021_);
lean_inc(v___y_6020_);
lean_inc_ref(v___y_6019_);
lean_inc(v___y_6018_);
lean_inc_ref(v___y_6017_);
lean_inc(v___x_6027_);
lean_inc_ref(v_a_6012_);
v___x_6028_ = l_Lean_Elab_Tactic_NormCast_normCastHyp(v_a_6012_, v___x_6027_, v___y_6017_, v___y_6018_, v___y_6019_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_, v___y_6024_);
if (lean_obj_tag(v___x_6028_) == 0)
{
lean_object* v_a_6029_; size_t v___x_6030_; size_t v___x_6031_; 
v_a_6029_ = lean_ctor_get(v___x_6028_, 0);
lean_inc(v_a_6029_);
lean_dec_ref(v___x_6028_);
v___x_6030_ = ((size_t)1ULL);
v___x_6031_ = lean_usize_add(v_i_6014_, v___x_6030_);
v_i_6014_ = v___x_6031_;
v_b_6016_ = v_a_6029_;
goto _start;
}
else
{
lean_dec(v___y_6024_);
lean_dec_ref(v___y_6023_);
lean_dec(v___y_6022_);
lean_dec_ref(v___y_6021_);
lean_dec(v___y_6020_);
lean_dec_ref(v___y_6019_);
lean_dec(v___y_6018_);
lean_dec_ref(v___y_6017_);
lean_dec_ref(v_a_6012_);
return v___x_6028_;
}
}
else
{
lean_object* v___x_6033_; 
lean_dec(v___y_6024_);
lean_dec_ref(v___y_6023_);
lean_dec(v___y_6022_);
lean_dec_ref(v___y_6021_);
lean_dec(v___y_6020_);
lean_dec_ref(v___y_6019_);
lean_dec(v___y_6018_);
lean_dec_ref(v___y_6017_);
lean_dec_ref(v_a_6012_);
v___x_6033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6033_, 0, v_b_6016_);
return v___x_6033_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1___boxed(lean_object* v_a_6034_, lean_object* v_as_6035_, lean_object* v_i_6036_, lean_object* v_stop_6037_, lean_object* v_b_6038_, lean_object* v___y_6039_, lean_object* v___y_6040_, lean_object* v___y_6041_, lean_object* v___y_6042_, lean_object* v___y_6043_, lean_object* v___y_6044_, lean_object* v___y_6045_, lean_object* v___y_6046_, lean_object* v___y_6047_){
_start:
{
size_t v_i_boxed_6048_; size_t v_stop_boxed_6049_; lean_object* v_res_6050_; 
v_i_boxed_6048_ = lean_unbox_usize(v_i_6036_);
lean_dec(v_i_6036_);
v_stop_boxed_6049_ = lean_unbox_usize(v_stop_6037_);
lean_dec(v_stop_6037_);
v_res_6050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1(v_a_6034_, v_as_6035_, v_i_boxed_6048_, v_stop_boxed_6049_, v_b_6038_, v___y_6039_, v___y_6040_, v___y_6041_, v___y_6042_, v___y_6043_, v___y_6044_, v___y_6045_, v___y_6046_);
lean_dec_ref(v_as_6035_);
return v_res_6050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lam__0(lean_object* v___y_6051_, lean_object* v_a_6052_, lean_object* v___x_6053_, lean_object* v___y_6054_, lean_object* v___y_6055_, lean_object* v___y_6056_, lean_object* v___y_6057_, lean_object* v___y_6058_, lean_object* v___y_6059_, lean_object* v___y_6060_, lean_object* v___y_6061_){
_start:
{
if (lean_obj_tag(v___y_6051_) == 0)
{
lean_object* v___x_6063_; 
lean_inc(v___y_6061_);
lean_inc_ref(v___y_6060_);
lean_inc(v___y_6059_);
lean_inc_ref(v___y_6058_);
lean_inc(v___y_6057_);
lean_inc_ref(v___y_6056_);
lean_inc(v___y_6055_);
lean_inc_ref(v___y_6054_);
lean_inc_ref(v_a_6052_);
v___x_6063_ = l_Lean_Elab_Tactic_NormCast_normCastTarget(v_a_6052_, v___y_6054_, v___y_6055_, v___y_6056_, v___y_6057_, v___y_6058_, v___y_6059_, v___y_6060_, v___y_6061_);
if (lean_obj_tag(v___x_6063_) == 0)
{
lean_object* v___x_6064_; 
lean_dec_ref(v___x_6063_);
v___x_6064_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_6055_, v___y_6058_, v___y_6059_, v___y_6060_, v___y_6061_);
if (lean_obj_tag(v___x_6064_) == 0)
{
lean_object* v_a_6065_; lean_object* v___x_6066_; 
v_a_6065_ = lean_ctor_get(v___x_6064_, 0);
lean_inc(v_a_6065_);
lean_dec_ref(v___x_6064_);
lean_inc(v___y_6061_);
lean_inc_ref(v___y_6060_);
lean_inc(v___y_6059_);
lean_inc_ref(v___y_6058_);
v___x_6066_ = l_Lean_MVarId_getNondepPropHyps(v_a_6065_, v___y_6058_, v___y_6059_, v___y_6060_, v___y_6061_);
if (lean_obj_tag(v___x_6066_) == 0)
{
lean_object* v_a_6067_; lean_object* v___x_6069_; uint8_t v_isShared_6070_; uint8_t v_isSharedCheck_6087_; 
v_a_6067_ = lean_ctor_get(v___x_6066_, 0);
v_isSharedCheck_6087_ = !lean_is_exclusive(v___x_6066_);
if (v_isSharedCheck_6087_ == 0)
{
v___x_6069_ = v___x_6066_;
v_isShared_6070_ = v_isSharedCheck_6087_;
goto v_resetjp_6068_;
}
else
{
lean_inc(v_a_6067_);
lean_dec(v___x_6066_);
v___x_6069_ = lean_box(0);
v_isShared_6070_ = v_isSharedCheck_6087_;
goto v_resetjp_6068_;
}
v_resetjp_6068_:
{
lean_object* v___x_6071_; lean_object* v___x_6072_; uint8_t v___x_6073_; 
v___x_6071_ = lean_array_get_size(v_a_6067_);
v___x_6072_ = lean_box(0);
v___x_6073_ = lean_nat_dec_lt(v___x_6053_, v___x_6071_);
if (v___x_6073_ == 0)
{
lean_object* v___x_6075_; 
lean_dec(v_a_6067_);
lean_dec(v___y_6061_);
lean_dec_ref(v___y_6060_);
lean_dec(v___y_6059_);
lean_dec_ref(v___y_6058_);
lean_dec(v___y_6057_);
lean_dec_ref(v___y_6056_);
lean_dec(v___y_6055_);
lean_dec_ref(v___y_6054_);
lean_dec_ref(v_a_6052_);
if (v_isShared_6070_ == 0)
{
lean_ctor_set(v___x_6069_, 0, v___x_6072_);
v___x_6075_ = v___x_6069_;
goto v_reusejp_6074_;
}
else
{
lean_object* v_reuseFailAlloc_6076_; 
v_reuseFailAlloc_6076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6076_, 0, v___x_6072_);
v___x_6075_ = v_reuseFailAlloc_6076_;
goto v_reusejp_6074_;
}
v_reusejp_6074_:
{
return v___x_6075_;
}
}
else
{
uint8_t v___x_6077_; 
v___x_6077_ = lean_nat_dec_le(v___x_6071_, v___x_6071_);
if (v___x_6077_ == 0)
{
if (v___x_6073_ == 0)
{
lean_object* v___x_6079_; 
lean_dec(v_a_6067_);
lean_dec(v___y_6061_);
lean_dec_ref(v___y_6060_);
lean_dec(v___y_6059_);
lean_dec_ref(v___y_6058_);
lean_dec(v___y_6057_);
lean_dec_ref(v___y_6056_);
lean_dec(v___y_6055_);
lean_dec_ref(v___y_6054_);
lean_dec_ref(v_a_6052_);
if (v_isShared_6070_ == 0)
{
lean_ctor_set(v___x_6069_, 0, v___x_6072_);
v___x_6079_ = v___x_6069_;
goto v_reusejp_6078_;
}
else
{
lean_object* v_reuseFailAlloc_6080_; 
v_reuseFailAlloc_6080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6080_, 0, v___x_6072_);
v___x_6079_ = v_reuseFailAlloc_6080_;
goto v_reusejp_6078_;
}
v_reusejp_6078_:
{
return v___x_6079_;
}
}
else
{
size_t v___x_6081_; size_t v___x_6082_; lean_object* v___x_6083_; 
lean_del_object(v___x_6069_);
v___x_6081_ = ((size_t)0ULL);
v___x_6082_ = lean_usize_of_nat(v___x_6071_);
v___x_6083_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1(v_a_6052_, v_a_6067_, v___x_6081_, v___x_6082_, v___x_6072_, v___y_6054_, v___y_6055_, v___y_6056_, v___y_6057_, v___y_6058_, v___y_6059_, v___y_6060_, v___y_6061_);
lean_dec(v_a_6067_);
return v___x_6083_;
}
}
else
{
size_t v___x_6084_; size_t v___x_6085_; lean_object* v___x_6086_; 
lean_del_object(v___x_6069_);
v___x_6084_ = ((size_t)0ULL);
v___x_6085_ = lean_usize_of_nat(v___x_6071_);
v___x_6086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1(v_a_6052_, v_a_6067_, v___x_6084_, v___x_6085_, v___x_6072_, v___y_6054_, v___y_6055_, v___y_6056_, v___y_6057_, v___y_6058_, v___y_6059_, v___y_6060_, v___y_6061_);
lean_dec(v_a_6067_);
return v___x_6086_;
}
}
}
}
else
{
lean_object* v_a_6088_; lean_object* v___x_6090_; uint8_t v_isShared_6091_; uint8_t v_isSharedCheck_6095_; 
lean_dec(v___y_6061_);
lean_dec_ref(v___y_6060_);
lean_dec(v___y_6059_);
lean_dec_ref(v___y_6058_);
lean_dec(v___y_6057_);
lean_dec_ref(v___y_6056_);
lean_dec(v___y_6055_);
lean_dec_ref(v___y_6054_);
lean_dec_ref(v_a_6052_);
v_a_6088_ = lean_ctor_get(v___x_6066_, 0);
v_isSharedCheck_6095_ = !lean_is_exclusive(v___x_6066_);
if (v_isSharedCheck_6095_ == 0)
{
v___x_6090_ = v___x_6066_;
v_isShared_6091_ = v_isSharedCheck_6095_;
goto v_resetjp_6089_;
}
else
{
lean_inc(v_a_6088_);
lean_dec(v___x_6066_);
v___x_6090_ = lean_box(0);
v_isShared_6091_ = v_isSharedCheck_6095_;
goto v_resetjp_6089_;
}
v_resetjp_6089_:
{
lean_object* v___x_6093_; 
if (v_isShared_6091_ == 0)
{
v___x_6093_ = v___x_6090_;
goto v_reusejp_6092_;
}
else
{
lean_object* v_reuseFailAlloc_6094_; 
v_reuseFailAlloc_6094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6094_, 0, v_a_6088_);
v___x_6093_ = v_reuseFailAlloc_6094_;
goto v_reusejp_6092_;
}
v_reusejp_6092_:
{
return v___x_6093_;
}
}
}
}
else
{
lean_object* v_a_6096_; lean_object* v___x_6098_; uint8_t v_isShared_6099_; uint8_t v_isSharedCheck_6103_; 
lean_dec(v___y_6061_);
lean_dec_ref(v___y_6060_);
lean_dec(v___y_6059_);
lean_dec_ref(v___y_6058_);
lean_dec(v___y_6057_);
lean_dec_ref(v___y_6056_);
lean_dec(v___y_6055_);
lean_dec_ref(v___y_6054_);
lean_dec_ref(v_a_6052_);
v_a_6096_ = lean_ctor_get(v___x_6064_, 0);
v_isSharedCheck_6103_ = !lean_is_exclusive(v___x_6064_);
if (v_isSharedCheck_6103_ == 0)
{
v___x_6098_ = v___x_6064_;
v_isShared_6099_ = v_isSharedCheck_6103_;
goto v_resetjp_6097_;
}
else
{
lean_inc(v_a_6096_);
lean_dec(v___x_6064_);
v___x_6098_ = lean_box(0);
v_isShared_6099_ = v_isSharedCheck_6103_;
goto v_resetjp_6097_;
}
v_resetjp_6097_:
{
lean_object* v___x_6101_; 
if (v_isShared_6099_ == 0)
{
v___x_6101_ = v___x_6098_;
goto v_reusejp_6100_;
}
else
{
lean_object* v_reuseFailAlloc_6102_; 
v_reuseFailAlloc_6102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6102_, 0, v_a_6096_);
v___x_6101_ = v_reuseFailAlloc_6102_;
goto v_reusejp_6100_;
}
v_reusejp_6100_:
{
return v___x_6101_;
}
}
}
}
else
{
lean_dec(v___y_6061_);
lean_dec_ref(v___y_6060_);
lean_dec(v___y_6059_);
lean_dec_ref(v___y_6058_);
lean_dec(v___y_6057_);
lean_dec_ref(v___y_6056_);
lean_dec(v___y_6055_);
lean_dec_ref(v___y_6054_);
lean_dec_ref(v_a_6052_);
return v___x_6063_;
}
}
else
{
lean_object* v_hypotheses_6104_; uint8_t v_type_6105_; lean_object* v___y_6107_; lean_object* v___y_6108_; lean_object* v___y_6109_; lean_object* v___y_6110_; lean_object* v___y_6111_; lean_object* v___y_6112_; lean_object* v___y_6113_; lean_object* v___y_6114_; 
v_hypotheses_6104_ = lean_ctor_get(v___y_6051_, 0);
lean_inc_ref(v_hypotheses_6104_);
v_type_6105_ = lean_ctor_get_uint8(v___y_6051_, sizeof(void*)*1);
lean_dec_ref(v___y_6051_);
if (v_type_6105_ == 0)
{
v___y_6107_ = v___y_6054_;
v___y_6108_ = v___y_6055_;
v___y_6109_ = v___y_6056_;
v___y_6110_ = v___y_6057_;
v___y_6111_ = v___y_6058_;
v___y_6112_ = v___y_6059_;
v___y_6113_ = v___y_6060_;
v___y_6114_ = v___y_6061_;
goto v___jp_6106_;
}
else
{
lean_object* v___x_6145_; 
lean_inc(v___y_6061_);
lean_inc_ref(v___y_6060_);
lean_inc(v___y_6059_);
lean_inc_ref(v___y_6058_);
lean_inc(v___y_6057_);
lean_inc_ref(v___y_6056_);
lean_inc(v___y_6055_);
lean_inc_ref(v___y_6054_);
lean_inc_ref(v_a_6052_);
v___x_6145_ = l_Lean_Elab_Tactic_NormCast_normCastTarget(v_a_6052_, v___y_6054_, v___y_6055_, v___y_6056_, v___y_6057_, v___y_6058_, v___y_6059_, v___y_6060_, v___y_6061_);
if (lean_obj_tag(v___x_6145_) == 0)
{
lean_dec_ref(v___x_6145_);
v___y_6107_ = v___y_6054_;
v___y_6108_ = v___y_6055_;
v___y_6109_ = v___y_6056_;
v___y_6110_ = v___y_6057_;
v___y_6111_ = v___y_6058_;
v___y_6112_ = v___y_6059_;
v___y_6113_ = v___y_6060_;
v___y_6114_ = v___y_6061_;
goto v___jp_6106_;
}
else
{
lean_dec_ref(v_hypotheses_6104_);
lean_dec(v___y_6061_);
lean_dec_ref(v___y_6060_);
lean_dec(v___y_6059_);
lean_dec_ref(v___y_6058_);
lean_dec(v___y_6057_);
lean_dec_ref(v___y_6056_);
lean_dec(v___y_6055_);
lean_dec_ref(v___y_6054_);
lean_dec_ref(v_a_6052_);
return v___x_6145_;
}
}
v___jp_6106_:
{
lean_object* v___x_6115_; 
lean_inc(v___y_6114_);
lean_inc_ref(v___y_6113_);
lean_inc(v___y_6112_);
lean_inc_ref(v___y_6111_);
lean_inc(v___y_6110_);
lean_inc_ref(v___y_6109_);
lean_inc(v___y_6108_);
lean_inc_ref(v___y_6107_);
v___x_6115_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_6104_, v___y_6107_, v___y_6108_, v___y_6109_, v___y_6110_, v___y_6111_, v___y_6112_, v___y_6113_, v___y_6114_);
if (lean_obj_tag(v___x_6115_) == 0)
{
lean_object* v_a_6116_; lean_object* v___x_6118_; uint8_t v_isShared_6119_; uint8_t v_isSharedCheck_6136_; 
v_a_6116_ = lean_ctor_get(v___x_6115_, 0);
v_isSharedCheck_6136_ = !lean_is_exclusive(v___x_6115_);
if (v_isSharedCheck_6136_ == 0)
{
v___x_6118_ = v___x_6115_;
v_isShared_6119_ = v_isSharedCheck_6136_;
goto v_resetjp_6117_;
}
else
{
lean_inc(v_a_6116_);
lean_dec(v___x_6115_);
v___x_6118_ = lean_box(0);
v_isShared_6119_ = v_isSharedCheck_6136_;
goto v_resetjp_6117_;
}
v_resetjp_6117_:
{
lean_object* v___x_6120_; lean_object* v___x_6121_; uint8_t v___x_6122_; 
v___x_6120_ = lean_array_get_size(v_a_6116_);
v___x_6121_ = lean_box(0);
v___x_6122_ = lean_nat_dec_lt(v___x_6053_, v___x_6120_);
if (v___x_6122_ == 0)
{
lean_object* v___x_6124_; 
lean_dec(v_a_6116_);
lean_dec(v___y_6114_);
lean_dec_ref(v___y_6113_);
lean_dec(v___y_6112_);
lean_dec_ref(v___y_6111_);
lean_dec(v___y_6110_);
lean_dec_ref(v___y_6109_);
lean_dec(v___y_6108_);
lean_dec_ref(v___y_6107_);
lean_dec_ref(v_a_6052_);
if (v_isShared_6119_ == 0)
{
lean_ctor_set(v___x_6118_, 0, v___x_6121_);
v___x_6124_ = v___x_6118_;
goto v_reusejp_6123_;
}
else
{
lean_object* v_reuseFailAlloc_6125_; 
v_reuseFailAlloc_6125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6125_, 0, v___x_6121_);
v___x_6124_ = v_reuseFailAlloc_6125_;
goto v_reusejp_6123_;
}
v_reusejp_6123_:
{
return v___x_6124_;
}
}
else
{
uint8_t v___x_6126_; 
v___x_6126_ = lean_nat_dec_le(v___x_6120_, v___x_6120_);
if (v___x_6126_ == 0)
{
if (v___x_6122_ == 0)
{
lean_object* v___x_6128_; 
lean_dec(v_a_6116_);
lean_dec(v___y_6114_);
lean_dec_ref(v___y_6113_);
lean_dec(v___y_6112_);
lean_dec_ref(v___y_6111_);
lean_dec(v___y_6110_);
lean_dec_ref(v___y_6109_);
lean_dec(v___y_6108_);
lean_dec_ref(v___y_6107_);
lean_dec_ref(v_a_6052_);
if (v_isShared_6119_ == 0)
{
lean_ctor_set(v___x_6118_, 0, v___x_6121_);
v___x_6128_ = v___x_6118_;
goto v_reusejp_6127_;
}
else
{
lean_object* v_reuseFailAlloc_6129_; 
v_reuseFailAlloc_6129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6129_, 0, v___x_6121_);
v___x_6128_ = v_reuseFailAlloc_6129_;
goto v_reusejp_6127_;
}
v_reusejp_6127_:
{
return v___x_6128_;
}
}
else
{
size_t v___x_6130_; size_t v___x_6131_; lean_object* v___x_6132_; 
lean_del_object(v___x_6118_);
v___x_6130_ = ((size_t)0ULL);
v___x_6131_ = lean_usize_of_nat(v___x_6120_);
v___x_6132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1(v_a_6052_, v_a_6116_, v___x_6130_, v___x_6131_, v___x_6121_, v___y_6107_, v___y_6108_, v___y_6109_, v___y_6110_, v___y_6111_, v___y_6112_, v___y_6113_, v___y_6114_);
lean_dec(v_a_6116_);
return v___x_6132_;
}
}
else
{
size_t v___x_6133_; size_t v___x_6134_; lean_object* v___x_6135_; 
lean_del_object(v___x_6118_);
v___x_6133_ = ((size_t)0ULL);
v___x_6134_ = lean_usize_of_nat(v___x_6120_);
v___x_6135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1(v_a_6052_, v_a_6116_, v___x_6133_, v___x_6134_, v___x_6121_, v___y_6107_, v___y_6108_, v___y_6109_, v___y_6110_, v___y_6111_, v___y_6112_, v___y_6113_, v___y_6114_);
lean_dec(v_a_6116_);
return v___x_6135_;
}
}
}
}
else
{
lean_object* v_a_6137_; lean_object* v___x_6139_; uint8_t v_isShared_6140_; uint8_t v_isSharedCheck_6144_; 
lean_dec(v___y_6114_);
lean_dec_ref(v___y_6113_);
lean_dec(v___y_6112_);
lean_dec_ref(v___y_6111_);
lean_dec(v___y_6110_);
lean_dec_ref(v___y_6109_);
lean_dec(v___y_6108_);
lean_dec_ref(v___y_6107_);
lean_dec_ref(v_a_6052_);
v_a_6137_ = lean_ctor_get(v___x_6115_, 0);
v_isSharedCheck_6144_ = !lean_is_exclusive(v___x_6115_);
if (v_isSharedCheck_6144_ == 0)
{
v___x_6139_ = v___x_6115_;
v_isShared_6140_ = v_isSharedCheck_6144_;
goto v_resetjp_6138_;
}
else
{
lean_inc(v_a_6137_);
lean_dec(v___x_6115_);
v___x_6139_ = lean_box(0);
v_isShared_6140_ = v_isSharedCheck_6144_;
goto v_resetjp_6138_;
}
v_resetjp_6138_:
{
lean_object* v___x_6142_; 
if (v_isShared_6140_ == 0)
{
v___x_6142_ = v___x_6139_;
goto v_reusejp_6141_;
}
else
{
lean_object* v_reuseFailAlloc_6143_; 
v_reuseFailAlloc_6143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6143_, 0, v_a_6137_);
v___x_6142_ = v_reuseFailAlloc_6143_;
goto v_reusejp_6141_;
}
v_reusejp_6141_:
{
return v___x_6142_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lam__0___boxed(lean_object* v___y_6146_, lean_object* v_a_6147_, lean_object* v___x_6148_, lean_object* v___y_6149_, lean_object* v___y_6150_, lean_object* v___y_6151_, lean_object* v___y_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_, lean_object* v___y_6157_){
_start:
{
lean_object* v_res_6158_; 
v_res_6158_ = l_Lean_Elab_Tactic_NormCast_evalNormCast0___lam__0(v___y_6146_, v_a_6147_, v___x_6148_, v___y_6149_, v___y_6150_, v___y_6151_, v___y_6152_, v___y_6153_, v___y_6154_, v___y_6155_, v___y_6156_);
lean_dec(v___x_6148_);
return v_res_6158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0(lean_object* v_stx_6168_, lean_object* v_a_6169_, lean_object* v_a_6170_, lean_object* v_a_6171_, lean_object* v_a_6172_, lean_object* v_a_6173_, lean_object* v_a_6174_, lean_object* v_a_6175_, lean_object* v_a_6176_){
_start:
{
lean_object* v___x_6178_; uint8_t v___x_6179_; 
v___x_6178_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__2));
lean_inc(v_stx_6168_);
v___x_6179_ = l_Lean_Syntax_isOfKind(v_stx_6168_, v___x_6178_);
if (v___x_6179_ == 0)
{
lean_object* v___x_6180_; 
lean_dec(v_a_6176_);
lean_dec_ref(v_a_6175_);
lean_dec(v_a_6174_);
lean_dec_ref(v_a_6173_);
lean_dec(v_a_6172_);
lean_dec_ref(v_a_6171_);
lean_dec(v_a_6170_);
lean_dec_ref(v_a_6169_);
lean_dec(v_stx_6168_);
v___x_6180_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg();
return v___x_6180_;
}
else
{
lean_object* v___x_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; lean_object* v___y_6185_; lean_object* v___y_6186_; lean_object* v___y_6187_; lean_object* v___y_6188_; lean_object* v___y_6189_; lean_object* v___y_6190_; lean_object* v___y_6191_; lean_object* v___y_6192_; lean_object* v___y_6193_; lean_object* v___x_6206_; lean_object* v___x_6207_; uint8_t v___x_6208_; 
v___x_6181_ = lean_unsigned_to_nat(0u);
v___x_6182_ = lean_unsigned_to_nat(1u);
v___x_6183_ = l_Lean_Syntax_getArg(v_stx_6168_, v___x_6182_);
v___x_6206_ = lean_unsigned_to_nat(2u);
v___x_6207_ = l_Lean_Syntax_getArg(v_stx_6168_, v___x_6206_);
lean_dec(v_stx_6168_);
v___x_6208_ = l_Lean_Syntax_isNone(v___x_6207_);
if (v___x_6208_ == 0)
{
uint8_t v___x_6209_; 
lean_inc(v___x_6207_);
v___x_6209_ = l_Lean_Syntax_matchesNull(v___x_6207_, v___x_6182_);
if (v___x_6209_ == 0)
{
lean_object* v___x_6210_; 
lean_dec(v___x_6207_);
lean_dec(v___x_6183_);
lean_dec(v_a_6176_);
lean_dec_ref(v_a_6175_);
lean_dec(v_a_6174_);
lean_dec_ref(v_a_6173_);
lean_dec(v_a_6172_);
lean_dec_ref(v_a_6171_);
lean_dec(v_a_6170_);
lean_dec_ref(v_a_6169_);
v___x_6210_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg();
return v___x_6210_;
}
else
{
lean_object* v_loc_x3f_6211_; lean_object* v___x_6212_; 
v_loc_x3f_6211_ = l_Lean_Syntax_getArg(v___x_6207_, v___x_6181_);
lean_dec(v___x_6207_);
v___x_6212_ = l_Lean_Elab_Tactic_expandLocation(v_loc_x3f_6211_);
lean_dec(v_loc_x3f_6211_);
v___y_6185_ = v_a_6174_;
v___y_6186_ = v_a_6171_;
v___y_6187_ = v_a_6173_;
v___y_6188_ = v_a_6172_;
v___y_6189_ = v_a_6176_;
v___y_6190_ = v_a_6170_;
v___y_6191_ = v_a_6169_;
v___y_6192_ = v_a_6175_;
v___y_6193_ = v___x_6212_;
goto v___jp_6184_;
}
}
else
{
lean_object* v___x_6213_; lean_object* v___x_6214_; 
lean_dec(v___x_6207_);
v___x_6213_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__3));
v___x_6214_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_6214_, 0, v___x_6213_);
lean_ctor_set_uint8(v___x_6214_, sizeof(void*)*1, v___x_6179_);
v___y_6185_ = v_a_6174_;
v___y_6186_ = v_a_6171_;
v___y_6187_ = v_a_6173_;
v___y_6188_ = v_a_6172_;
v___y_6189_ = v_a_6176_;
v___y_6190_ = v_a_6170_;
v___y_6191_ = v_a_6169_;
v___y_6192_ = v_a_6175_;
v___y_6193_ = v___x_6214_;
goto v___jp_6184_;
}
v___jp_6184_:
{
lean_object* v___x_6194_; 
lean_inc(v___y_6189_);
lean_inc_ref(v___y_6192_);
lean_inc(v___y_6185_);
lean_inc_ref(v___y_6187_);
lean_inc(v___y_6188_);
lean_inc_ref(v___y_6186_);
v___x_6194_ = l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg(v___x_6183_, v___y_6191_, v___y_6186_, v___y_6188_, v___y_6187_, v___y_6185_, v___y_6192_, v___y_6189_);
if (lean_obj_tag(v___x_6194_) == 0)
{
lean_object* v_a_6195_; lean_object* v___y_6196_; lean_object* v___x_6197_; 
v_a_6195_ = lean_ctor_get(v___x_6194_, 0);
lean_inc(v_a_6195_);
lean_dec_ref(v___x_6194_);
v___y_6196_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___lam__0___boxed), 12, 3);
lean_closure_set(v___y_6196_, 0, v___y_6193_);
lean_closure_set(v___y_6196_, 1, v_a_6195_);
lean_closure_set(v___y_6196_, 2, v___x_6181_);
v___x_6197_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_6196_, v___y_6191_, v___y_6190_, v___y_6186_, v___y_6188_, v___y_6187_, v___y_6185_, v___y_6192_, v___y_6189_);
return v___x_6197_;
}
else
{
lean_object* v_a_6198_; lean_object* v___x_6200_; uint8_t v_isShared_6201_; uint8_t v_isSharedCheck_6205_; 
lean_dec(v___y_6193_);
lean_dec_ref(v___y_6192_);
lean_dec_ref(v___y_6191_);
lean_dec(v___y_6190_);
lean_dec(v___y_6189_);
lean_dec(v___y_6188_);
lean_dec_ref(v___y_6187_);
lean_dec_ref(v___y_6186_);
lean_dec(v___y_6185_);
v_a_6198_ = lean_ctor_get(v___x_6194_, 0);
v_isSharedCheck_6205_ = !lean_is_exclusive(v___x_6194_);
if (v_isSharedCheck_6205_ == 0)
{
v___x_6200_ = v___x_6194_;
v_isShared_6201_ = v_isSharedCheck_6205_;
goto v_resetjp_6199_;
}
else
{
lean_inc(v_a_6198_);
lean_dec(v___x_6194_);
v___x_6200_ = lean_box(0);
v_isShared_6201_ = v_isSharedCheck_6205_;
goto v_resetjp_6199_;
}
v_resetjp_6199_:
{
lean_object* v___x_6203_; 
if (v_isShared_6201_ == 0)
{
v___x_6203_ = v___x_6200_;
goto v_reusejp_6202_;
}
else
{
lean_object* v_reuseFailAlloc_6204_; 
v_reuseFailAlloc_6204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6204_, 0, v_a_6198_);
v___x_6203_ = v_reuseFailAlloc_6204_;
goto v_reusejp_6202_;
}
v_reusejp_6202_:
{
return v___x_6203_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___boxed(lean_object* v_stx_6215_, lean_object* v_a_6216_, lean_object* v_a_6217_, lean_object* v_a_6218_, lean_object* v_a_6219_, lean_object* v_a_6220_, lean_object* v_a_6221_, lean_object* v_a_6222_, lean_object* v_a_6223_, lean_object* v_a_6224_){
_start:
{
lean_object* v_res_6225_; 
v_res_6225_ = l_Lean_Elab_Tactic_NormCast_evalNormCast0(v_stx_6215_, v_a_6216_, v_a_6217_, v_a_6218_, v_a_6219_, v_a_6220_, v_a_6221_, v_a_6222_, v_a_6223_);
return v_res_6225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1(){
_start:
{
lean_object* v___x_6234_; lean_object* v___x_6235_; lean_object* v___x_6236_; lean_object* v___x_6237_; lean_object* v___x_6238_; 
v___x_6234_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6235_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__2));
v___x_6236_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1));
v___x_6237_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___boxed), 10, 0);
v___x_6238_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6234_, v___x_6235_, v___x_6236_, v___x_6237_);
return v___x_6238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___boxed(lean_object* v_a_6239_){
_start:
{
lean_object* v_res_6240_; 
v_res_6240_ = l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1();
return v_res_6240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3(){
_start:
{
lean_object* v___x_6267_; lean_object* v___x_6268_; lean_object* v___x_6269_; 
v___x_6267_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1));
v___x_6268_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__6));
v___x_6269_ = l_Lean_addBuiltinDeclarationRanges(v___x_6267_, v___x_6268_);
return v___x_6269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___boxed(lean_object* v_a_6270_){
_start:
{
lean_object* v_res_6271_; 
v_res_6271_ = l_Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3();
return v_res_6271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___lam__0(lean_object* v___y_6272_, lean_object* v___y_6273_, lean_object* v___y_6274_, lean_object* v___y_6275_, lean_object* v___y_6276_, lean_object* v___y_6277_, lean_object* v___y_6278_, lean_object* v___y_6279_){
_start:
{
lean_object* v___x_6281_; 
lean_inc(v___y_6279_);
lean_inc_ref(v___y_6278_);
lean_inc(v___y_6277_);
lean_inc_ref(v___y_6276_);
v___x_6281_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_6273_, v___y_6276_, v___y_6277_, v___y_6278_, v___y_6279_);
if (lean_obj_tag(v___x_6281_) == 0)
{
lean_object* v_a_6282_; lean_object* v___x_6283_; lean_object* v___x_6284_; 
v_a_6282_ = lean_ctor_get(v___x_6281_, 0);
lean_inc(v_a_6282_);
lean_dec_ref(v___x_6281_);
v___x_6283_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__10));
lean_inc(v___y_6279_);
lean_inc_ref(v___y_6278_);
lean_inc(v___y_6277_);
lean_inc_ref(v___y_6276_);
v___x_6284_ = l_Lean_Elab_Tactic_NormCast_derive(v_a_6282_, v___x_6283_, v___y_6276_, v___y_6277_, v___y_6278_, v___y_6279_);
if (lean_obj_tag(v___x_6284_) == 0)
{
lean_object* v_a_6285_; lean_object* v___x_6286_; 
v_a_6285_ = lean_ctor_get(v___x_6284_, 0);
lean_inc(v_a_6285_);
lean_dec_ref(v___x_6284_);
v___x_6286_ = l_Lean_Elab_Tactic_Conv_applySimpResult(v_a_6285_, v___y_6272_, v___y_6273_, v___y_6274_, v___y_6275_, v___y_6276_, v___y_6277_, v___y_6278_, v___y_6279_);
return v___x_6286_;
}
else
{
lean_object* v_a_6287_; lean_object* v___x_6289_; uint8_t v_isShared_6290_; uint8_t v_isSharedCheck_6294_; 
lean_dec(v___y_6279_);
lean_dec_ref(v___y_6278_);
lean_dec(v___y_6277_);
lean_dec_ref(v___y_6276_);
lean_dec(v___y_6275_);
lean_dec_ref(v___y_6274_);
lean_dec(v___y_6273_);
lean_dec_ref(v___y_6272_);
v_a_6287_ = lean_ctor_get(v___x_6284_, 0);
v_isSharedCheck_6294_ = !lean_is_exclusive(v___x_6284_);
if (v_isSharedCheck_6294_ == 0)
{
v___x_6289_ = v___x_6284_;
v_isShared_6290_ = v_isSharedCheck_6294_;
goto v_resetjp_6288_;
}
else
{
lean_inc(v_a_6287_);
lean_dec(v___x_6284_);
v___x_6289_ = lean_box(0);
v_isShared_6290_ = v_isSharedCheck_6294_;
goto v_resetjp_6288_;
}
v_resetjp_6288_:
{
lean_object* v___x_6292_; 
if (v_isShared_6290_ == 0)
{
v___x_6292_ = v___x_6289_;
goto v_reusejp_6291_;
}
else
{
lean_object* v_reuseFailAlloc_6293_; 
v_reuseFailAlloc_6293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6293_, 0, v_a_6287_);
v___x_6292_ = v_reuseFailAlloc_6293_;
goto v_reusejp_6291_;
}
v_reusejp_6291_:
{
return v___x_6292_;
}
}
}
}
else
{
lean_object* v_a_6295_; lean_object* v___x_6297_; uint8_t v_isShared_6298_; uint8_t v_isSharedCheck_6302_; 
lean_dec(v___y_6279_);
lean_dec_ref(v___y_6278_);
lean_dec(v___y_6277_);
lean_dec_ref(v___y_6276_);
lean_dec(v___y_6275_);
lean_dec_ref(v___y_6274_);
lean_dec(v___y_6273_);
lean_dec_ref(v___y_6272_);
v_a_6295_ = lean_ctor_get(v___x_6281_, 0);
v_isSharedCheck_6302_ = !lean_is_exclusive(v___x_6281_);
if (v_isSharedCheck_6302_ == 0)
{
v___x_6297_ = v___x_6281_;
v_isShared_6298_ = v_isSharedCheck_6302_;
goto v_resetjp_6296_;
}
else
{
lean_inc(v_a_6295_);
lean_dec(v___x_6281_);
v___x_6297_ = lean_box(0);
v_isShared_6298_ = v_isSharedCheck_6302_;
goto v_resetjp_6296_;
}
v_resetjp_6296_:
{
lean_object* v___x_6300_; 
if (v_isShared_6298_ == 0)
{
v___x_6300_ = v___x_6297_;
goto v_reusejp_6299_;
}
else
{
lean_object* v_reuseFailAlloc_6301_; 
v_reuseFailAlloc_6301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6301_, 0, v_a_6295_);
v___x_6300_ = v_reuseFailAlloc_6301_;
goto v_reusejp_6299_;
}
v_reusejp_6299_:
{
return v___x_6300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___lam__0___boxed(lean_object* v___y_6303_, lean_object* v___y_6304_, lean_object* v___y_6305_, lean_object* v___y_6306_, lean_object* v___y_6307_, lean_object* v___y_6308_, lean_object* v___y_6309_, lean_object* v___y_6310_, lean_object* v___y_6311_){
_start:
{
lean_object* v_res_6312_; 
v_res_6312_ = l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___lam__0(v___y_6303_, v___y_6304_, v___y_6305_, v___y_6306_, v___y_6307_, v___y_6308_, v___y_6309_, v___y_6310_);
return v_res_6312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg(lean_object* v_a_6314_, lean_object* v_a_6315_, lean_object* v_a_6316_, lean_object* v_a_6317_, lean_object* v_a_6318_, lean_object* v_a_6319_, lean_object* v_a_6320_, lean_object* v_a_6321_){
_start:
{
lean_object* v___f_6323_; lean_object* v___x_6324_; 
v___f_6323_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___closed__0));
v___x_6324_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_6323_, v_a_6314_, v_a_6315_, v_a_6316_, v_a_6317_, v_a_6318_, v_a_6319_, v_a_6320_, v_a_6321_);
return v___x_6324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___boxed(lean_object* v_a_6325_, lean_object* v_a_6326_, lean_object* v_a_6327_, lean_object* v_a_6328_, lean_object* v_a_6329_, lean_object* v_a_6330_, lean_object* v_a_6331_, lean_object* v_a_6332_, lean_object* v_a_6333_){
_start:
{
lean_object* v_res_6334_; 
v_res_6334_ = l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg(v_a_6325_, v_a_6326_, v_a_6327_, v_a_6328_, v_a_6329_, v_a_6330_, v_a_6331_, v_a_6332_);
return v_res_6334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast(lean_object* v_x_6335_, lean_object* v_a_6336_, lean_object* v_a_6337_, lean_object* v_a_6338_, lean_object* v_a_6339_, lean_object* v_a_6340_, lean_object* v_a_6341_, lean_object* v_a_6342_, lean_object* v_a_6343_){
_start:
{
lean_object* v___x_6345_; 
v___x_6345_ = l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg(v_a_6336_, v_a_6337_, v_a_6338_, v_a_6339_, v_a_6340_, v_a_6341_, v_a_6342_, v_a_6343_);
return v___x_6345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___boxed(lean_object* v_x_6346_, lean_object* v_a_6347_, lean_object* v_a_6348_, lean_object* v_a_6349_, lean_object* v_a_6350_, lean_object* v_a_6351_, lean_object* v_a_6352_, lean_object* v_a_6353_, lean_object* v_a_6354_, lean_object* v_a_6355_){
_start:
{
lean_object* v_res_6356_; 
v_res_6356_ = l_Lean_Elab_Tactic_NormCast_evalConvNormCast(v_x_6346_, v_a_6347_, v_a_6348_, v_a_6349_, v_a_6350_, v_a_6351_, v_a_6352_, v_a_6353_, v_a_6354_);
lean_dec(v_x_6346_);
return v_res_6356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1(){
_start:
{
lean_object* v___x_6373_; lean_object* v___x_6374_; lean_object* v___x_6375_; lean_object* v___x_6376_; lean_object* v___x_6377_; 
v___x_6373_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6374_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2));
v___x_6375_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4));
v___x_6376_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalConvNormCast___boxed), 10, 0);
v___x_6377_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6373_, v___x_6374_, v___x_6375_, v___x_6376_);
return v___x_6377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___boxed(lean_object* v_a_6378_){
_start:
{
lean_object* v_res_6379_; 
v_res_6379_ = l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1();
return v_res_6379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3(){
_start:
{
lean_object* v___x_6406_; lean_object* v___x_6407_; lean_object* v___x_6408_; 
v___x_6406_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4));
v___x_6407_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__6));
v___x_6408_ = l_Lean_addBuiltinDeclarationRanges(v___x_6406_, v___x_6407_);
return v___x_6408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___boxed(lean_object* v_a_6409_){
_start:
{
lean_object* v_res_6410_; 
v_res_6410_ = l_Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3();
return v_res_6410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0(lean_object* v_stx_6411_, lean_object* v___x_6412_, lean_object* v_simprocs_6413_, lean_object* v_discharge_x3f_6414_, lean_object* v___y_6415_, lean_object* v___y_6416_, lean_object* v___y_6417_, lean_object* v___y_6418_, lean_object* v___y_6419_, lean_object* v___y_6420_, lean_object* v___y_6421_, lean_object* v___y_6422_){
_start:
{
lean_object* v___x_6424_; lean_object* v___x_6425_; lean_object* v___x_6426_; lean_object* v___x_6427_; 
v___x_6424_ = lean_unsigned_to_nat(5u);
v___x_6425_ = l_Lean_Syntax_getArg(v_stx_6411_, v___x_6424_);
v___x_6426_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_6425_);
lean_dec(v___x_6425_);
v___x_6427_ = l_Lean_Elab_Tactic_simpLocation(v___x_6412_, v_simprocs_6413_, v_discharge_x3f_6414_, v___x_6426_, v___y_6415_, v___y_6416_, v___y_6417_, v___y_6418_, v___y_6419_, v___y_6420_, v___y_6421_, v___y_6422_);
if (lean_obj_tag(v___x_6427_) == 0)
{
lean_object* v___x_6429_; uint8_t v_isShared_6430_; uint8_t v_isSharedCheck_6435_; 
v_isSharedCheck_6435_ = !lean_is_exclusive(v___x_6427_);
if (v_isSharedCheck_6435_ == 0)
{
lean_object* v_unused_6436_; 
v_unused_6436_ = lean_ctor_get(v___x_6427_, 0);
lean_dec(v_unused_6436_);
v___x_6429_ = v___x_6427_;
v_isShared_6430_ = v_isSharedCheck_6435_;
goto v_resetjp_6428_;
}
else
{
lean_dec(v___x_6427_);
v___x_6429_ = lean_box(0);
v_isShared_6430_ = v_isSharedCheck_6435_;
goto v_resetjp_6428_;
}
v_resetjp_6428_:
{
lean_object* v___x_6431_; lean_object* v___x_6433_; 
v___x_6431_ = lean_box(0);
if (v_isShared_6430_ == 0)
{
lean_ctor_set(v___x_6429_, 0, v___x_6431_);
v___x_6433_ = v___x_6429_;
goto v_reusejp_6432_;
}
else
{
lean_object* v_reuseFailAlloc_6434_; 
v_reuseFailAlloc_6434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6434_, 0, v___x_6431_);
v___x_6433_ = v_reuseFailAlloc_6434_;
goto v_reusejp_6432_;
}
v_reusejp_6432_:
{
return v___x_6433_;
}
}
}
else
{
lean_object* v_a_6437_; lean_object* v___x_6439_; uint8_t v_isShared_6440_; uint8_t v_isSharedCheck_6444_; 
v_a_6437_ = lean_ctor_get(v___x_6427_, 0);
v_isSharedCheck_6444_ = !lean_is_exclusive(v___x_6427_);
if (v_isSharedCheck_6444_ == 0)
{
v___x_6439_ = v___x_6427_;
v_isShared_6440_ = v_isSharedCheck_6444_;
goto v_resetjp_6438_;
}
else
{
lean_inc(v_a_6437_);
lean_dec(v___x_6427_);
v___x_6439_ = lean_box(0);
v_isShared_6440_ = v_isSharedCheck_6444_;
goto v_resetjp_6438_;
}
v_resetjp_6438_:
{
lean_object* v___x_6442_; 
if (v_isShared_6440_ == 0)
{
v___x_6442_ = v___x_6439_;
goto v_reusejp_6441_;
}
else
{
lean_object* v_reuseFailAlloc_6443_; 
v_reuseFailAlloc_6443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6443_, 0, v_a_6437_);
v___x_6442_ = v_reuseFailAlloc_6443_;
goto v_reusejp_6441_;
}
v_reusejp_6441_:
{
return v___x_6442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0___boxed(lean_object* v_stx_6445_, lean_object* v___x_6446_, lean_object* v_simprocs_6447_, lean_object* v_discharge_x3f_6448_, lean_object* v___y_6449_, lean_object* v___y_6450_, lean_object* v___y_6451_, lean_object* v___y_6452_, lean_object* v___y_6453_, lean_object* v___y_6454_, lean_object* v___y_6455_, lean_object* v___y_6456_, lean_object* v___y_6457_){
_start:
{
lean_object* v_res_6458_; 
v_res_6458_ = l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0(v_stx_6445_, v___x_6446_, v_simprocs_6447_, v_discharge_x3f_6448_, v___y_6449_, v___y_6450_, v___y_6451_, v___y_6452_, v___y_6453_, v___y_6454_, v___y_6455_, v___y_6456_);
lean_dec(v_stx_6445_);
return v_res_6458_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__0(void){
_start:
{
lean_object* v___x_6459_; lean_object* v___x_6460_; 
v___x_6459_ = l_Lean_Meta_NormCast_pushCastExt;
v___x_6460_ = lean_alloc_closure((void*)(l_Lean_Meta_SimpExtension_getTheorems___boxed), 4, 1);
lean_closure_set(v___x_6460_, 0, v___x_6459_);
return v___x_6460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast(lean_object* v_stx_6461_, lean_object* v_a_6462_, lean_object* v_a_6463_, lean_object* v_a_6464_, lean_object* v_a_6465_, lean_object* v_a_6466_, lean_object* v_a_6467_, lean_object* v_a_6468_, lean_object* v_a_6469_){
_start:
{
uint8_t v___x_6471_; uint8_t v___x_6472_; lean_object* v___x_6473_; lean_object* v___x_6474_; lean_object* v___x_6475_; lean_object* v___x_6476_; lean_object* v___x_6477_; lean_object* v___x_6478_; 
v___x_6471_ = 0;
v___x_6472_ = 0;
v___x_6473_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__0, &l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__0_once, _init_l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__0);
v___x_6474_ = lean_box(v___x_6471_);
v___x_6475_ = lean_box(v___x_6472_);
v___x_6476_ = lean_box(v___x_6471_);
lean_inc(v_stx_6461_);
v___x_6477_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_6477_, 0, v_stx_6461_);
lean_closure_set(v___x_6477_, 1, v___x_6474_);
lean_closure_set(v___x_6477_, 2, v___x_6475_);
lean_closure_set(v___x_6477_, 3, v___x_6476_);
lean_closure_set(v___x_6477_, 4, v___x_6473_);
lean_inc(v_a_6469_);
lean_inc_ref(v_a_6468_);
lean_inc(v_a_6467_);
lean_inc_ref(v_a_6466_);
lean_inc(v_a_6465_);
lean_inc_ref(v_a_6464_);
lean_inc(v_a_6463_);
lean_inc_ref(v_a_6462_);
v___x_6478_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_6477_, v_a_6462_, v_a_6463_, v_a_6464_, v_a_6465_, v_a_6466_, v_a_6467_, v_a_6468_, v_a_6469_);
if (lean_obj_tag(v___x_6478_) == 0)
{
lean_object* v_a_6479_; lean_object* v_ctx_6480_; lean_object* v_simprocs_6481_; lean_object* v_dischargeWrapper_6482_; lean_object* v___x_6483_; lean_object* v___f_6484_; lean_object* v___x_6485_; 
v_a_6479_ = lean_ctor_get(v___x_6478_, 0);
lean_inc(v_a_6479_);
lean_dec_ref(v___x_6478_);
v_ctx_6480_ = lean_ctor_get(v_a_6479_, 0);
lean_inc_ref(v_ctx_6480_);
v_simprocs_6481_ = lean_ctor_get(v_a_6479_, 1);
lean_inc_ref(v_simprocs_6481_);
v_dischargeWrapper_6482_ = lean_ctor_get(v_a_6479_, 2);
lean_inc(v_dischargeWrapper_6482_);
lean_dec(v_a_6479_);
v___x_6483_ = l_Lean_Meta_Simp_Context_setFailIfUnchanged(v_ctx_6480_, v___x_6471_);
v___f_6484_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0___boxed), 13, 3);
lean_closure_set(v___f_6484_, 0, v_stx_6461_);
lean_closure_set(v___f_6484_, 1, v___x_6483_);
lean_closure_set(v___f_6484_, 2, v_simprocs_6481_);
v___x_6485_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v_dischargeWrapper_6482_, v___f_6484_, v_a_6462_, v_a_6463_, v_a_6464_, v_a_6465_, v_a_6466_, v_a_6467_, v_a_6468_, v_a_6469_);
lean_dec(v_dischargeWrapper_6482_);
return v___x_6485_;
}
else
{
lean_object* v_a_6486_; lean_object* v___x_6488_; uint8_t v_isShared_6489_; uint8_t v_isSharedCheck_6493_; 
lean_dec(v_a_6469_);
lean_dec_ref(v_a_6468_);
lean_dec(v_a_6467_);
lean_dec_ref(v_a_6466_);
lean_dec(v_a_6465_);
lean_dec_ref(v_a_6464_);
lean_dec(v_a_6463_);
lean_dec_ref(v_a_6462_);
lean_dec(v_stx_6461_);
v_a_6486_ = lean_ctor_get(v___x_6478_, 0);
v_isSharedCheck_6493_ = !lean_is_exclusive(v___x_6478_);
if (v_isSharedCheck_6493_ == 0)
{
v___x_6488_ = v___x_6478_;
v_isShared_6489_ = v_isSharedCheck_6493_;
goto v_resetjp_6487_;
}
else
{
lean_inc(v_a_6486_);
lean_dec(v___x_6478_);
v___x_6488_ = lean_box(0);
v_isShared_6489_ = v_isSharedCheck_6493_;
goto v_resetjp_6487_;
}
v_resetjp_6487_:
{
lean_object* v___x_6491_; 
if (v_isShared_6489_ == 0)
{
v___x_6491_ = v___x_6488_;
goto v_reusejp_6490_;
}
else
{
lean_object* v_reuseFailAlloc_6492_; 
v_reuseFailAlloc_6492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6492_, 0, v_a_6486_);
v___x_6491_ = v_reuseFailAlloc_6492_;
goto v_reusejp_6490_;
}
v_reusejp_6490_:
{
return v___x_6491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___boxed(lean_object* v_stx_6494_, lean_object* v_a_6495_, lean_object* v_a_6496_, lean_object* v_a_6497_, lean_object* v_a_6498_, lean_object* v_a_6499_, lean_object* v_a_6500_, lean_object* v_a_6501_, lean_object* v_a_6502_, lean_object* v_a_6503_){
_start:
{
lean_object* v_res_6504_; 
v_res_6504_ = l_Lean_Elab_Tactic_NormCast_evalPushCast(v_stx_6494_, v_a_6495_, v_a_6496_, v_a_6497_, v_a_6498_, v_a_6499_, v_a_6500_, v_a_6501_, v_a_6502_);
return v_res_6504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1(){
_start:
{
lean_object* v___x_6519_; lean_object* v___x_6520_; lean_object* v___x_6521_; lean_object* v___x_6522_; lean_object* v___x_6523_; 
v___x_6519_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6520_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1));
v___x_6521_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3));
v___x_6522_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalPushCast___boxed), 10, 0);
v___x_6523_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6519_, v___x_6520_, v___x_6521_, v___x_6522_);
return v___x_6523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___boxed(lean_object* v_a_6524_){
_start:
{
lean_object* v_res_6525_; 
v_res_6525_ = l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1();
return v_res_6525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3(){
_start:
{
lean_object* v___x_6552_; lean_object* v___x_6553_; lean_object* v___x_6554_; 
v___x_6552_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3));
v___x_6553_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__6));
v___x_6554_ = l_Lean_addBuiltinDeclarationRanges(v___x_6552_, v___x_6553_);
return v___x_6554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___boxed(lean_object* v_a_6555_){
_start:
{
lean_object* v_res_6556_; 
v_res_6556_ = l_Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3();
return v_res_6556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg(){
_start:
{
lean_object* v___x_6558_; lean_object* v___x_6559_; 
v___x_6558_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0);
v___x_6559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6559_, 0, v___x_6558_);
return v___x_6559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg___boxed(lean_object* v___y_6560_){
_start:
{
lean_object* v_res_6561_; 
v_res_6561_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg();
return v_res_6561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0(lean_object* v_00_u03b1_6562_, lean_object* v___y_6563_, lean_object* v___y_6564_){
_start:
{
lean_object* v___x_6566_; 
v___x_6566_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg();
return v___x_6566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___boxed(lean_object* v_00_u03b1_6567_, lean_object* v___y_6568_, lean_object* v___y_6569_, lean_object* v___y_6570_){
_start:
{
lean_object* v_res_6571_; 
v_res_6571_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0(v_00_u03b1_6567_, v___y_6568_, v___y_6569_);
lean_dec(v___y_6569_);
lean_dec_ref(v___y_6568_);
return v_res_6571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___lam__0(lean_object* v___x_6572_, lean_object* v___x_6573_, lean_object* v___x_6574_, lean_object* v___y_6575_, lean_object* v___y_6576_){
_start:
{
lean_object* v___x_6578_; lean_object* v___x_6579_; 
v___x_6578_ = lean_st_mk_ref(v___x_6572_);
lean_inc(v___y_6576_);
lean_inc_ref(v___y_6575_);
v___x_6579_ = l_Lean_realizeGlobalConstNoOverload(v___x_6573_, v___y_6575_, v___y_6576_);
if (lean_obj_tag(v___x_6579_) == 0)
{
lean_object* v_a_6580_; uint8_t v___x_6581_; lean_object* v___x_6582_; lean_object* v___x_6583_; 
v_a_6580_ = lean_ctor_get(v___x_6579_, 0);
lean_inc(v_a_6580_);
lean_dec_ref(v___x_6579_);
v___x_6581_ = 0;
v___x_6582_ = lean_unsigned_to_nat(1000u);
lean_inc(v___x_6578_);
v___x_6583_ = l_Lean_Meta_NormCast_addElim(v_a_6580_, v___x_6581_, v___x_6582_, v___x_6574_, v___x_6578_, v___y_6575_, v___y_6576_);
if (lean_obj_tag(v___x_6583_) == 0)
{
lean_object* v_a_6584_; lean_object* v___x_6586_; uint8_t v_isShared_6587_; uint8_t v_isSharedCheck_6592_; 
v_a_6584_ = lean_ctor_get(v___x_6583_, 0);
v_isSharedCheck_6592_ = !lean_is_exclusive(v___x_6583_);
if (v_isSharedCheck_6592_ == 0)
{
v___x_6586_ = v___x_6583_;
v_isShared_6587_ = v_isSharedCheck_6592_;
goto v_resetjp_6585_;
}
else
{
lean_inc(v_a_6584_);
lean_dec(v___x_6583_);
v___x_6586_ = lean_box(0);
v_isShared_6587_ = v_isSharedCheck_6592_;
goto v_resetjp_6585_;
}
v_resetjp_6585_:
{
lean_object* v___x_6588_; lean_object* v___x_6590_; 
v___x_6588_ = lean_st_ref_get(v___x_6578_);
lean_dec(v___x_6578_);
lean_dec(v___x_6588_);
if (v_isShared_6587_ == 0)
{
v___x_6590_ = v___x_6586_;
goto v_reusejp_6589_;
}
else
{
lean_object* v_reuseFailAlloc_6591_; 
v_reuseFailAlloc_6591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6591_, 0, v_a_6584_);
v___x_6590_ = v_reuseFailAlloc_6591_;
goto v_reusejp_6589_;
}
v_reusejp_6589_:
{
return v___x_6590_;
}
}
}
else
{
lean_dec(v___x_6578_);
return v___x_6583_;
}
}
else
{
lean_object* v_a_6593_; lean_object* v___x_6595_; uint8_t v_isShared_6596_; uint8_t v_isSharedCheck_6600_; 
lean_dec(v___x_6578_);
lean_dec(v___y_6576_);
lean_dec_ref(v___y_6575_);
lean_dec_ref(v___x_6574_);
v_a_6593_ = lean_ctor_get(v___x_6579_, 0);
v_isSharedCheck_6600_ = !lean_is_exclusive(v___x_6579_);
if (v_isSharedCheck_6600_ == 0)
{
v___x_6595_ = v___x_6579_;
v_isShared_6596_ = v_isSharedCheck_6600_;
goto v_resetjp_6594_;
}
else
{
lean_inc(v_a_6593_);
lean_dec(v___x_6579_);
v___x_6595_ = lean_box(0);
v_isShared_6596_ = v_isSharedCheck_6600_;
goto v_resetjp_6594_;
}
v_resetjp_6594_:
{
lean_object* v___x_6598_; 
if (v_isShared_6596_ == 0)
{
v___x_6598_ = v___x_6595_;
goto v_reusejp_6597_;
}
else
{
lean_object* v_reuseFailAlloc_6599_; 
v_reuseFailAlloc_6599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6599_, 0, v_a_6593_);
v___x_6598_ = v_reuseFailAlloc_6599_;
goto v_reusejp_6597_;
}
v_reusejp_6597_:
{
return v___x_6598_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___lam__0___boxed(lean_object* v___x_6601_, lean_object* v___x_6602_, lean_object* v___x_6603_, lean_object* v___y_6604_, lean_object* v___y_6605_, lean_object* v___y_6606_){
_start:
{
lean_object* v_res_6607_; 
v_res_6607_ = l_Lean_Elab_Tactic_NormCast_elabAddElim___lam__0(v___x_6601_, v___x_6602_, v___x_6603_, v___y_6604_, v___y_6605_);
return v_res_6607_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__4(void){
_start:
{
lean_object* v___x_6617_; 
v___x_6617_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_6617_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5(void){
_start:
{
lean_object* v___x_6618_; lean_object* v___x_6619_; 
v___x_6618_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__4, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__4_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__4);
v___x_6619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6619_, 0, v___x_6618_);
return v___x_6619_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__6(void){
_start:
{
lean_object* v___x_6620_; lean_object* v___x_6621_; lean_object* v___x_6622_; 
v___x_6620_ = lean_unsigned_to_nat(32u);
v___x_6621_ = lean_mk_empty_array_with_capacity(v___x_6620_);
v___x_6622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6622_, 0, v___x_6621_);
return v___x_6622_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7(void){
_start:
{
size_t v___x_6623_; lean_object* v___x_6624_; lean_object* v___x_6625_; lean_object* v___x_6626_; lean_object* v___x_6627_; lean_object* v___x_6628_; 
v___x_6623_ = ((size_t)5ULL);
v___x_6624_ = lean_unsigned_to_nat(0u);
v___x_6625_ = lean_unsigned_to_nat(32u);
v___x_6626_ = lean_mk_empty_array_with_capacity(v___x_6625_);
v___x_6627_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__6, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__6_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__6);
v___x_6628_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6628_, 0, v___x_6627_);
lean_ctor_set(v___x_6628_, 1, v___x_6626_);
lean_ctor_set(v___x_6628_, 2, v___x_6624_);
lean_ctor_set(v___x_6628_, 3, v___x_6624_);
lean_ctor_set_usize(v___x_6628_, 4, v___x_6623_);
return v___x_6628_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__8(void){
_start:
{
lean_object* v___x_6629_; lean_object* v___x_6630_; lean_object* v___x_6631_; lean_object* v___x_6632_; 
v___x_6629_ = lean_box(1);
v___x_6630_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7);
v___x_6631_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5);
v___x_6632_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6632_, 0, v___x_6631_);
lean_ctor_set(v___x_6632_, 1, v___x_6630_);
lean_ctor_set(v___x_6632_, 2, v___x_6629_);
return v___x_6632_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__10(void){
_start:
{
lean_object* v___x_6635_; lean_object* v___x_6636_; lean_object* v___x_6637_; 
v___x_6635_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5);
v___x_6636_ = lean_unsigned_to_nat(0u);
v___x_6637_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_6637_, 0, v___x_6636_);
lean_ctor_set(v___x_6637_, 1, v___x_6636_);
lean_ctor_set(v___x_6637_, 2, v___x_6636_);
lean_ctor_set(v___x_6637_, 3, v___x_6635_);
lean_ctor_set(v___x_6637_, 4, v___x_6635_);
lean_ctor_set(v___x_6637_, 5, v___x_6635_);
lean_ctor_set(v___x_6637_, 6, v___x_6635_);
lean_ctor_set(v___x_6637_, 7, v___x_6635_);
lean_ctor_set(v___x_6637_, 8, v___x_6635_);
return v___x_6637_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__11(void){
_start:
{
lean_object* v___x_6638_; lean_object* v___x_6639_; 
v___x_6638_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5);
v___x_6639_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6639_, 0, v___x_6638_);
lean_ctor_set(v___x_6639_, 1, v___x_6638_);
lean_ctor_set(v___x_6639_, 2, v___x_6638_);
lean_ctor_set(v___x_6639_, 3, v___x_6638_);
lean_ctor_set(v___x_6639_, 4, v___x_6638_);
lean_ctor_set(v___x_6639_, 5, v___x_6638_);
return v___x_6639_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__12(void){
_start:
{
lean_object* v___x_6640_; lean_object* v___x_6641_; 
v___x_6640_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5);
v___x_6641_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6641_, 0, v___x_6640_);
lean_ctor_set(v___x_6641_, 1, v___x_6640_);
lean_ctor_set(v___x_6641_, 2, v___x_6640_);
lean_ctor_set(v___x_6641_, 3, v___x_6640_);
lean_ctor_set(v___x_6641_, 4, v___x_6640_);
return v___x_6641_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__13(void){
_start:
{
lean_object* v___x_6642_; lean_object* v___x_6643_; lean_object* v___x_6644_; lean_object* v___x_6645_; lean_object* v___x_6646_; lean_object* v___x_6647_; 
v___x_6642_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__12, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__12_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__12);
v___x_6643_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7);
v___x_6644_ = lean_box(1);
v___x_6645_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__11, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__11_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__11);
v___x_6646_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__10, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__10_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__10);
v___x_6647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6647_, 0, v___x_6646_);
lean_ctor_set(v___x_6647_, 1, v___x_6645_);
lean_ctor_set(v___x_6647_, 2, v___x_6644_);
lean_ctor_set(v___x_6647_, 3, v___x_6643_);
lean_ctor_set(v___x_6647_, 4, v___x_6642_);
return v___x_6647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim(lean_object* v_stx_6648_, lean_object* v_a_6649_, lean_object* v_a_6650_){
_start:
{
lean_object* v___x_6652_; uint8_t v___x_6653_; 
v___x_6652_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__1));
lean_inc(v_stx_6648_);
v___x_6653_ = l_Lean_Syntax_isOfKind(v_stx_6648_, v___x_6652_);
if (v___x_6653_ == 0)
{
lean_object* v___x_6654_; 
lean_dec_ref(v_a_6649_);
lean_dec(v_stx_6648_);
v___x_6654_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg();
return v___x_6654_;
}
else
{
lean_object* v___x_6655_; lean_object* v___x_6656_; lean_object* v___x_6657_; uint8_t v___x_6658_; 
v___x_6655_ = lean_unsigned_to_nat(1u);
v___x_6656_ = l_Lean_Syntax_getArg(v_stx_6648_, v___x_6655_);
lean_dec(v_stx_6648_);
v___x_6657_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__3));
lean_inc(v___x_6656_);
v___x_6658_ = l_Lean_Syntax_isOfKind(v___x_6656_, v___x_6657_);
if (v___x_6658_ == 0)
{
lean_object* v___x_6659_; 
lean_dec(v___x_6656_);
lean_dec_ref(v_a_6649_);
v___x_6659_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg();
return v___x_6659_;
}
else
{
lean_object* v___x_6660_; lean_object* v___x_6661_; uint8_t v___x_6662_; lean_object* v___x_6663_; lean_object* v___x_6664_; lean_object* v___x_6665_; lean_object* v___x_6666_; lean_object* v___x_6667_; lean_object* v___x_6668_; lean_object* v___f_6669_; lean_object* v___x_6670_; 
v___x_6660_ = lean_unsigned_to_nat(0u);
v___x_6661_ = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
v___x_6662_ = 0;
v___x_6663_ = lean_box(1);
v___x_6664_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__8, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__8);
v___x_6665_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__9));
v___x_6666_ = lean_box(0);
v___x_6667_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6667_, 0, v___x_6661_);
lean_ctor_set(v___x_6667_, 1, v___x_6663_);
lean_ctor_set(v___x_6667_, 2, v___x_6664_);
lean_ctor_set(v___x_6667_, 3, v___x_6665_);
lean_ctor_set(v___x_6667_, 4, v___x_6666_);
lean_ctor_set(v___x_6667_, 5, v___x_6660_);
lean_ctor_set(v___x_6667_, 6, v___x_6666_);
lean_ctor_set_uint8(v___x_6667_, sizeof(void*)*7, v___x_6662_);
lean_ctor_set_uint8(v___x_6667_, sizeof(void*)*7 + 1, v___x_6662_);
lean_ctor_set_uint8(v___x_6667_, sizeof(void*)*7 + 2, v___x_6662_);
lean_ctor_set_uint8(v___x_6667_, sizeof(void*)*7 + 3, v___x_6658_);
v___x_6668_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__13, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__13_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__13);
v___f_6669_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___lam__0___boxed), 6, 3);
lean_closure_set(v___f_6669_, 0, v___x_6668_);
lean_closure_set(v___f_6669_, 1, v___x_6656_);
lean_closure_set(v___f_6669_, 2, v___x_6667_);
v___x_6670_ = l_Lean_Elab_Command_liftCoreM___redArg(v___f_6669_, v_a_6649_, v_a_6650_);
return v___x_6670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___boxed(lean_object* v_stx_6671_, lean_object* v_a_6672_, lean_object* v_a_6673_, lean_object* v_a_6674_){
_start:
{
lean_object* v_res_6675_; 
v_res_6675_ = l_Lean_Elab_Tactic_NormCast_elabAddElim(v_stx_6671_, v_a_6672_, v_a_6673_);
lean_dec(v_a_6673_);
return v_res_6675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1(){
_start:
{
lean_object* v___x_6684_; lean_object* v___x_6685_; lean_object* v___x_6686_; lean_object* v___x_6687_; lean_object* v___x_6688_; 
v___x_6684_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_6685_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__1));
v___x_6686_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1));
v___x_6687_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___boxed), 4, 0);
v___x_6688_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6684_, v___x_6685_, v___x_6686_, v___x_6687_);
return v___x_6688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___boxed(lean_object* v_a_6689_){
_start:
{
lean_object* v_res_6690_; 
v_res_6690_ = l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1();
return v_res_6690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3(){
_start:
{
lean_object* v___x_6717_; lean_object* v___x_6718_; lean_object* v___x_6719_; 
v___x_6717_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1));
v___x_6718_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__6));
v___x_6719_ = l_Lean_addBuiltinDeclarationRanges(v___x_6717_, v___x_6718_);
return v___x_6719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___boxed(lean_object* v_a_6720_){
_start:
{
lean_object* v_res_6721_; 
v_res_6721_ = l_Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3();
return v_res_6721_;
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

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
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_realizeGlobalConstNoOverload(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_NormCast_addElim(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_NormCast_pushCastExt;
lean_object* l_Lean_Meta_SimpExtension_getTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Lean_Meta_Simp_Result_mkCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Elab_Term_throwTypeMismatchError___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabTerm(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_synthesizeSyntheticMVars(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Lean_Elab_Term_tryPostpone(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
lean_object* l_Lean_Elab_Tactic_simpLocation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_applySimpResultToLocalDecl(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkSimpContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Context_setFailIfUnchanged(lean_object*, uint8_t);
lean_object* l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_MVarId_getNondepPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getFVarIds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_Parser_Tactic_getConfigItems(lean_object*);
lean_object* l_Lean_Elab_Tactic_mkConfigItemViews(lean_object*);
lean_object* l_Lean_Elab_Tactic_elabConfig(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasSyntheticSorry(lean_object*);
uint8_t l_Lean_Expr_hasSorry(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandLocation(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Elab_Term_withExpectedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Term_termElabAttribute;
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
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "proving: "};
static const lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__3 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__3_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__4;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__1_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "discharging: "};
static const lean_object* l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8(lean_object*, lean_object*);
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
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1;
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__14;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__15 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__15_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__16;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__17 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__17_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__20_value;
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "elabModCast"};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__5_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__7_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__0_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__10_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 229, 224, 191, 239, 182, 82, 45)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 228, 31, 241, 142, 75, 34, 234)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(209) << 1) | 1)),((lean_object*)(((size_t)(29) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(224) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__0_value),((lean_object*)(((size_t)(29) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(209) << 1) | 1)),((lean_object*)(((size_t)(33) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(209) << 1) | 1)),((lean_object*)(((size_t)(44) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__3_value),((lean_object*)(((size_t)(33) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__4_value),((lean_object*)(((size_t)(44) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "evalNormCast0"};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__5_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__7_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__0_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__10_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 229, 224, 191, 239, 182, 82, 45)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 95, 7, 173, 250, 13, 126, 205)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(241) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(253) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(241) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(241) << 1) | 1)),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__4_value),((lean_object*)(((size_t)(17) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Conv"};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "normCast"};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__5_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__0_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(51, 212, 92, 235, 115, 8, 100, 36)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(204, 210, 228, 19, 50, 14, 27, 75)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "evalConvNormCast"};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__5_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__7_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__0_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__10_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 229, 224, 191, 239, 182, 82, 45)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(13, 37, 228, 165, 116, 249, 109, 194)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(256) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(258) << 1) | 1)),((lean_object*)(((size_t)(41) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__1_value),((lean_object*)(((size_t)(41) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(256) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(256) << 1) | 1)),((lean_object*)(((size_t)(20) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__4_value),((lean_object*)(((size_t)(20) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "pushCast"};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__5_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__0_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 171, 212, 196, 187, 204, 157, 118)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "evalPushCast"};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__5_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__7_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__0_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__10_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 229, 224, 191, 239, 182, 82, 45)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(91, 23, 255, 99, 127, 149, 218, 153)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(261) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(266) << 1) | 1)),((lean_object*)(((size_t)(78) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__1_value),((lean_object*)(((size_t)(78) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(261) << 1) | 1)),((lean_object*)(((size_t)(4) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(261) << 1) | 1)),((lean_object*)(((size_t)(16) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__3_value),((lean_object*)(((size_t)(4) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__4_value),((lean_object*)(((size_t)(16) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___boxed(lean_object*);
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
static const lean_string_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "elabAddElim"};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__5_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__7_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__0_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__10_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(63, 229, 224, 191, 239, 182, 82, 45)}};
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1_value_aux_3),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(132, 193, 199, 111, 225, 102, 144, 218)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___boxed(lean_object*);
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(269) << 1) | 1)),((lean_object*)(((size_t)(54) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__0 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(274) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__1 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__1_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__0_value),((lean_object*)(((size_t)(54) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__1_value),((lean_object*)(((size_t)(31) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__2 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__2_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(269) << 1) | 1)),((lean_object*)(((size_t)(58) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__3 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(269) << 1) | 1)),((lean_object*)(((size_t)(69) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__4 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__4_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__3_value),((lean_object*)(((size_t)(58) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__4_value),((lean_object*)(((size_t)(69) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__5 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__5_value;
static const lean_ctor_object l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__2_value),((lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__5_value)}};
static const lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__6 = (const lean_object*)&l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3();
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___boxed(lean_object*);
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
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = lean_unsigned_to_nat(32u);
v___x_289_ = lean_mk_empty_array_with_capacity(v___x_288_);
v___x_290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
return v___x_290_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_291_ = ((size_t)5ULL);
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = lean_unsigned_to_nat(32u);
v___x_294_ = lean_mk_empty_array_with_capacity(v___x_293_);
v___x_295_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__0);
v___x_296_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v___x_294_);
lean_ctor_set(v___x_296_, 2, v___x_292_);
lean_ctor_set(v___x_296_, 3, v___x_292_);
lean_ctor_set_usize(v___x_296_, 4, v___x_291_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(lean_object* v___y_297_){
_start:
{
lean_object* v___x_299_; lean_object* v_traceState_300_; lean_object* v_traces_301_; lean_object* v___x_302_; lean_object* v_traceState_303_; lean_object* v_env_304_; lean_object* v_nextMacroScope_305_; lean_object* v_ngen_306_; lean_object* v_auxDeclNGen_307_; lean_object* v_cache_308_; lean_object* v_messages_309_; lean_object* v_infoState_310_; lean_object* v_snapshotTasks_311_; lean_object* v_newDecls_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_331_; 
v___x_299_ = lean_st_ref_get(v___y_297_);
v_traceState_300_ = lean_ctor_get(v___x_299_, 4);
lean_inc_ref(v_traceState_300_);
lean_dec(v___x_299_);
v_traces_301_ = lean_ctor_get(v_traceState_300_, 0);
lean_inc_ref(v_traces_301_);
lean_dec_ref(v_traceState_300_);
v___x_302_ = lean_st_ref_take(v___y_297_);
v_traceState_303_ = lean_ctor_get(v___x_302_, 4);
v_env_304_ = lean_ctor_get(v___x_302_, 0);
v_nextMacroScope_305_ = lean_ctor_get(v___x_302_, 1);
v_ngen_306_ = lean_ctor_get(v___x_302_, 2);
v_auxDeclNGen_307_ = lean_ctor_get(v___x_302_, 3);
v_cache_308_ = lean_ctor_get(v___x_302_, 5);
v_messages_309_ = lean_ctor_get(v___x_302_, 6);
v_infoState_310_ = lean_ctor_get(v___x_302_, 7);
v_snapshotTasks_311_ = lean_ctor_get(v___x_302_, 8);
v_newDecls_312_ = lean_ctor_get(v___x_302_, 9);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_331_ == 0)
{
v___x_314_ = v___x_302_;
v_isShared_315_ = v_isSharedCheck_331_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_newDecls_312_);
lean_inc(v_snapshotTasks_311_);
lean_inc(v_infoState_310_);
lean_inc(v_messages_309_);
lean_inc(v_cache_308_);
lean_inc(v_traceState_303_);
lean_inc(v_auxDeclNGen_307_);
lean_inc(v_ngen_306_);
lean_inc(v_nextMacroScope_305_);
lean_inc(v_env_304_);
lean_dec(v___x_302_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_331_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
uint64_t v_tid_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_329_; 
v_tid_316_ = lean_ctor_get_uint64(v_traceState_303_, sizeof(void*)*1);
v_isSharedCheck_329_ = !lean_is_exclusive(v_traceState_303_);
if (v_isSharedCheck_329_ == 0)
{
lean_object* v_unused_330_; 
v_unused_330_ = lean_ctor_get(v_traceState_303_, 0);
lean_dec(v_unused_330_);
v___x_318_ = v_traceState_303_;
v_isShared_319_ = v_isSharedCheck_329_;
goto v_resetjp_317_;
}
else
{
lean_dec(v_traceState_303_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_329_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_320_; lean_object* v___x_322_; 
v___x_320_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__1);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 0, v___x_320_);
v___x_322_ = v___x_318_;
goto v_reusejp_321_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_320_);
lean_ctor_set_uint64(v_reuseFailAlloc_328_, sizeof(void*)*1, v_tid_316_);
v___x_322_ = v_reuseFailAlloc_328_;
goto v_reusejp_321_;
}
v_reusejp_321_:
{
lean_object* v___x_324_; 
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 4, v___x_322_);
v___x_324_ = v___x_314_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_env_304_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_nextMacroScope_305_);
lean_ctor_set(v_reuseFailAlloc_327_, 2, v_ngen_306_);
lean_ctor_set(v_reuseFailAlloc_327_, 3, v_auxDeclNGen_307_);
lean_ctor_set(v_reuseFailAlloc_327_, 4, v___x_322_);
lean_ctor_set(v_reuseFailAlloc_327_, 5, v_cache_308_);
lean_ctor_set(v_reuseFailAlloc_327_, 6, v_messages_309_);
lean_ctor_set(v_reuseFailAlloc_327_, 7, v_infoState_310_);
lean_ctor_set(v_reuseFailAlloc_327_, 8, v_snapshotTasks_311_);
lean_ctor_set(v_reuseFailAlloc_327_, 9, v_newDecls_312_);
v___x_324_ = v_reuseFailAlloc_327_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_st_ref_set(v___y_297_, v___x_324_);
v___x_326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_326_, 0, v_traces_301_);
return v___x_326_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___boxed(lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___y_332_);
lean_dec(v___y_332_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0(lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___y_338_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___boxed(lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0(v___y_341_, v___y_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
return v_res_346_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(lean_object* v_opts_347_, lean_object* v_opt_348_){
_start:
{
lean_object* v_name_349_; lean_object* v_defValue_350_; lean_object* v_map_351_; lean_object* v___x_352_; 
v_name_349_ = lean_ctor_get(v_opt_348_, 0);
v_defValue_350_ = lean_ctor_get(v_opt_348_, 1);
v_map_351_ = lean_ctor_get(v_opts_347_, 0);
v___x_352_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_351_, v_name_349_);
if (lean_obj_tag(v___x_352_) == 0)
{
uint8_t v___x_353_; 
v___x_353_ = lean_unbox(v_defValue_350_);
return v___x_353_;
}
else
{
lean_object* v_val_354_; 
v_val_354_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_val_354_);
lean_dec_ref(v___x_352_);
if (lean_obj_tag(v_val_354_) == 1)
{
uint8_t v_v_355_; 
v_v_355_ = lean_ctor_get_uint8(v_val_354_, 0);
lean_dec_ref(v_val_354_);
return v_v_355_;
}
else
{
uint8_t v___x_356_; 
lean_dec(v_val_354_);
v___x_356_ = lean_unbox(v_defValue_350_);
return v___x_356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___boxed(lean_object* v_opts_357_, lean_object* v_opt_358_){
_start:
{
uint8_t v_res_359_; lean_object* v_r_360_; 
v_res_359_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_opts_357_, v_opt_358_);
lean_dec_ref(v_opt_358_);
lean_dec_ref(v_opts_357_);
v_r_360_ = lean_box(v_res_359_);
return v_r_360_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__1(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__0));
v___x_363_ = l_Lean_stringToMessageData(v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0(lean_object* v_a_364_, lean_object* v_b_365_, lean_object* v_x_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_Meta_mkEq(v_a_364_, v_b_365_, v___y_367_, v___y_368_, v___y_369_, v___y_370_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_383_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_383_ == 0)
{
v___x_375_ = v___x_372_;
v_isShared_376_ = v_isSharedCheck_383_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_372_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_383_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
v___x_377_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__1, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__1);
v___x_378_ = l_Lean_MessageData_ofExpr(v_a_373_);
v___x_379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_377_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_379_);
v___x_381_ = v___x_375_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
v_a_384_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_372_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_372_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___boxed(lean_object* v_a_392_, lean_object* v_b_393_, lean_object* v_x_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0(v_a_392_, v_b_393_, v_x_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec_ref(v_x_394_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__4(size_t v_sz_401_, size_t v_i_402_, lean_object* v_bs_403_){
_start:
{
uint8_t v___x_404_; 
v___x_404_ = lean_usize_dec_lt(v_i_402_, v_sz_401_);
if (v___x_404_ == 0)
{
return v_bs_403_;
}
else
{
lean_object* v_v_405_; lean_object* v_msg_406_; lean_object* v___x_407_; lean_object* v_bs_x27_408_; size_t v___x_409_; size_t v___x_410_; lean_object* v___x_411_; 
v_v_405_ = lean_array_uget_borrowed(v_bs_403_, v_i_402_);
v_msg_406_ = lean_ctor_get(v_v_405_, 1);
lean_inc_ref(v_msg_406_);
v___x_407_ = lean_unsigned_to_nat(0u);
v_bs_x27_408_ = lean_array_uset(v_bs_403_, v_i_402_, v___x_407_);
v___x_409_ = ((size_t)1ULL);
v___x_410_ = lean_usize_add(v_i_402_, v___x_409_);
v___x_411_ = lean_array_uset(v_bs_x27_408_, v_i_402_, v_msg_406_);
v_i_402_ = v___x_410_;
v_bs_403_ = v___x_411_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__4___boxed(lean_object* v_sz_413_, lean_object* v_i_414_, lean_object* v_bs_415_){
_start:
{
size_t v_sz_boxed_416_; size_t v_i_boxed_417_; lean_object* v_res_418_; 
v_sz_boxed_416_ = lean_unbox_usize(v_sz_413_);
lean_dec(v_sz_413_);
v_i_boxed_417_ = lean_unbox_usize(v_i_414_);
lean_dec(v_i_414_);
v_res_418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__4(v_sz_boxed_416_, v_i_boxed_417_, v_bs_415_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__5(lean_object* v_msgData_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
lean_object* v___x_425_; lean_object* v_env_426_; lean_object* v___x_427_; lean_object* v_mctx_428_; lean_object* v_lctx_429_; lean_object* v_options_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_425_ = lean_st_ref_get(v___y_423_);
v_env_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc_ref(v_env_426_);
lean_dec(v___x_425_);
v___x_427_ = lean_st_ref_get(v___y_421_);
v_mctx_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc_ref(v_mctx_428_);
lean_dec(v___x_427_);
v_lctx_429_ = lean_ctor_get(v___y_420_, 2);
v_options_430_ = lean_ctor_get(v___y_422_, 2);
lean_inc_ref(v_options_430_);
lean_inc_ref(v_lctx_429_);
v___x_431_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_431_, 0, v_env_426_);
lean_ctor_set(v___x_431_, 1, v_mctx_428_);
lean_ctor_set(v___x_431_, 2, v_lctx_429_);
lean_ctor_set(v___x_431_, 3, v_options_430_);
v___x_432_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v_msgData_419_);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__5___boxed(lean_object* v_msgData_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__5(v_msgData_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_);
lean_dec(v___y_438_);
lean_dec_ref(v___y_437_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3(lean_object* v_oldTraces_441_, lean_object* v_data_442_, lean_object* v_ref_443_, lean_object* v_msg_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
lean_object* v_fileName_450_; lean_object* v_fileMap_451_; lean_object* v_options_452_; lean_object* v_currRecDepth_453_; lean_object* v_maxRecDepth_454_; lean_object* v_ref_455_; lean_object* v_currNamespace_456_; lean_object* v_openDecls_457_; lean_object* v_initHeartbeats_458_; lean_object* v_maxHeartbeats_459_; lean_object* v_quotContext_460_; lean_object* v_currMacroScope_461_; uint8_t v_diag_462_; lean_object* v_cancelTk_x3f_463_; uint8_t v_suppressElabErrors_464_; lean_object* v_inheritedTraceOptions_465_; lean_object* v___x_466_; lean_object* v_traceState_467_; lean_object* v_traces_468_; lean_object* v_ref_469_; lean_object* v___x_470_; lean_object* v___x_471_; size_t v_sz_472_; size_t v___x_473_; lean_object* v___x_474_; lean_object* v_msg_475_; lean_object* v___x_476_; lean_object* v_a_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_515_; 
v_fileName_450_ = lean_ctor_get(v___y_447_, 0);
v_fileMap_451_ = lean_ctor_get(v___y_447_, 1);
v_options_452_ = lean_ctor_get(v___y_447_, 2);
v_currRecDepth_453_ = lean_ctor_get(v___y_447_, 3);
v_maxRecDepth_454_ = lean_ctor_get(v___y_447_, 4);
v_ref_455_ = lean_ctor_get(v___y_447_, 5);
v_currNamespace_456_ = lean_ctor_get(v___y_447_, 6);
v_openDecls_457_ = lean_ctor_get(v___y_447_, 7);
v_initHeartbeats_458_ = lean_ctor_get(v___y_447_, 8);
v_maxHeartbeats_459_ = lean_ctor_get(v___y_447_, 9);
v_quotContext_460_ = lean_ctor_get(v___y_447_, 10);
v_currMacroScope_461_ = lean_ctor_get(v___y_447_, 11);
v_diag_462_ = lean_ctor_get_uint8(v___y_447_, sizeof(void*)*14);
v_cancelTk_x3f_463_ = lean_ctor_get(v___y_447_, 12);
v_suppressElabErrors_464_ = lean_ctor_get_uint8(v___y_447_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_465_ = lean_ctor_get(v___y_447_, 13);
v___x_466_ = lean_st_ref_get(v___y_448_);
v_traceState_467_ = lean_ctor_get(v___x_466_, 4);
lean_inc_ref(v_traceState_467_);
lean_dec(v___x_466_);
v_traces_468_ = lean_ctor_get(v_traceState_467_, 0);
lean_inc_ref(v_traces_468_);
lean_dec_ref(v_traceState_467_);
v_ref_469_ = l_Lean_replaceRef(v_ref_443_, v_ref_455_);
lean_inc_ref(v_inheritedTraceOptions_465_);
lean_inc(v_cancelTk_x3f_463_);
lean_inc(v_currMacroScope_461_);
lean_inc(v_quotContext_460_);
lean_inc(v_maxHeartbeats_459_);
lean_inc(v_initHeartbeats_458_);
lean_inc(v_openDecls_457_);
lean_inc(v_currNamespace_456_);
lean_inc(v_maxRecDepth_454_);
lean_inc(v_currRecDepth_453_);
lean_inc_ref(v_options_452_);
lean_inc_ref(v_fileMap_451_);
lean_inc_ref(v_fileName_450_);
v___x_470_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_470_, 0, v_fileName_450_);
lean_ctor_set(v___x_470_, 1, v_fileMap_451_);
lean_ctor_set(v___x_470_, 2, v_options_452_);
lean_ctor_set(v___x_470_, 3, v_currRecDepth_453_);
lean_ctor_set(v___x_470_, 4, v_maxRecDepth_454_);
lean_ctor_set(v___x_470_, 5, v_ref_469_);
lean_ctor_set(v___x_470_, 6, v_currNamespace_456_);
lean_ctor_set(v___x_470_, 7, v_openDecls_457_);
lean_ctor_set(v___x_470_, 8, v_initHeartbeats_458_);
lean_ctor_set(v___x_470_, 9, v_maxHeartbeats_459_);
lean_ctor_set(v___x_470_, 10, v_quotContext_460_);
lean_ctor_set(v___x_470_, 11, v_currMacroScope_461_);
lean_ctor_set(v___x_470_, 12, v_cancelTk_x3f_463_);
lean_ctor_set(v___x_470_, 13, v_inheritedTraceOptions_465_);
lean_ctor_set_uint8(v___x_470_, sizeof(void*)*14, v_diag_462_);
lean_ctor_set_uint8(v___x_470_, sizeof(void*)*14 + 1, v_suppressElabErrors_464_);
v___x_471_ = l_Lean_PersistentArray_toArray___redArg(v_traces_468_);
lean_dec_ref(v_traces_468_);
v_sz_472_ = lean_array_size(v___x_471_);
v___x_473_ = ((size_t)0ULL);
v___x_474_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__4(v_sz_472_, v___x_473_, v___x_471_);
v_msg_475_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_475_, 0, v_data_442_);
lean_ctor_set(v_msg_475_, 1, v_msg_444_);
lean_ctor_set(v_msg_475_, 2, v___x_474_);
v___x_476_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__5(v_msg_475_, v___y_445_, v___y_446_, v___x_470_, v___y_448_);
lean_dec_ref(v___x_470_);
v_a_477_ = lean_ctor_get(v___x_476_, 0);
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_476_);
if (v_isSharedCheck_515_ == 0)
{
v___x_479_ = v___x_476_;
v_isShared_480_ = v_isSharedCheck_515_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_a_477_);
lean_dec(v___x_476_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_515_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v_traceState_482_; lean_object* v_env_483_; lean_object* v_nextMacroScope_484_; lean_object* v_ngen_485_; lean_object* v_auxDeclNGen_486_; lean_object* v_cache_487_; lean_object* v_messages_488_; lean_object* v_infoState_489_; lean_object* v_snapshotTasks_490_; lean_object* v_newDecls_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_514_; 
v___x_481_ = lean_st_ref_take(v___y_448_);
v_traceState_482_ = lean_ctor_get(v___x_481_, 4);
v_env_483_ = lean_ctor_get(v___x_481_, 0);
v_nextMacroScope_484_ = lean_ctor_get(v___x_481_, 1);
v_ngen_485_ = lean_ctor_get(v___x_481_, 2);
v_auxDeclNGen_486_ = lean_ctor_get(v___x_481_, 3);
v_cache_487_ = lean_ctor_get(v___x_481_, 5);
v_messages_488_ = lean_ctor_get(v___x_481_, 6);
v_infoState_489_ = lean_ctor_get(v___x_481_, 7);
v_snapshotTasks_490_ = lean_ctor_get(v___x_481_, 8);
v_newDecls_491_ = lean_ctor_get(v___x_481_, 9);
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_514_ == 0)
{
v___x_493_ = v___x_481_;
v_isShared_494_ = v_isSharedCheck_514_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_newDecls_491_);
lean_inc(v_snapshotTasks_490_);
lean_inc(v_infoState_489_);
lean_inc(v_messages_488_);
lean_inc(v_cache_487_);
lean_inc(v_traceState_482_);
lean_inc(v_auxDeclNGen_486_);
lean_inc(v_ngen_485_);
lean_inc(v_nextMacroScope_484_);
lean_inc(v_env_483_);
lean_dec(v___x_481_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_514_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
uint64_t v_tid_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_512_; 
v_tid_495_ = lean_ctor_get_uint64(v_traceState_482_, sizeof(void*)*1);
v_isSharedCheck_512_ = !lean_is_exclusive(v_traceState_482_);
if (v_isSharedCheck_512_ == 0)
{
lean_object* v_unused_513_; 
v_unused_513_ = lean_ctor_get(v_traceState_482_, 0);
lean_dec(v_unused_513_);
v___x_497_ = v_traceState_482_;
v_isShared_498_ = v_isSharedCheck_512_;
goto v_resetjp_496_;
}
else
{
lean_dec(v_traceState_482_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_512_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_499_, 0, v_ref_443_);
lean_ctor_set(v___x_499_, 1, v_a_477_);
v___x_500_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_441_, v___x_499_);
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_500_);
v___x_502_ = v___x_497_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_500_);
lean_ctor_set_uint64(v_reuseFailAlloc_511_, sizeof(void*)*1, v_tid_495_);
v___x_502_ = v_reuseFailAlloc_511_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_504_; 
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 4, v___x_502_);
v___x_504_ = v___x_493_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_env_483_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_nextMacroScope_484_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v_ngen_485_);
lean_ctor_set(v_reuseFailAlloc_510_, 3, v_auxDeclNGen_486_);
lean_ctor_set(v_reuseFailAlloc_510_, 4, v___x_502_);
lean_ctor_set(v_reuseFailAlloc_510_, 5, v_cache_487_);
lean_ctor_set(v_reuseFailAlloc_510_, 6, v_messages_488_);
lean_ctor_set(v_reuseFailAlloc_510_, 7, v_infoState_489_);
lean_ctor_set(v_reuseFailAlloc_510_, 8, v_snapshotTasks_490_);
lean_ctor_set(v_reuseFailAlloc_510_, 9, v_newDecls_491_);
v___x_504_ = v_reuseFailAlloc_510_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_508_; 
v___x_505_ = lean_st_ref_set(v___y_448_, v___x_504_);
v___x_506_ = lean_box(0);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 0, v___x_506_);
v___x_508_ = v___x_479_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3___boxed(lean_object* v_oldTraces_516_, lean_object* v_data_517_, lean_object* v_ref_518_, lean_object* v_msg_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3(v_oldTraces_516_, v_data_517_, v_ref_518_, v_msg_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
return v_res_525_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__2(lean_object* v_e_526_){
_start:
{
if (lean_obj_tag(v_e_526_) == 0)
{
uint8_t v___x_527_; 
v___x_527_ = 2;
return v___x_527_;
}
else
{
lean_object* v_a_528_; 
v_a_528_ = lean_ctor_get(v_e_526_, 0);
if (lean_obj_tag(v_a_528_) == 0)
{
uint8_t v___x_529_; 
v___x_529_ = 1;
return v___x_529_;
}
else
{
uint8_t v___x_530_; 
v___x_530_ = 0;
return v___x_530_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__2___boxed(lean_object* v_e_531_){
_start:
{
uint8_t v_res_532_; lean_object* v_r_533_; 
v_res_532_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__2(v_e_531_);
lean_dec_ref(v_e_531_);
v_r_533_ = lean_box(v_res_532_);
return v_r_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__5(lean_object* v_opts_534_, lean_object* v_opt_535_){
_start:
{
lean_object* v_name_536_; lean_object* v_defValue_537_; lean_object* v_map_538_; lean_object* v___x_539_; 
v_name_536_ = lean_ctor_get(v_opt_535_, 0);
v_defValue_537_ = lean_ctor_get(v_opt_535_, 1);
v_map_538_ = lean_ctor_get(v_opts_534_, 0);
v___x_539_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_538_, v_name_536_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_inc(v_defValue_537_);
return v_defValue_537_;
}
else
{
lean_object* v_val_540_; 
v_val_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_val_540_);
lean_dec_ref(v___x_539_);
if (lean_obj_tag(v_val_540_) == 3)
{
lean_object* v_v_541_; 
v_v_541_ = lean_ctor_get(v_val_540_, 0);
lean_inc(v_v_541_);
lean_dec_ref(v_val_540_);
return v_v_541_;
}
else
{
lean_dec(v_val_540_);
lean_inc(v_defValue_537_);
return v_defValue_537_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__5___boxed(lean_object* v_opts_542_, lean_object* v_opt_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__5(v_opts_542_, v_opt_543_);
lean_dec_ref(v_opt_543_);
lean_dec_ref(v_opts_542_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4___redArg(lean_object* v_x_545_){
_start:
{
if (lean_obj_tag(v_x_545_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_554_; 
v_a_547_ = lean_ctor_get(v_x_545_, 0);
v_isSharedCheck_554_ = !lean_is_exclusive(v_x_545_);
if (v_isSharedCheck_554_ == 0)
{
v___x_549_ = v_x_545_;
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_a_547_);
lean_dec(v_x_545_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_554_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_552_; 
if (v_isShared_550_ == 0)
{
lean_ctor_set_tag(v___x_549_, 1);
v___x_552_ = v___x_549_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_553_; 
v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
v___x_552_ = v_reuseFailAlloc_553_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
return v___x_552_;
}
}
}
else
{
lean_object* v_a_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_562_; 
v_a_555_ = lean_ctor_get(v_x_545_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v_x_545_);
if (v_isSharedCheck_562_ == 0)
{
v___x_557_ = v_x_545_;
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_a_555_);
lean_dec(v_x_545_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_562_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
lean_ctor_set_tag(v___x_557_, 0);
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
v___x_560_ = v_reuseFailAlloc_561_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
return v___x_560_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4___redArg___boxed(lean_object* v_x_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4___redArg(v_x_563_);
return v_res_565_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__0));
v___x_568_ = l_Lean_stringToMessageData(v___x_567_);
return v___x_568_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2(void){
_start:
{
lean_object* v___x_569_; double v___x_570_; 
v___x_569_ = lean_unsigned_to_nat(0u);
v___x_570_ = lean_float_of_nat(v___x_569_);
return v___x_570_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__4(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__3));
v___x_573_ = l_Lean_stringToMessageData(v___x_572_);
return v___x_573_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__5(void){
_start:
{
lean_object* v___x_574_; double v___x_575_; 
v___x_574_ = lean_unsigned_to_nat(1000u);
v___x_575_ = lean_float_of_nat(v___x_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(lean_object* v_cls_576_, uint8_t v_collapsed_577_, lean_object* v_tag_578_, lean_object* v_opts_579_, uint8_t v_clsEnabled_580_, lean_object* v_oldTraces_581_, lean_object* v_msg_582_, lean_object* v_resStartStop_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v_fst_589_; lean_object* v_snd_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_689_; 
v_fst_589_ = lean_ctor_get(v_resStartStop_583_, 0);
v_snd_590_ = lean_ctor_get(v_resStartStop_583_, 1);
v_isSharedCheck_689_ = !lean_is_exclusive(v_resStartStop_583_);
if (v_isSharedCheck_689_ == 0)
{
v___x_592_ = v_resStartStop_583_;
v_isShared_593_ = v_isSharedCheck_689_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_snd_590_);
lean_inc(v_fst_589_);
lean_dec(v_resStartStop_583_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_689_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___y_595_; lean_object* v___y_596_; lean_object* v_data_597_; lean_object* v_fst_608_; lean_object* v_snd_609_; lean_object* v___x_611_; uint8_t v_isShared_612_; uint8_t v_isSharedCheck_688_; 
v_fst_608_ = lean_ctor_get(v_snd_590_, 0);
v_snd_609_ = lean_ctor_get(v_snd_590_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v_snd_590_);
if (v_isSharedCheck_688_ == 0)
{
v___x_611_ = v_snd_590_;
v_isShared_612_ = v_isSharedCheck_688_;
goto v_resetjp_610_;
}
else
{
lean_inc(v_snd_609_);
lean_inc(v_fst_608_);
lean_dec(v_snd_590_);
v___x_611_ = lean_box(0);
v_isShared_612_ = v_isSharedCheck_688_;
goto v_resetjp_610_;
}
v___jp_594_:
{
lean_object* v___x_598_; 
lean_inc(v___y_596_);
v___x_598_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3(v_oldTraces_581_, v_data_597_, v___y_596_, v___y_595_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v___x_599_; 
lean_dec_ref(v___x_598_);
v___x_599_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4___redArg(v_fst_589_);
return v___x_599_;
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
lean_dec(v_fst_589_);
v_a_600_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_598_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_598_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
v_resetjp_610_:
{
lean_object* v___x_613_; uint8_t v___x_614_; lean_object* v___y_616_; lean_object* v_a_617_; uint8_t v___y_641_; double v___y_673_; 
v___x_613_ = l_Lean_trace_profiler;
v___x_614_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_opts_579_, v___x_613_);
if (v___x_614_ == 0)
{
v___y_641_ = v___x_614_;
goto v___jp_640_;
}
else
{
lean_object* v___x_678_; uint8_t v___x_679_; 
v___x_678_ = l_Lean_trace_profiler_useHeartbeats;
v___x_679_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_opts_579_, v___x_678_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; lean_object* v___x_681_; double v___x_682_; double v___x_683_; double v___x_684_; 
v___x_680_ = l_Lean_trace_profiler_threshold;
v___x_681_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__5(v_opts_579_, v___x_680_);
v___x_682_ = lean_float_of_nat(v___x_681_);
v___x_683_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__5);
v___x_684_ = lean_float_div(v___x_682_, v___x_683_);
v___y_673_ = v___x_684_;
goto v___jp_672_;
}
else
{
lean_object* v___x_685_; lean_object* v___x_686_; double v___x_687_; 
v___x_685_ = l_Lean_trace_profiler_threshold;
v___x_686_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__5(v_opts_579_, v___x_685_);
v___x_687_ = lean_float_of_nat(v___x_686_);
v___y_673_ = v___x_687_;
goto v___jp_672_;
}
}
v___jp_615_:
{
uint8_t v_result_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_623_; 
v_result_618_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__2(v_fst_589_);
v___x_619_ = l_Lean_TraceResult_toEmoji(v_result_618_);
v___x_620_ = l_Lean_stringToMessageData(v___x_619_);
v___x_621_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1);
if (v_isShared_612_ == 0)
{
lean_ctor_set_tag(v___x_611_, 7);
lean_ctor_set(v___x_611_, 1, v___x_621_);
lean_ctor_set(v___x_611_, 0, v___x_620_);
v___x_623_ = v___x_611_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v___x_621_);
v___x_623_ = v_reuseFailAlloc_634_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v_m_625_; 
if (v_isShared_593_ == 0)
{
lean_ctor_set_tag(v___x_592_, 7);
lean_ctor_set(v___x_592_, 1, v_a_617_);
lean_ctor_set(v___x_592_, 0, v___x_623_);
v_m_625_ = v___x_592_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_a_617_);
v_m_625_ = v_reuseFailAlloc_633_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_626_; lean_object* v___x_627_; double v___x_628_; lean_object* v_data_629_; 
v___x_626_ = lean_box(v_result_618_);
v___x_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
v___x_628_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2);
lean_inc_ref(v_tag_578_);
lean_inc_ref(v___x_627_);
lean_inc(v_cls_576_);
v_data_629_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_629_, 0, v_cls_576_);
lean_ctor_set(v_data_629_, 1, v___x_627_);
lean_ctor_set(v_data_629_, 2, v_tag_578_);
lean_ctor_set_float(v_data_629_, sizeof(void*)*3, v___x_628_);
lean_ctor_set_float(v_data_629_, sizeof(void*)*3 + 8, v___x_628_);
lean_ctor_set_uint8(v_data_629_, sizeof(void*)*3 + 16, v_collapsed_577_);
if (v___x_614_ == 0)
{
lean_dec_ref(v___x_627_);
lean_dec(v_snd_609_);
lean_dec(v_fst_608_);
lean_dec_ref(v_tag_578_);
lean_dec(v_cls_576_);
v___y_595_ = v_m_625_;
v___y_596_ = v___y_616_;
v_data_597_ = v_data_629_;
goto v___jp_594_;
}
else
{
lean_object* v_data_630_; double v___x_631_; double v___x_632_; 
lean_dec_ref(v_data_629_);
v_data_630_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_630_, 0, v_cls_576_);
lean_ctor_set(v_data_630_, 1, v___x_627_);
lean_ctor_set(v_data_630_, 2, v_tag_578_);
v___x_631_ = lean_unbox_float(v_fst_608_);
lean_dec(v_fst_608_);
lean_ctor_set_float(v_data_630_, sizeof(void*)*3, v___x_631_);
v___x_632_ = lean_unbox_float(v_snd_609_);
lean_dec(v_snd_609_);
lean_ctor_set_float(v_data_630_, sizeof(void*)*3 + 8, v___x_632_);
lean_ctor_set_uint8(v_data_630_, sizeof(void*)*3 + 16, v_collapsed_577_);
v___y_595_ = v_m_625_;
v___y_596_ = v___y_616_;
v_data_597_ = v_data_630_;
goto v___jp_594_;
}
}
}
}
v___jp_635_:
{
lean_object* v_ref_636_; lean_object* v___x_637_; 
v_ref_636_ = lean_ctor_get(v___y_586_, 5);
lean_inc(v___y_587_);
lean_inc_ref(v___y_586_);
lean_inc(v___y_585_);
lean_inc_ref(v___y_584_);
lean_inc(v_fst_589_);
v___x_637_ = lean_apply_6(v_msg_582_, v_fst_589_, v___y_584_, v___y_585_, v___y_586_, v___y_587_, lean_box(0));
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
lean_inc(v_a_638_);
lean_dec_ref(v___x_637_);
v___y_616_ = v_ref_636_;
v_a_617_ = v_a_638_;
goto v___jp_615_;
}
else
{
lean_object* v___x_639_; 
lean_dec_ref(v___x_637_);
v___x_639_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__4);
v___y_616_ = v_ref_636_;
v_a_617_ = v___x_639_;
goto v___jp_615_;
}
}
v___jp_640_:
{
if (v_clsEnabled_580_ == 0)
{
if (v___y_641_ == 0)
{
lean_object* v___x_642_; lean_object* v_traceState_643_; lean_object* v_env_644_; lean_object* v_nextMacroScope_645_; lean_object* v_ngen_646_; lean_object* v_auxDeclNGen_647_; lean_object* v_cache_648_; lean_object* v_messages_649_; lean_object* v_infoState_650_; lean_object* v_snapshotTasks_651_; lean_object* v_newDecls_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_671_; 
lean_del_object(v___x_611_);
lean_dec(v_snd_609_);
lean_dec(v_fst_608_);
lean_del_object(v___x_592_);
lean_dec_ref(v_msg_582_);
lean_dec_ref(v_tag_578_);
lean_dec(v_cls_576_);
v___x_642_ = lean_st_ref_take(v___y_587_);
v_traceState_643_ = lean_ctor_get(v___x_642_, 4);
v_env_644_ = lean_ctor_get(v___x_642_, 0);
v_nextMacroScope_645_ = lean_ctor_get(v___x_642_, 1);
v_ngen_646_ = lean_ctor_get(v___x_642_, 2);
v_auxDeclNGen_647_ = lean_ctor_get(v___x_642_, 3);
v_cache_648_ = lean_ctor_get(v___x_642_, 5);
v_messages_649_ = lean_ctor_get(v___x_642_, 6);
v_infoState_650_ = lean_ctor_get(v___x_642_, 7);
v_snapshotTasks_651_ = lean_ctor_get(v___x_642_, 8);
v_newDecls_652_ = lean_ctor_get(v___x_642_, 9);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_671_ == 0)
{
v___x_654_ = v___x_642_;
v_isShared_655_ = v_isSharedCheck_671_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_newDecls_652_);
lean_inc(v_snapshotTasks_651_);
lean_inc(v_infoState_650_);
lean_inc(v_messages_649_);
lean_inc(v_cache_648_);
lean_inc(v_traceState_643_);
lean_inc(v_auxDeclNGen_647_);
lean_inc(v_ngen_646_);
lean_inc(v_nextMacroScope_645_);
lean_inc(v_env_644_);
lean_dec(v___x_642_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_671_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
uint64_t v_tid_656_; lean_object* v_traces_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_670_; 
v_tid_656_ = lean_ctor_get_uint64(v_traceState_643_, sizeof(void*)*1);
v_traces_657_ = lean_ctor_get(v_traceState_643_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v_traceState_643_);
if (v_isSharedCheck_670_ == 0)
{
v___x_659_ = v_traceState_643_;
v_isShared_660_ = v_isSharedCheck_670_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_traces_657_);
lean_dec(v_traceState_643_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_670_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_661_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_581_, v_traces_657_);
lean_dec_ref(v_traces_657_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v___x_661_);
v___x_663_ = v___x_659_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_661_);
lean_ctor_set_uint64(v_reuseFailAlloc_669_, sizeof(void*)*1, v_tid_656_);
v___x_663_ = v_reuseFailAlloc_669_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
lean_object* v___x_665_; 
if (v_isShared_655_ == 0)
{
lean_ctor_set(v___x_654_, 4, v___x_663_);
v___x_665_ = v___x_654_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_env_644_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_nextMacroScope_645_);
lean_ctor_set(v_reuseFailAlloc_668_, 2, v_ngen_646_);
lean_ctor_set(v_reuseFailAlloc_668_, 3, v_auxDeclNGen_647_);
lean_ctor_set(v_reuseFailAlloc_668_, 4, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_668_, 5, v_cache_648_);
lean_ctor_set(v_reuseFailAlloc_668_, 6, v_messages_649_);
lean_ctor_set(v_reuseFailAlloc_668_, 7, v_infoState_650_);
lean_ctor_set(v_reuseFailAlloc_668_, 8, v_snapshotTasks_651_);
lean_ctor_set(v_reuseFailAlloc_668_, 9, v_newDecls_652_);
v___x_665_ = v_reuseFailAlloc_668_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = lean_st_ref_set(v___y_587_, v___x_665_);
v___x_667_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4___redArg(v_fst_589_);
return v___x_667_;
}
}
}
}
}
else
{
goto v___jp_635_;
}
}
else
{
goto v___jp_635_;
}
}
v___jp_672_:
{
double v___x_674_; double v___x_675_; double v___x_676_; uint8_t v___x_677_; 
v___x_674_ = lean_unbox_float(v_snd_609_);
v___x_675_ = lean_unbox_float(v_fst_608_);
v___x_676_ = lean_float_sub(v___x_674_, v___x_675_);
v___x_677_ = lean_float_decLt(v___y_673_, v___x_676_);
v___y_641_ = v___x_677_;
goto v___jp_640_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___boxed(lean_object* v_cls_690_, lean_object* v_collapsed_691_, lean_object* v_tag_692_, lean_object* v_opts_693_, lean_object* v_clsEnabled_694_, lean_object* v_oldTraces_695_, lean_object* v_msg_696_, lean_object* v_resStartStop_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
uint8_t v_collapsed_boxed_703_; uint8_t v_clsEnabled_boxed_704_; lean_object* v_res_705_; 
v_collapsed_boxed_703_ = lean_unbox(v_collapsed_691_);
v_clsEnabled_boxed_704_ = lean_unbox(v_clsEnabled_694_);
v_res_705_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_cls_690_, v_collapsed_boxed_703_, v_tag_692_, v_opts_693_, v_clsEnabled_boxed_704_, v_oldTraces_695_, v_msg_696_, v_resStartStop_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_);
lean_dec(v___y_701_);
lean_dec_ref(v___y_700_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec_ref(v_opts_693_);
return v_res_705_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_710_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__2_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_));
v___x_711_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__2));
v___x_712_ = l_Lean_Name_append(v___x_711_, v___x_710_);
return v___x_712_;
}
}
static double _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4(void){
_start:
{
lean_object* v___x_713_; double v___x_714_; 
v___x_713_ = lean_unsigned_to_nat(1000000000u);
v___x_714_ = lean_float_of_nat(v___x_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(lean_object* v_a_715_, lean_object* v_b_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_){
_start:
{
lean_object* v___x_722_; lean_object* v_options_723_; uint8_t v_hasTrace_724_; 
v___x_722_ = l_Lean_Meta_NormCast_normCastExt;
v_options_723_ = lean_ctor_get(v_a_719_, 2);
v_hasTrace_724_ = lean_ctor_get_uint8(v_options_723_, sizeof(void*)*1);
if (v_hasTrace_724_ == 0)
{
lean_object* v_down_725_; lean_object* v___x_726_; 
v_down_725_ = lean_ctor_get(v___x_722_, 1);
v___x_726_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_down_725_, v_a_720_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_a_727_; lean_object* v___x_728_; 
v_a_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_a_727_);
lean_dec_ref(v___x_726_);
v___x_728_ = l_Lean_Elab_Tactic_NormCast_proveEqUsing(v_a_727_, v_a_715_, v_b_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
return v___x_728_;
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_dec_ref(v_b_716_);
lean_dec_ref(v_a_715_);
v_a_729_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_726_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_726_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
else
{
lean_object* v_down_737_; lean_object* v_inheritedTraceOptions_738_; lean_object* v___f_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; lean_object* v___y_745_; lean_object* v___y_746_; lean_object* v_a_747_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v_a_762_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v_a_767_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v_a_779_; 
v_down_737_ = lean_ctor_get(v___x_722_, 1);
v_inheritedTraceOptions_738_ = lean_ctor_get(v_a_719_, 13);
lean_inc_ref(v_b_716_);
lean_inc_ref(v_a_715_);
v___f_739_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___boxed), 8, 2);
lean_closure_set(v___f_739_, 0, v_a_715_);
lean_closure_set(v___f_739_, 1, v_b_716_);
v___x_740_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__2_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_));
v___x_741_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_742_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3);
v___x_743_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_738_, v_options_723_, v___x_742_);
if (v___x_743_ == 0)
{
lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_814_ = l_Lean_trace_profiler;
v___x_815_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_723_, v___x_814_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; 
lean_dec_ref(v___f_739_);
v___x_816_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_down_737_, v_a_720_);
if (lean_obj_tag(v___x_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_818_; 
v_a_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref(v___x_816_);
v___x_818_ = l_Lean_Elab_Tactic_NormCast_proveEqUsing(v_a_817_, v_a_715_, v_b_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
return v___x_818_;
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec_ref(v_b_716_);
lean_dec_ref(v_a_715_);
v_a_819_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_816_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_816_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
goto v___jp_781_;
}
}
else
{
goto v___jp_781_;
}
v___jp_744_:
{
lean_object* v___x_748_; double v___x_749_; double v___x_750_; double v___x_751_; double v___x_752_; double v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_748_ = lean_io_mono_nanos_now();
v___x_749_ = lean_float_of_nat(v___y_746_);
v___x_750_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4);
v___x_751_ = lean_float_div(v___x_749_, v___x_750_);
v___x_752_ = lean_float_of_nat(v___x_748_);
v___x_753_ = lean_float_div(v___x_752_, v___x_750_);
v___x_754_ = lean_box_float(v___x_751_);
v___x_755_ = lean_box_float(v___x_753_);
v___x_756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_754_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_757_, 0, v_a_747_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
v___x_758_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v___x_740_, v_hasTrace_724_, v___x_741_, v_options_723_, v___x_743_, v___y_745_, v___f_739_, v___x_757_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
return v___x_758_;
}
v___jp_759_:
{
lean_object* v___x_763_; 
v___x_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_763_, 0, v_a_762_);
v___y_745_ = v___y_760_;
v___y_746_ = v___y_761_;
v_a_747_ = v___x_763_;
goto v___jp_744_;
}
v___jp_764_:
{
lean_object* v___x_768_; double v___x_769_; double v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_768_ = lean_io_get_num_heartbeats();
v___x_769_ = lean_float_of_nat(v___y_766_);
v___x_770_ = lean_float_of_nat(v___x_768_);
v___x_771_ = lean_box_float(v___x_769_);
v___x_772_ = lean_box_float(v___x_770_);
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_771_);
lean_ctor_set(v___x_773_, 1, v___x_772_);
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v_a_767_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
v___x_775_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v___x_740_, v_hasTrace_724_, v___x_741_, v_options_723_, v___x_743_, v___y_765_, v___f_739_, v___x_774_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
return v___x_775_;
}
v___jp_776_:
{
lean_object* v___x_780_; 
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v_a_779_);
v___y_765_ = v___y_777_;
v___y_766_ = v___y_778_;
v_a_767_ = v___x_780_;
goto v___jp_764_;
}
v___jp_781_:
{
lean_object* v___x_782_; lean_object* v_a_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_782_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v_a_720_);
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_783_);
lean_dec_ref(v___x_782_);
v___x_784_ = l_Lean_trace_profiler_useHeartbeats;
v___x_785_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_723_, v___x_784_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = lean_io_mono_nanos_now();
v___x_787_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_down_737_, v_a_720_);
if (lean_obj_tag(v___x_787_) == 0)
{
lean_object* v_a_788_; lean_object* v___x_789_; 
v_a_788_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_788_);
lean_dec_ref(v___x_787_);
v___x_789_ = l_Lean_Elab_Tactic_NormCast_proveEqUsing(v_a_788_, v_a_715_, v_b_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_789_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_789_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set_tag(v___x_792_, 1);
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
v___y_745_ = v_a_783_;
v___y_746_ = v___x_786_;
v_a_747_ = v___x_795_;
goto v___jp_744_;
}
}
}
else
{
lean_object* v_a_798_; 
v_a_798_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_798_);
lean_dec_ref(v___x_789_);
v___y_760_ = v_a_783_;
v___y_761_ = v___x_786_;
v_a_762_ = v_a_798_;
goto v___jp_759_;
}
}
else
{
lean_object* v_a_799_; 
lean_dec_ref(v_b_716_);
lean_dec_ref(v_a_715_);
v_a_799_ = lean_ctor_get(v___x_787_, 0);
lean_inc(v_a_799_);
lean_dec_ref(v___x_787_);
v___y_760_ = v_a_783_;
v___y_761_ = v___x_786_;
v_a_762_ = v_a_799_;
goto v___jp_759_;
}
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_io_get_num_heartbeats();
v___x_801_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_down_737_, v_a_720_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_803_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_a_802_);
lean_dec_ref(v___x_801_);
v___x_803_ = l_Lean_Elab_Tactic_NormCast_proveEqUsing(v_a_802_, v_a_715_, v_b_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_803_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_803_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
lean_ctor_set_tag(v___x_806_, 1);
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
v___y_765_ = v_a_783_;
v___y_766_ = v___x_800_;
v_a_767_ = v___x_809_;
goto v___jp_764_;
}
}
}
else
{
lean_object* v_a_812_; 
v_a_812_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_812_);
lean_dec_ref(v___x_803_);
v___y_777_ = v_a_783_;
v___y_778_ = v___x_800_;
v_a_779_ = v_a_812_;
goto v___jp_776_;
}
}
else
{
lean_object* v_a_813_; 
lean_dec_ref(v_b_716_);
lean_dec_ref(v_a_715_);
v_a_813_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_a_813_);
lean_dec_ref(v___x_801_);
v___y_777_ = v_a_783_;
v___y_778_ = v___x_800_;
v_a_779_ = v_a_813_;
goto v___jp_776_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___boxed(lean_object* v_a_827_, lean_object* v_b_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_a_827_, v_b_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4(lean_object* v_00_u03b1_835_, lean_object* v_x_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4___redArg(v_x_836_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4___boxed(lean_object* v_00_u03b1_843_, lean_object* v_x_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4(v_00_u03b1_843_, v_x_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
lean_dec(v___y_848_);
lean_dec_ref(v___y_847_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(lean_object* v_msg_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_ref_857_; lean_object* v___x_858_; lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_867_; 
v_ref_857_ = lean_ctor_get(v___y_854_, 5);
v___x_858_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__5(v_msg_851_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
v_a_859_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_867_ == 0)
{
v___x_861_ = v___x_858_;
v_isShared_862_ = v_isSharedCheck_867_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_858_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_867_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; lean_object* v___x_865_; 
lean_inc(v_ref_857_);
v___x_863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_863_, 0, v_ref_857_);
lean_ctor_set(v___x_863_, 1, v_a_859_);
if (v_isShared_862_ == 0)
{
lean_ctor_set_tag(v___x_861_, 1);
lean_ctor_set(v___x_861_, 0, v___x_863_);
v___x_865_ = v___x_861_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg___boxed(lean_object* v_msg_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v_msg_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
return v_res_874_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_mkCoe___closed__0));
v___x_877_ = l_Lean_stringToMessageData(v___x_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_mkCoe(lean_object* v_e_878_, lean_object* v_ty_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_Meta_coerce_x3f(v_e_878_, v_ty_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_896_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_896_ == 0)
{
v___x_888_ = v___x_885_;
v_isShared_889_ = v_isSharedCheck_896_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_885_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_896_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
if (lean_obj_tag(v_a_886_) == 1)
{
lean_object* v_a_890_; lean_object* v___x_892_; 
v_a_890_ = lean_ctor_get(v_a_886_, 0);
lean_inc(v_a_890_);
lean_dec_ref(v_a_886_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v_a_890_);
v___x_892_ = v___x_888_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_890_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
else
{
lean_object* v___x_894_; lean_object* v___x_895_; 
lean_del_object(v___x_888_);
lean_dec(v_a_886_);
v___x_894_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_895_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_894_, v_a_880_, v_a_881_, v_a_882_, v_a_883_);
return v___x_895_;
}
}
}
else
{
lean_object* v_a_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_904_; 
v_a_897_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_904_ == 0)
{
v___x_899_ = v___x_885_;
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_a_897_);
lean_dec(v___x_885_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_904_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_902_; 
if (v_isShared_900_ == 0)
{
v___x_902_ = v___x_899_;
goto v_reusejp_901_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v_a_897_);
v___x_902_ = v_reuseFailAlloc_903_;
goto v_reusejp_901_;
}
v_reusejp_901_:
{
return v___x_902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_mkCoe___boxed(lean_object* v_e_905_, lean_object* v_ty_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_e_905_, v_ty_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
lean_dec(v_a_908_);
lean_dec_ref(v_a_907_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0(lean_object* v_00_u03b1_913_, lean_object* v_msg_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v_msg_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___boxed(lean_object* v_00_u03b1_921_, lean_object* v_msg_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0(v_00_u03b1_921_, v_msg_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(lean_object* v_e_929_, lean_object* v_a_930_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Lean_Expr_getAppFn(v_e_929_);
if (lean_obj_tag(v___x_935_) == 4)
{
lean_object* v_declName_936_; lean_object* v___x_937_; 
v_declName_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_declName_936_);
lean_dec_ref(v___x_935_);
v___x_937_ = l_Lean_Meta_getCoeFnInfo_x3f___redArg(v_declName_936_, v_a_930_);
lean_dec(v_declName_936_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_961_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_961_ == 0)
{
v___x_940_ = v___x_937_;
v_isShared_941_ = v_isSharedCheck_961_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_937_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_961_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
if (lean_obj_tag(v_a_938_) == 1)
{
lean_object* v_val_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_960_; 
v_val_942_ = lean_ctor_get(v_a_938_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v_a_938_);
if (v_isSharedCheck_960_ == 0)
{
v___x_944_ = v_a_938_;
v_isShared_945_ = v_isSharedCheck_960_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_val_942_);
lean_dec(v_a_938_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_960_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v_numArgs_946_; lean_object* v_coercee_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v_numArgs_946_ = lean_ctor_get(v_val_942_, 0);
lean_inc(v_numArgs_946_);
v_coercee_947_ = lean_ctor_get(v_val_942_, 1);
lean_inc(v_coercee_947_);
lean_dec(v_val_942_);
v___x_948_ = l_Lean_Expr_getAppNumArgs(v_e_929_);
v___x_949_ = lean_nat_dec_eq(v___x_948_, v_numArgs_946_);
lean_dec(v_numArgs_946_);
if (v___x_949_ == 0)
{
lean_dec(v___x_948_);
lean_dec(v_coercee_947_);
lean_del_object(v___x_944_);
lean_del_object(v___x_940_);
goto v___jp_932_;
}
else
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_955_; 
v___x_950_ = lean_nat_sub(v___x_948_, v_coercee_947_);
lean_dec(v_coercee_947_);
lean_dec(v___x_948_);
v___x_951_ = lean_unsigned_to_nat(1u);
v___x_952_ = lean_nat_sub(v___x_950_, v___x_951_);
lean_dec(v___x_950_);
v___x_953_ = l_Lean_Expr_getRevArg_x21(v_e_929_, v___x_952_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v___x_953_);
v___x_955_ = v___x_944_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_953_);
v___x_955_ = v_reuseFailAlloc_959_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
lean_object* v___x_957_; 
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_955_);
v___x_957_ = v___x_940_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
else
{
lean_del_object(v___x_940_);
lean_dec(v_a_938_);
goto v___jp_932_;
}
}
}
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
v_a_962_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_937_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_937_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
else
{
lean_dec_ref(v___x_935_);
goto v___jp_932_;
}
v___jp_932_:
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = lean_box(0);
v___x_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_934_, 0, v___x_933_);
return v___x_934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg___boxed(lean_object* v_e_970_, lean_object* v_a_971_, lean_object* v_a_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_e_970_, v_a_971_);
lean_dec(v_a_971_);
lean_dec_ref(v_e_970_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f(lean_object* v_e_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_e_974_, v_a_978_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___boxed(lean_object* v_e_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f(v_e_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_);
lean_dec(v_a_985_);
lean_dec_ref(v_a_984_);
lean_dec(v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec_ref(v_e_981_);
return v_res_987_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__6(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_997_ = lean_box(0);
v___x_998_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__5));
v___x_999_ = l_Lean_mkConst(v___x_998_, v___x_997_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__7(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = lean_unsigned_to_nat(0u);
v___x_1001_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__6, &l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__6_once, _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__6);
v___x_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_1001_);
lean_ctor_set(v___x_1002_, 1, v___x_1000_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__8(void){
_start:
{
lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_1003_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__7, &l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__7_once, _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__7);
v___x_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1004_, 0, v___x_1003_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(lean_object* v_e_1005_){
_start:
{
lean_object* v___x_1006_; uint8_t v___x_1007_; 
v___x_1006_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__2));
v___x_1007_ = l_Lean_Expr_isConstOf(v_e_1005_, v___x_1006_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; 
v___x_1008_ = l_Lean_Expr_consumeMData(v_e_1005_);
if (lean_obj_tag(v___x_1008_) == 5)
{
lean_object* v_fn_1009_; 
v_fn_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc_ref(v_fn_1009_);
lean_dec_ref(v___x_1008_);
if (lean_obj_tag(v_fn_1009_) == 5)
{
lean_object* v_fn_1010_; 
v_fn_1010_ = lean_ctor_get(v_fn_1009_, 0);
lean_inc_ref(v_fn_1010_);
if (lean_obj_tag(v_fn_1010_) == 5)
{
lean_object* v_fn_1011_; 
v_fn_1011_ = lean_ctor_get(v_fn_1010_, 0);
if (lean_obj_tag(v_fn_1011_) == 4)
{
lean_object* v_declName_1012_; 
v_declName_1012_ = lean_ctor_get(v_fn_1011_, 0);
lean_inc(v_declName_1012_);
if (lean_obj_tag(v_declName_1012_) == 1)
{
lean_object* v_pre_1013_; 
v_pre_1013_ = lean_ctor_get(v_declName_1012_, 0);
lean_inc(v_pre_1013_);
if (lean_obj_tag(v_pre_1013_) == 1)
{
lean_object* v_pre_1014_; 
v_pre_1014_ = lean_ctor_get(v_pre_1013_, 0);
if (lean_obj_tag(v_pre_1014_) == 0)
{
lean_object* v_arg_1015_; lean_object* v_arg_1016_; lean_object* v_str_1017_; lean_object* v_str_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v_arg_1015_ = lean_ctor_get(v_fn_1009_, 1);
lean_inc_ref(v_arg_1015_);
lean_dec_ref(v_fn_1009_);
v_arg_1016_ = lean_ctor_get(v_fn_1010_, 1);
lean_inc_ref(v_arg_1016_);
lean_dec_ref(v_fn_1010_);
v_str_1017_ = lean_ctor_get(v_declName_1012_, 1);
lean_inc_ref(v_str_1017_);
lean_dec_ref(v_declName_1012_);
v_str_1018_ = lean_ctor_get(v_pre_1013_, 1);
lean_inc_ref(v_str_1018_);
lean_dec_ref(v_pre_1013_);
v___x_1019_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__3));
v___x_1020_ = lean_string_dec_eq(v_str_1018_, v___x_1019_);
lean_dec_ref(v_str_1018_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; 
lean_dec_ref(v_str_1017_);
lean_dec_ref(v_arg_1016_);
lean_dec_ref(v_arg_1015_);
v___x_1021_ = lean_box(0);
return v___x_1021_;
}
else
{
lean_object* v___x_1022_; uint8_t v___x_1023_; 
v___x_1022_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__4));
v___x_1023_ = lean_string_dec_eq(v_str_1017_, v___x_1022_);
lean_dec_ref(v_str_1017_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; 
lean_dec_ref(v_arg_1016_);
lean_dec_ref(v_arg_1015_);
v___x_1024_ = lean_box(0);
return v___x_1024_;
}
else
{
if (lean_obj_tag(v_arg_1015_) == 9)
{
lean_object* v_a_1025_; 
v_a_1025_ = lean_ctor_get(v_arg_1015_, 0);
lean_inc_ref(v_a_1025_);
lean_dec_ref(v_arg_1015_);
if (lean_obj_tag(v_a_1025_) == 0)
{
lean_object* v_val_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1034_; 
v_val_1026_ = lean_ctor_get(v_a_1025_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_a_1025_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1028_ = v_a_1025_;
v_isShared_1029_ = v_isSharedCheck_1034_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_val_1026_);
lean_dec(v_a_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1034_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v_arg_1016_);
lean_ctor_set(v___x_1030_, 1, v_val_1026_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set_tag(v___x_1028_, 1);
lean_ctor_set(v___x_1028_, 0, v___x_1030_);
v___x_1032_ = v___x_1028_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
else
{
lean_object* v___x_1035_; 
lean_dec_ref(v_a_1025_);
lean_dec_ref(v_arg_1016_);
v___x_1035_ = lean_box(0);
return v___x_1035_;
}
}
else
{
lean_object* v___x_1036_; 
lean_dec_ref(v_arg_1016_);
lean_dec_ref(v_arg_1015_);
v___x_1036_ = lean_box(0);
return v___x_1036_;
}
}
}
}
else
{
lean_object* v___x_1037_; 
lean_dec_ref(v_pre_1013_);
lean_dec_ref(v_declName_1012_);
lean_dec_ref(v_fn_1010_);
lean_dec_ref(v_fn_1009_);
v___x_1037_ = lean_box(0);
return v___x_1037_;
}
}
else
{
lean_object* v___x_1038_; 
lean_dec_ref(v_declName_1012_);
lean_dec(v_pre_1013_);
lean_dec_ref(v_fn_1010_);
lean_dec_ref(v_fn_1009_);
v___x_1038_ = lean_box(0);
return v___x_1038_;
}
}
else
{
lean_object* v___x_1039_; 
lean_dec(v_declName_1012_);
lean_dec_ref(v_fn_1010_);
lean_dec_ref(v_fn_1009_);
v___x_1039_ = lean_box(0);
return v___x_1039_;
}
}
else
{
lean_object* v___x_1040_; 
lean_dec_ref(v_fn_1010_);
lean_dec_ref(v_fn_1009_);
v___x_1040_ = lean_box(0);
return v___x_1040_;
}
}
else
{
lean_object* v___x_1041_; 
lean_dec_ref(v_fn_1010_);
lean_dec_ref(v_fn_1009_);
v___x_1041_ = lean_box(0);
return v___x_1041_;
}
}
else
{
lean_object* v___x_1042_; 
lean_dec_ref(v_fn_1009_);
v___x_1042_ = lean_box(0);
return v___x_1042_;
}
}
else
{
lean_object* v___x_1043_; 
lean_dec_ref(v___x_1008_);
v___x_1043_ = lean_box(0);
return v___x_1043_;
}
}
else
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__8, &l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__8);
return v___x_1044_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___boxed(lean_object* v_e_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_e_1045_);
lean_dec_ref(v_e_1045_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(lean_object* v_x_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
v___x_1053_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1054_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1053_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1054_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1054_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0___boxed(lean_object* v_x_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v_x_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v_x_1063_);
return v_res_1069_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___closed__0));
v___x_1072_ = l_Lean_stringToMessageData(v___x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4(lean_object* v___x_1073_, lean_object* v_expr_1074_, lean_object* v_x_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
if (lean_obj_tag(v_x_1075_) == 0)
{
lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1087_; 
v_isSharedCheck_1087_ = !lean_is_exclusive(v_x_1075_);
if (v_isSharedCheck_1087_ == 0)
{
lean_object* v_unused_1088_; 
v_unused_1088_ = lean_ctor_get(v_x_1075_, 0);
lean_dec(v_unused_1088_);
v___x_1082_ = v_x_1075_;
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
else
{
lean_dec(v_x_1075_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1087_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v___x_1085_; 
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 0, v___x_1073_);
v___x_1085_ = v___x_1082_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1073_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1105_; 
v_a_1089_ = lean_ctor_get(v_x_1075_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_x_1075_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1091_ = v_x_1075_;
v_isShared_1092_ = v_isSharedCheck_1105_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v_x_1075_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1105_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v_expr_1093_; uint8_t v___x_1094_; 
v_expr_1093_ = lean_ctor_get(v_a_1089_, 0);
lean_inc_ref(v_expr_1093_);
lean_dec(v_a_1089_);
v___x_1094_ = lean_expr_eqv(v_expr_1093_, v_expr_1074_);
if (v___x_1094_ == 0)
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1095_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___closed__1, &l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___closed__1);
v___x_1096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1073_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = l_Lean_MessageData_ofExpr(v_expr_1093_);
v___x_1098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set_tag(v___x_1091_, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1098_);
v___x_1100_ = v___x_1091_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
else
{
lean_object* v___x_1103_; 
lean_dec_ref(v_expr_1093_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set_tag(v___x_1091_, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1073_);
v___x_1103_ = v___x_1091_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1073_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___boxed(lean_object* v___x_1106_, lean_object* v_expr_1107_, lean_object* v_x_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4(v___x_1106_, v_expr_1107_, v_x_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec_ref(v_expr_1107_);
return v_res_1114_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0_spec__0(lean_object* v_e_1115_){
_start:
{
if (lean_obj_tag(v_e_1115_) == 0)
{
uint8_t v___x_1116_; 
v___x_1116_ = 2;
return v___x_1116_;
}
else
{
uint8_t v___x_1117_; 
v___x_1117_ = 0;
return v___x_1117_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0_spec__0___boxed(lean_object* v_e_1118_){
_start:
{
uint8_t v_res_1119_; lean_object* v_r_1120_; 
v_res_1119_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0_spec__0(v_e_1118_);
lean_dec_ref(v_e_1118_);
v_r_1120_ = lean_box(v_res_1119_);
return v_r_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(lean_object* v_cls_1121_, uint8_t v_collapsed_1122_, lean_object* v_tag_1123_, lean_object* v_opts_1124_, uint8_t v_clsEnabled_1125_, lean_object* v_oldTraces_1126_, lean_object* v_msg_1127_, lean_object* v_resStartStop_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_){
_start:
{
lean_object* v_fst_1134_; lean_object* v_snd_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1234_; 
v_fst_1134_ = lean_ctor_get(v_resStartStop_1128_, 0);
v_snd_1135_ = lean_ctor_get(v_resStartStop_1128_, 1);
v_isSharedCheck_1234_ = !lean_is_exclusive(v_resStartStop_1128_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1137_ = v_resStartStop_1128_;
v_isShared_1138_ = v_isSharedCheck_1234_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_snd_1135_);
lean_inc(v_fst_1134_);
lean_dec(v_resStartStop_1128_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1234_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___y_1140_; lean_object* v___y_1141_; lean_object* v_data_1142_; lean_object* v_fst_1153_; lean_object* v_snd_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1233_; 
v_fst_1153_ = lean_ctor_get(v_snd_1135_, 0);
v_snd_1154_ = lean_ctor_get(v_snd_1135_, 1);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_snd_1135_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1156_ = v_snd_1135_;
v_isShared_1157_ = v_isSharedCheck_1233_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_snd_1154_);
lean_inc(v_fst_1153_);
lean_dec(v_snd_1135_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1233_;
goto v_resetjp_1155_;
}
v___jp_1139_:
{
lean_object* v___x_1143_; 
lean_inc(v___y_1141_);
v___x_1143_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3(v_oldTraces_1126_, v_data_1142_, v___y_1141_, v___y_1140_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v___x_1144_; 
lean_dec_ref(v___x_1143_);
v___x_1144_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4___redArg(v_fst_1134_);
return v___x_1144_;
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_dec(v_fst_1134_);
v_a_1145_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1143_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1143_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
v_resetjp_1155_:
{
lean_object* v___x_1158_; uint8_t v___x_1159_; lean_object* v___y_1161_; lean_object* v_a_1162_; uint8_t v___y_1186_; double v___y_1218_; 
v___x_1158_ = l_Lean_trace_profiler;
v___x_1159_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_opts_1124_, v___x_1158_);
if (v___x_1159_ == 0)
{
v___y_1186_ = v___x_1159_;
goto v___jp_1185_;
}
else
{
lean_object* v___x_1223_; uint8_t v___x_1224_; 
v___x_1223_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1224_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_opts_1124_, v___x_1223_);
if (v___x_1224_ == 0)
{
lean_object* v___x_1225_; lean_object* v___x_1226_; double v___x_1227_; double v___x_1228_; double v___x_1229_; 
v___x_1225_ = l_Lean_trace_profiler_threshold;
v___x_1226_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__5(v_opts_1124_, v___x_1225_);
v___x_1227_ = lean_float_of_nat(v___x_1226_);
v___x_1228_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__5);
v___x_1229_ = lean_float_div(v___x_1227_, v___x_1228_);
v___y_1218_ = v___x_1229_;
goto v___jp_1217_;
}
else
{
lean_object* v___x_1230_; lean_object* v___x_1231_; double v___x_1232_; 
v___x_1230_ = l_Lean_trace_profiler_threshold;
v___x_1231_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__5(v_opts_1124_, v___x_1230_);
v___x_1232_ = lean_float_of_nat(v___x_1231_);
v___y_1218_ = v___x_1232_;
goto v___jp_1217_;
}
}
v___jp_1160_:
{
uint8_t v_result_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1168_; 
v_result_1163_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0_spec__0(v_fst_1134_);
v___x_1164_ = l_Lean_TraceResult_toEmoji(v_result_1163_);
v___x_1165_ = l_Lean_stringToMessageData(v___x_1164_);
v___x_1166_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1);
if (v_isShared_1157_ == 0)
{
lean_ctor_set_tag(v___x_1156_, 7);
lean_ctor_set(v___x_1156_, 1, v___x_1166_);
lean_ctor_set(v___x_1156_, 0, v___x_1165_);
v___x_1168_ = v___x_1156_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v_m_1170_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set_tag(v___x_1137_, 7);
lean_ctor_set(v___x_1137_, 1, v_a_1162_);
lean_ctor_set(v___x_1137_, 0, v___x_1168_);
v_m_1170_ = v___x_1137_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1178_, 1, v_a_1162_);
v_m_1170_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; double v___x_1173_; lean_object* v_data_1174_; 
v___x_1171_ = lean_box(v_result_1163_);
v___x_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
v___x_1173_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2);
lean_inc_ref(v_tag_1123_);
lean_inc_ref(v___x_1172_);
lean_inc(v_cls_1121_);
v_data_1174_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1174_, 0, v_cls_1121_);
lean_ctor_set(v_data_1174_, 1, v___x_1172_);
lean_ctor_set(v_data_1174_, 2, v_tag_1123_);
lean_ctor_set_float(v_data_1174_, sizeof(void*)*3, v___x_1173_);
lean_ctor_set_float(v_data_1174_, sizeof(void*)*3 + 8, v___x_1173_);
lean_ctor_set_uint8(v_data_1174_, sizeof(void*)*3 + 16, v_collapsed_1122_);
if (v___x_1159_ == 0)
{
lean_dec_ref(v___x_1172_);
lean_dec(v_snd_1154_);
lean_dec(v_fst_1153_);
lean_dec_ref(v_tag_1123_);
lean_dec(v_cls_1121_);
v___y_1140_ = v_m_1170_;
v___y_1141_ = v___y_1161_;
v_data_1142_ = v_data_1174_;
goto v___jp_1139_;
}
else
{
lean_object* v_data_1175_; double v___x_1176_; double v___x_1177_; 
lean_dec_ref(v_data_1174_);
v_data_1175_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1175_, 0, v_cls_1121_);
lean_ctor_set(v_data_1175_, 1, v___x_1172_);
lean_ctor_set(v_data_1175_, 2, v_tag_1123_);
v___x_1176_ = lean_unbox_float(v_fst_1153_);
lean_dec(v_fst_1153_);
lean_ctor_set_float(v_data_1175_, sizeof(void*)*3, v___x_1176_);
v___x_1177_ = lean_unbox_float(v_snd_1154_);
lean_dec(v_snd_1154_);
lean_ctor_set_float(v_data_1175_, sizeof(void*)*3 + 8, v___x_1177_);
lean_ctor_set_uint8(v_data_1175_, sizeof(void*)*3 + 16, v_collapsed_1122_);
v___y_1140_ = v_m_1170_;
v___y_1141_ = v___y_1161_;
v_data_1142_ = v_data_1175_;
goto v___jp_1139_;
}
}
}
}
v___jp_1180_:
{
lean_object* v_ref_1181_; lean_object* v___x_1182_; 
v_ref_1181_ = lean_ctor_get(v___y_1131_, 5);
lean_inc(v___y_1132_);
lean_inc_ref(v___y_1131_);
lean_inc(v___y_1130_);
lean_inc_ref(v___y_1129_);
lean_inc(v_fst_1134_);
v___x_1182_ = lean_apply_6(v_msg_1127_, v_fst_1134_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, lean_box(0));
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1183_);
lean_dec_ref(v___x_1182_);
v___y_1161_ = v_ref_1181_;
v_a_1162_ = v_a_1183_;
goto v___jp_1160_;
}
else
{
lean_object* v___x_1184_; 
lean_dec_ref(v___x_1182_);
v___x_1184_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__4);
v___y_1161_ = v_ref_1181_;
v_a_1162_ = v___x_1184_;
goto v___jp_1160_;
}
}
v___jp_1185_:
{
if (v_clsEnabled_1125_ == 0)
{
if (v___y_1186_ == 0)
{
lean_object* v___x_1187_; lean_object* v_traceState_1188_; lean_object* v_env_1189_; lean_object* v_nextMacroScope_1190_; lean_object* v_ngen_1191_; lean_object* v_auxDeclNGen_1192_; lean_object* v_cache_1193_; lean_object* v_messages_1194_; lean_object* v_infoState_1195_; lean_object* v_snapshotTasks_1196_; lean_object* v_newDecls_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1216_; 
lean_del_object(v___x_1156_);
lean_dec(v_snd_1154_);
lean_dec(v_fst_1153_);
lean_del_object(v___x_1137_);
lean_dec_ref(v_msg_1127_);
lean_dec_ref(v_tag_1123_);
lean_dec(v_cls_1121_);
v___x_1187_ = lean_st_ref_take(v___y_1132_);
v_traceState_1188_ = lean_ctor_get(v___x_1187_, 4);
v_env_1189_ = lean_ctor_get(v___x_1187_, 0);
v_nextMacroScope_1190_ = lean_ctor_get(v___x_1187_, 1);
v_ngen_1191_ = lean_ctor_get(v___x_1187_, 2);
v_auxDeclNGen_1192_ = lean_ctor_get(v___x_1187_, 3);
v_cache_1193_ = lean_ctor_get(v___x_1187_, 5);
v_messages_1194_ = lean_ctor_get(v___x_1187_, 6);
v_infoState_1195_ = lean_ctor_get(v___x_1187_, 7);
v_snapshotTasks_1196_ = lean_ctor_get(v___x_1187_, 8);
v_newDecls_1197_ = lean_ctor_get(v___x_1187_, 9);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1199_ = v___x_1187_;
v_isShared_1200_ = v_isSharedCheck_1216_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_newDecls_1197_);
lean_inc(v_snapshotTasks_1196_);
lean_inc(v_infoState_1195_);
lean_inc(v_messages_1194_);
lean_inc(v_cache_1193_);
lean_inc(v_traceState_1188_);
lean_inc(v_auxDeclNGen_1192_);
lean_inc(v_ngen_1191_);
lean_inc(v_nextMacroScope_1190_);
lean_inc(v_env_1189_);
lean_dec(v___x_1187_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1216_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
uint64_t v_tid_1201_; lean_object* v_traces_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1215_; 
v_tid_1201_ = lean_ctor_get_uint64(v_traceState_1188_, sizeof(void*)*1);
v_traces_1202_ = lean_ctor_get(v_traceState_1188_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_traceState_1188_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1204_ = v_traceState_1188_;
v_isShared_1205_ = v_isSharedCheck_1215_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_traces_1202_);
lean_dec(v_traceState_1188_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1215_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1206_; lean_object* v___x_1208_; 
v___x_1206_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1126_, v_traces_1202_);
lean_dec_ref(v_traces_1202_);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v___x_1206_);
v___x_1208_ = v___x_1204_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1206_);
lean_ctor_set_uint64(v_reuseFailAlloc_1214_, sizeof(void*)*1, v_tid_1201_);
v___x_1208_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1210_; 
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 4, v___x_1208_);
v___x_1210_ = v___x_1199_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_env_1189_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_nextMacroScope_1190_);
lean_ctor_set(v_reuseFailAlloc_1213_, 2, v_ngen_1191_);
lean_ctor_set(v_reuseFailAlloc_1213_, 3, v_auxDeclNGen_1192_);
lean_ctor_set(v_reuseFailAlloc_1213_, 4, v___x_1208_);
lean_ctor_set(v_reuseFailAlloc_1213_, 5, v_cache_1193_);
lean_ctor_set(v_reuseFailAlloc_1213_, 6, v_messages_1194_);
lean_ctor_set(v_reuseFailAlloc_1213_, 7, v_infoState_1195_);
lean_ctor_set(v_reuseFailAlloc_1213_, 8, v_snapshotTasks_1196_);
lean_ctor_set(v_reuseFailAlloc_1213_, 9, v_newDecls_1197_);
v___x_1210_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = lean_st_ref_set(v___y_1132_, v___x_1210_);
v___x_1212_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4___redArg(v_fst_1134_);
return v___x_1212_;
}
}
}
}
}
else
{
goto v___jp_1180_;
}
}
else
{
goto v___jp_1180_;
}
}
v___jp_1217_:
{
double v___x_1219_; double v___x_1220_; double v___x_1221_; uint8_t v___x_1222_; 
v___x_1219_ = lean_unbox_float(v_snd_1154_);
v___x_1220_ = lean_unbox_float(v_fst_1153_);
v___x_1221_ = lean_float_sub(v___x_1219_, v___x_1220_);
v___x_1222_ = lean_float_decLt(v___y_1218_, v___x_1221_);
v___y_1186_ = v___x_1222_;
goto v___jp_1185_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0___boxed(lean_object* v_cls_1235_, lean_object* v_collapsed_1236_, lean_object* v_tag_1237_, lean_object* v_opts_1238_, lean_object* v_clsEnabled_1239_, lean_object* v_oldTraces_1240_, lean_object* v_msg_1241_, lean_object* v_resStartStop_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
uint8_t v_collapsed_boxed_1248_; uint8_t v_clsEnabled_boxed_1249_; lean_object* v_res_1250_; 
v_collapsed_boxed_1248_ = lean_unbox(v_collapsed_1236_);
v_clsEnabled_boxed_1249_ = lean_unbox(v_clsEnabled_1239_);
v_res_1250_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v_cls_1235_, v_collapsed_boxed_1248_, v_tag_1237_, v_opts_1238_, v_clsEnabled_boxed_1249_, v_oldTraces_1240_, v_msg_1241_, v_resStartStop_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec_ref(v_opts_1238_);
return v_res_1250_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___closed__1(void){
_start:
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1252_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_splittingProcedure___closed__0));
v___x_1253_ = l_Lean_stringToMessageData(v___x_1252_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure(lean_object* v_expr_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v_a_1266_; lean_object* v_a_1276_; lean_object* v___y_1286_; uint8_t v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; uint8_t v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1292_; lean_object* v___y_1293_; lean_object* v_a_1294_; uint8_t v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; uint8_t v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v_a_1312_; lean_object* v___y_1315_; uint8_t v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; uint8_t v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; lean_object* v_a_1323_; uint8_t v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; uint8_t v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v_a_1334_; lean_object* v___y_1337_; uint8_t v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; uint8_t v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1344_; lean_object* v___y_1345_; uint8_t v___y_1346_; uint8_t v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; uint8_t v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v_a_1358_; lean_object* v___y_1362_; uint8_t v___y_1363_; lean_object* v___y_1364_; uint8_t v___y_1365_; lean_object* v___y_1366_; lean_object* v___y_1367_; lean_object* v___y_1368_; lean_object* v___y_1369_; lean_object* v_a_1370_; uint8_t v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; uint8_t v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v_a_1391_; lean_object* v___y_1394_; uint8_t v___y_1395_; lean_object* v___y_1396_; uint8_t v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v_a_1402_; uint8_t v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; uint8_t v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v_a_1413_; lean_object* v___y_1416_; lean_object* v___y_1417_; uint8_t v___y_1418_; lean_object* v___y_1419_; uint8_t v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; uint8_t v___y_1425_; uint8_t v___y_1429_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; uint8_t v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v_a_1437_; uint8_t v___y_1441_; lean_object* v___y_1442_; uint8_t v___y_1443_; uint8_t v___y_1449_; lean_object* v_a_1450_; uint8_t v___y_1454_; lean_object* v___y_1455_; uint8_t v___y_1456_; uint8_t v___y_1462_; lean_object* v_a_1463_; 
if (lean_obj_tag(v_expr_1254_) == 5)
{
lean_object* v_fn_1466_; 
v_fn_1466_ = lean_ctor_get(v_expr_1254_, 0);
if (lean_obj_tag(v_fn_1466_) == 5)
{
lean_object* v_arg_1467_; lean_object* v_fn_1468_; lean_object* v_arg_1469_; lean_object* v___x_1470_; 
v_arg_1467_ = lean_ctor_get(v_expr_1254_, 1);
v_fn_1468_ = lean_ctor_get(v_fn_1466_, 0);
v_arg_1469_ = lean_ctor_get(v_fn_1466_, 1);
lean_inc(v_a_1258_);
lean_inc_ref(v_a_1257_);
lean_inc(v_a_1256_);
lean_inc_ref(v_a_1255_);
lean_inc_ref(v_fn_1468_);
v___x_1470_ = lean_infer_type(v_fn_1468_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_2320_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_1473_ = v___x_1470_;
v_isShared_1474_ = v_isSharedCheck_2320_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_a_1471_);
lean_dec(v___x_1470_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_2320_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
if (lean_obj_tag(v_a_1471_) == 7)
{
lean_object* v_body_1482_; 
v_body_1482_ = lean_ctor_get(v_a_1471_, 2);
lean_inc_ref(v_body_1482_);
if (lean_obj_tag(v_body_1482_) == 7)
{
lean_object* v_binderType_1483_; lean_object* v_binderType_1484_; lean_object* v_body_1485_; uint8_t v___y_1487_; lean_object* v___y_1488_; uint8_t v___y_1489_; uint8_t v___y_1528_; lean_object* v_a_1529_; uint8_t v___y_1533_; lean_object* v___y_1534_; uint8_t v___y_1535_; uint8_t v___y_1572_; lean_object* v_a_1573_; uint8_t v___y_1577_; lean_object* v___y_1578_; uint8_t v___y_1581_; lean_object* v___y_1582_; lean_object* v___y_1583_; lean_object* v___y_1584_; uint8_t v___y_1585_; uint8_t v___y_1603_; lean_object* v___y_1604_; lean_object* v___y_1605_; lean_object* v_a_1606_; uint8_t v___y_1610_; lean_object* v___y_1611_; lean_object* v___y_1612_; lean_object* v___y_1613_; uint8_t v___y_1616_; lean_object* v___y_1617_; uint8_t v___y_1618_; uint8_t v___y_1657_; lean_object* v_a_1658_; uint8_t v___y_1662_; lean_object* v___y_1663_; uint8_t v___y_1664_; uint8_t v___y_1701_; lean_object* v_a_1702_; uint8_t v___y_1706_; lean_object* v___y_1707_; uint8_t v___y_1710_; lean_object* v___y_1711_; lean_object* v___y_1712_; lean_object* v___y_1713_; uint8_t v___y_1714_; uint8_t v___y_1732_; lean_object* v___y_1733_; lean_object* v___y_1734_; lean_object* v_a_1735_; uint8_t v___y_1739_; lean_object* v___y_1740_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1745_; uint8_t v___y_1746_; lean_object* v___y_1747_; lean_object* v___y_1748_; uint8_t v___y_1749_; lean_object* v___y_1750_; lean_object* v___y_1751_; lean_object* v___y_1752_; lean_object* v___y_1753_; uint8_t v___y_1754_; uint8_t v___y_1793_; lean_object* v___y_1794_; lean_object* v___y_1795_; lean_object* v___y_1796_; uint8_t v___y_1797_; lean_object* v___y_1798_; lean_object* v___y_1799_; lean_object* v___y_1800_; lean_object* v_a_1801_; lean_object* v___y_1805_; uint8_t v___y_1806_; lean_object* v___y_1807_; uint8_t v___y_1808_; lean_object* v___y_1809_; lean_object* v___y_1810_; lean_object* v___y_1811_; lean_object* v___y_1812_; lean_object* v___y_1813_; uint8_t v___y_1814_; uint8_t v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___y_1854_; uint8_t v___y_1855_; lean_object* v___y_1856_; lean_object* v___y_1857_; lean_object* v___y_1858_; lean_object* v_a_1859_; lean_object* v___y_1863_; uint8_t v___y_1864_; lean_object* v___y_1865_; uint8_t v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1868_; lean_object* v___y_1869_; lean_object* v___y_1870_; lean_object* v___y_1871_; lean_object* v___y_1875_; uint8_t v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; lean_object* v___y_1879_; uint8_t v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; uint8_t v___y_1886_; uint8_t v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; uint8_t v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v_a_1914_; lean_object* v___y_1918_; uint8_t v___y_1919_; lean_object* v___y_1920_; uint8_t v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1932_; uint8_t v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; uint8_t v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; uint8_t v___y_1941_; uint8_t v___y_1980_; lean_object* v___y_1981_; lean_object* v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; uint8_t v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v_a_1988_; lean_object* v___y_1992_; uint8_t v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; uint8_t v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; uint8_t v___y_2001_; uint8_t v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2042_; uint8_t v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; lean_object* v_a_2046_; lean_object* v___y_2050_; uint8_t v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2053_; uint8_t v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___y_2062_; uint8_t v___y_2063_; lean_object* v___y_2064_; lean_object* v___y_2065_; lean_object* v___y_2066_; uint8_t v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; lean_object* v___y_2071_; lean_object* v___y_2072_; uint8_t v___y_2073_; uint8_t v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2094_; uint8_t v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v_a_2101_; lean_object* v___y_2105_; uint8_t v___y_2106_; lean_object* v___y_2107_; lean_object* v___y_2108_; uint8_t v___y_2109_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v___y_2114_; lean_object* v___y_2115_; uint8_t v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; uint8_t v___y_2122_; lean_object* v___y_2123_; lean_object* v___y_2124_; uint8_t v___y_2206_; uint8_t v___x_2318_; 
lean_del_object(v___x_1473_);
v_binderType_1483_ = lean_ctor_get(v_a_1471_, 1);
lean_inc_ref(v_binderType_1483_);
lean_dec_ref(v_a_1471_);
v_binderType_1484_ = lean_ctor_get(v_body_1482_, 1);
lean_inc_ref(v_binderType_1484_);
v_body_1485_ = lean_ctor_get(v_body_1482_, 2);
lean_inc_ref(v_body_1485_);
lean_dec_ref(v_body_1482_);
v___x_2318_ = l_Lean_Expr_hasLooseBVars(v_binderType_1484_);
if (v___x_2318_ == 0)
{
uint8_t v___x_2319_; 
v___x_2319_ = l_Lean_Expr_hasLooseBVars(v_body_1485_);
lean_dec_ref(v_body_1485_);
v___y_2206_ = v___x_2319_;
goto v___jp_2205_;
}
else
{
lean_dec_ref(v_body_1485_);
v___y_2206_ = v___x_2318_;
goto v___jp_2205_;
}
v___jp_1486_:
{
if (v___y_1489_ == 0)
{
lean_object* v___x_1490_; 
lean_dec_ref(v___y_1488_);
v___x_1490_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1469_);
if (lean_obj_tag(v___x_1490_) == 1)
{
lean_object* v_val_1491_; lean_object* v_snd_1492_; lean_object* v___x_1493_; 
v_val_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_val_1491_);
lean_dec_ref(v___x_1490_);
v_snd_1492_ = lean_ctor_get(v_val_1491_, 1);
lean_inc(v_snd_1492_);
lean_dec(v_val_1491_);
v___x_1493_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1467_, v_a_1258_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_a_1494_);
lean_dec_ref(v___x_1493_);
if (lean_obj_tag(v_a_1494_) == 1)
{
lean_object* v_val_1495_; lean_object* v___x_1496_; 
v_val_1495_ = lean_ctor_get(v_a_1494_, 0);
lean_inc(v_val_1495_);
lean_dec_ref(v_a_1494_);
lean_inc(v_a_1258_);
lean_inc_ref(v_a_1257_);
lean_inc(v_a_1256_);
lean_inc_ref(v_a_1255_);
v___x_1496_ = lean_infer_type(v_val_1495_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1498_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1497_);
lean_dec_ref(v___x_1496_);
v___x_1498_ = l_Lean_Meta_mkNumeral(v_a_1497_, v_snd_1492_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; lean_object* v___x_1500_; 
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_a_1499_);
lean_dec_ref(v___x_1498_);
v___x_1500_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1499_, v_binderType_1483_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_object* v_a_1501_; lean_object* v___x_1502_; 
v_a_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1501_);
lean_dec_ref(v___x_1500_);
lean_inc_ref(v_arg_1469_);
v___x_1502_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1469_, v_a_1501_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_a_1503_; 
v_a_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1503_);
lean_dec_ref(v___x_1502_);
if (lean_obj_tag(v_a_1503_) == 1)
{
lean_object* v_val_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v_val_1504_ = lean_ctor_get(v_a_1503_, 0);
lean_inc(v_val_1504_);
lean_dec_ref(v_a_1503_);
v___x_1505_ = lean_box(0);
lean_inc_ref(v_fn_1468_);
v___x_1506_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1506_, 0, v_fn_1468_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
lean_ctor_set_uint8(v___x_1506_, sizeof(void*)*2, v___y_1487_);
v___x_1507_ = l_Lean_Meta_Simp_mkCongr(v___x_1506_, v_val_1504_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; lean_object* v___x_1509_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1508_);
lean_dec_ref(v___x_1507_);
lean_inc_ref(v_arg_1467_);
v___x_1509_ = l_Lean_Meta_Simp_mkCongrFun(v_a_1508_, v_arg_1467_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_dec_ref(v_expr_1254_);
return v___x_1509_;
}
else
{
lean_object* v_a_1510_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
lean_dec_ref(v___x_1509_);
v___y_1449_ = v___y_1487_;
v_a_1450_ = v_a_1510_;
goto v___jp_1448_;
}
}
else
{
lean_object* v_a_1511_; 
v_a_1511_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_a_1511_);
lean_dec_ref(v___x_1507_);
v___y_1449_ = v___y_1487_;
v_a_1450_ = v_a_1511_;
goto v___jp_1448_;
}
}
else
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v_a_1514_; 
lean_dec(v_a_1503_);
v___x_1512_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1513_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1512_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_a_1514_);
lean_dec_ref(v___x_1513_);
v___y_1449_ = v___y_1487_;
v_a_1450_ = v_a_1514_;
goto v___jp_1448_;
}
}
else
{
lean_object* v_a_1515_; 
v_a_1515_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_a_1515_);
lean_dec_ref(v___x_1502_);
v___y_1449_ = v___y_1487_;
v_a_1450_ = v_a_1515_;
goto v___jp_1448_;
}
}
else
{
lean_object* v_a_1516_; 
v_a_1516_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_a_1516_);
lean_dec_ref(v___x_1500_);
v___y_1449_ = v___y_1487_;
v_a_1450_ = v_a_1516_;
goto v___jp_1448_;
}
}
else
{
lean_object* v_a_1517_; 
lean_dec_ref(v_binderType_1483_);
v_a_1517_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_a_1517_);
lean_dec_ref(v___x_1498_);
v___y_1449_ = v___y_1487_;
v_a_1450_ = v_a_1517_;
goto v___jp_1448_;
}
}
else
{
lean_object* v_a_1518_; 
lean_dec(v_snd_1492_);
lean_dec_ref(v_binderType_1483_);
v_a_1518_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1518_);
lean_dec_ref(v___x_1496_);
v___y_1449_ = v___y_1487_;
v_a_1450_ = v_a_1518_;
goto v___jp_1448_;
}
}
else
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v_a_1521_; 
lean_dec(v_a_1494_);
lean_dec(v_snd_1492_);
lean_dec_ref(v_binderType_1483_);
v___x_1519_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1520_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1519_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_a_1521_);
lean_dec_ref(v___x_1520_);
v___y_1449_ = v___y_1487_;
v_a_1450_ = v_a_1521_;
goto v___jp_1448_;
}
}
else
{
lean_object* v_a_1522_; 
lean_dec(v_snd_1492_);
lean_dec_ref(v_binderType_1483_);
v_a_1522_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_a_1522_);
lean_dec_ref(v___x_1493_);
v___y_1449_ = v___y_1487_;
v_a_1450_ = v_a_1522_;
goto v___jp_1448_;
}
}
else
{
lean_object* v___x_1523_; 
lean_dec_ref(v_binderType_1483_);
v___x_1523_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1490_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
lean_dec(v___x_1490_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; 
lean_dec_ref(v_expr_1254_);
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1524_);
lean_dec_ref(v___x_1523_);
v_a_1266_ = v_a_1524_;
goto v___jp_1265_;
}
else
{
lean_object* v_a_1525_; 
v_a_1525_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1525_);
lean_dec_ref(v___x_1523_);
v___y_1449_ = v___y_1487_;
v_a_1450_ = v_a_1525_;
goto v___jp_1448_;
}
}
}
else
{
lean_object* v___x_1526_; 
lean_dec_ref(v_binderType_1483_);
lean_dec_ref(v_expr_1254_);
v___x_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1526_, 0, v___y_1488_);
return v___x_1526_;
}
}
v___jp_1527_:
{
uint8_t v___x_1530_; 
v___x_1530_ = l_Lean_Exception_isInterrupt(v_a_1529_);
if (v___x_1530_ == 0)
{
uint8_t v___x_1531_; 
lean_inc_ref(v_a_1529_);
v___x_1531_ = l_Lean_Exception_isRuntime(v_a_1529_);
v___y_1487_ = v___y_1528_;
v___y_1488_ = v_a_1529_;
v___y_1489_ = v___x_1531_;
goto v___jp_1486_;
}
else
{
v___y_1487_ = v___y_1528_;
v___y_1488_ = v_a_1529_;
v___y_1489_ = v___x_1530_;
goto v___jp_1486_;
}
}
v___jp_1532_:
{
if (v___y_1535_ == 0)
{
lean_object* v___x_1536_; 
lean_dec_ref(v___y_1534_);
v___x_1536_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1467_);
if (lean_obj_tag(v___x_1536_) == 1)
{
lean_object* v_val_1537_; lean_object* v_snd_1538_; lean_object* v___x_1539_; 
v_val_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_val_1537_);
lean_dec_ref(v___x_1536_);
v_snd_1538_ = lean_ctor_get(v_val_1537_, 1);
lean_inc(v_snd_1538_);
lean_dec(v_val_1537_);
v___x_1539_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1469_, v_a_1258_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1540_);
lean_dec_ref(v___x_1539_);
if (lean_obj_tag(v_a_1540_) == 1)
{
lean_object* v_val_1541_; lean_object* v___x_1542_; 
v_val_1541_ = lean_ctor_get(v_a_1540_, 0);
lean_inc(v_val_1541_);
lean_dec_ref(v_a_1540_);
lean_inc(v_a_1258_);
lean_inc_ref(v_a_1257_);
lean_inc(v_a_1256_);
lean_inc_ref(v_a_1255_);
v___x_1542_ = lean_infer_type(v_val_1541_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1544_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref(v___x_1542_);
v___x_1544_ = l_Lean_Meta_mkNumeral(v_a_1543_, v_snd_1538_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1546_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref(v___x_1544_);
lean_inc_ref(v_binderType_1483_);
v___x_1546_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1545_, v_binderType_1483_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1548_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref(v___x_1546_);
lean_inc_ref(v_arg_1467_);
v___x_1548_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1467_, v_a_1547_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1548_) == 0)
{
lean_object* v_a_1549_; 
v_a_1549_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1549_);
lean_dec_ref(v___x_1548_);
if (lean_obj_tag(v_a_1549_) == 1)
{
lean_object* v_val_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v_val_1550_ = lean_ctor_get(v_a_1549_, 0);
lean_inc(v_val_1550_);
lean_dec_ref(v_a_1549_);
lean_inc_ref(v_arg_1469_);
lean_inc_ref(v_fn_1468_);
v___x_1551_ = l_Lean_Expr_app___override(v_fn_1468_, v_arg_1469_);
v___x_1552_ = lean_box(0);
v___x_1553_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
lean_ctor_set_uint8(v___x_1553_, sizeof(void*)*2, v___y_1533_);
v___x_1554_ = l_Lean_Meta_Simp_mkCongr(v___x_1553_, v_val_1550_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1554_) == 0)
{
lean_dec_ref(v_binderType_1483_);
lean_dec_ref(v_expr_1254_);
return v___x_1554_;
}
else
{
lean_object* v_a_1555_; 
v_a_1555_ = lean_ctor_get(v___x_1554_, 0);
lean_inc(v_a_1555_);
lean_dec_ref(v___x_1554_);
v___y_1528_ = v___y_1533_;
v_a_1529_ = v_a_1555_;
goto v___jp_1527_;
}
}
else
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v_a_1558_; 
lean_dec(v_a_1549_);
v___x_1556_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1557_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1556_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
lean_inc(v_a_1558_);
lean_dec_ref(v___x_1557_);
v___y_1528_ = v___y_1533_;
v_a_1529_ = v_a_1558_;
goto v___jp_1527_;
}
}
else
{
lean_object* v_a_1559_; 
v_a_1559_ = lean_ctor_get(v___x_1548_, 0);
lean_inc(v_a_1559_);
lean_dec_ref(v___x_1548_);
v___y_1528_ = v___y_1533_;
v_a_1529_ = v_a_1559_;
goto v___jp_1527_;
}
}
else
{
lean_object* v_a_1560_; 
v_a_1560_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1560_);
lean_dec_ref(v___x_1546_);
v___y_1528_ = v___y_1533_;
v_a_1529_ = v_a_1560_;
goto v___jp_1527_;
}
}
else
{
lean_object* v_a_1561_; 
v_a_1561_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1561_);
lean_dec_ref(v___x_1544_);
v___y_1528_ = v___y_1533_;
v_a_1529_ = v_a_1561_;
goto v___jp_1527_;
}
}
else
{
lean_object* v_a_1562_; 
lean_dec(v_snd_1538_);
v_a_1562_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1562_);
lean_dec_ref(v___x_1542_);
v___y_1528_ = v___y_1533_;
v_a_1529_ = v_a_1562_;
goto v___jp_1527_;
}
}
else
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v_a_1565_; 
lean_dec(v_a_1540_);
lean_dec(v_snd_1538_);
v___x_1563_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1564_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1563_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref(v___x_1564_);
v___y_1528_ = v___y_1533_;
v_a_1529_ = v_a_1565_;
goto v___jp_1527_;
}
}
else
{
lean_object* v_a_1566_; 
lean_dec(v_snd_1538_);
v_a_1566_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1566_);
lean_dec_ref(v___x_1539_);
v___y_1528_ = v___y_1533_;
v_a_1529_ = v_a_1566_;
goto v___jp_1527_;
}
}
else
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1536_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
lean_dec(v___x_1536_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; 
lean_dec_ref(v_binderType_1483_);
lean_dec_ref(v_expr_1254_);
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref(v___x_1567_);
v_a_1266_ = v_a_1568_;
goto v___jp_1265_;
}
else
{
lean_object* v_a_1569_; 
v_a_1569_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1569_);
lean_dec_ref(v___x_1567_);
v___y_1528_ = v___y_1533_;
v_a_1529_ = v_a_1569_;
goto v___jp_1527_;
}
}
}
else
{
lean_object* v___x_1570_; 
lean_dec_ref(v_binderType_1483_);
lean_dec_ref(v_expr_1254_);
v___x_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1570_, 0, v___y_1534_);
return v___x_1570_;
}
}
v___jp_1571_:
{
uint8_t v___x_1574_; 
v___x_1574_ = l_Lean_Exception_isInterrupt(v_a_1573_);
if (v___x_1574_ == 0)
{
uint8_t v___x_1575_; 
lean_inc_ref(v_a_1573_);
v___x_1575_ = l_Lean_Exception_isRuntime(v_a_1573_);
v___y_1533_ = v___y_1572_;
v___y_1534_ = v_a_1573_;
v___y_1535_ = v___x_1575_;
goto v___jp_1532_;
}
else
{
v___y_1533_ = v___y_1572_;
v___y_1534_ = v_a_1573_;
v___y_1535_ = v___x_1574_;
goto v___jp_1532_;
}
}
v___jp_1576_:
{
if (lean_obj_tag(v___y_1578_) == 0)
{
lean_dec_ref(v_binderType_1483_);
lean_dec_ref(v_expr_1254_);
return v___y_1578_;
}
else
{
lean_object* v_a_1579_; 
v_a_1579_ = lean_ctor_get(v___y_1578_, 0);
lean_inc(v_a_1579_);
lean_dec_ref(v___y_1578_);
v___y_1572_ = v___y_1577_;
v_a_1573_ = v_a_1579_;
goto v___jp_1571_;
}
}
v___jp_1580_:
{
if (v___y_1585_ == 0)
{
lean_object* v___x_1586_; 
lean_dec_ref(v___y_1582_);
v___x_1586_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v___y_1584_, v___y_1583_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; lean_object* v___x_1588_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref(v___x_1586_);
lean_inc_ref(v_binderType_1483_);
v___x_1588_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1587_, v_binderType_1483_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1590_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_a_1589_);
lean_dec_ref(v___x_1588_);
lean_inc_ref(v_arg_1467_);
v___x_1590_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1467_, v_a_1589_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1590_) == 0)
{
lean_object* v_a_1591_; 
v_a_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1591_);
lean_dec_ref(v___x_1590_);
if (lean_obj_tag(v_a_1591_) == 1)
{
lean_object* v_val_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v_val_1592_ = lean_ctor_get(v_a_1591_, 0);
lean_inc(v_val_1592_);
lean_dec_ref(v_a_1591_);
lean_inc_ref(v_arg_1469_);
lean_inc_ref(v_fn_1468_);
v___x_1593_ = l_Lean_Expr_app___override(v_fn_1468_, v_arg_1469_);
v___x_1594_ = lean_box(0);
v___x_1595_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1595_, 0, v___x_1593_);
lean_ctor_set(v___x_1595_, 1, v___x_1594_);
lean_ctor_set_uint8(v___x_1595_, sizeof(void*)*2, v___y_1581_);
v___x_1596_ = l_Lean_Meta_Simp_mkCongr(v___x_1595_, v_val_1592_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v___y_1577_ = v___y_1581_;
v___y_1578_ = v___x_1596_;
goto v___jp_1576_;
}
else
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_dec(v_a_1591_);
v___x_1597_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1598_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1597_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v___y_1577_ = v___y_1581_;
v___y_1578_ = v___x_1598_;
goto v___jp_1576_;
}
}
else
{
lean_object* v_a_1599_; 
v_a_1599_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_a_1599_);
lean_dec_ref(v___x_1590_);
v___y_1572_ = v___y_1581_;
v_a_1573_ = v_a_1599_;
goto v___jp_1571_;
}
}
else
{
lean_object* v_a_1600_; 
v_a_1600_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_a_1600_);
lean_dec_ref(v___x_1588_);
v___y_1572_ = v___y_1581_;
v_a_1573_ = v_a_1600_;
goto v___jp_1571_;
}
}
else
{
lean_object* v_a_1601_; 
v_a_1601_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1601_);
lean_dec_ref(v___x_1586_);
v___y_1572_ = v___y_1581_;
v_a_1573_ = v_a_1601_;
goto v___jp_1571_;
}
}
else
{
lean_dec_ref(v___y_1584_);
lean_dec_ref(v___y_1583_);
v___y_1572_ = v___y_1581_;
v_a_1573_ = v___y_1582_;
goto v___jp_1571_;
}
}
v___jp_1602_:
{
uint8_t v___x_1607_; 
v___x_1607_ = l_Lean_Exception_isInterrupt(v_a_1606_);
if (v___x_1607_ == 0)
{
uint8_t v___x_1608_; 
lean_inc_ref(v_a_1606_);
v___x_1608_ = l_Lean_Exception_isRuntime(v_a_1606_);
v___y_1581_ = v___y_1603_;
v___y_1582_ = v_a_1606_;
v___y_1583_ = v___y_1605_;
v___y_1584_ = v___y_1604_;
v___y_1585_ = v___x_1608_;
goto v___jp_1580_;
}
else
{
v___y_1581_ = v___y_1603_;
v___y_1582_ = v_a_1606_;
v___y_1583_ = v___y_1605_;
v___y_1584_ = v___y_1604_;
v___y_1585_ = v___x_1607_;
goto v___jp_1580_;
}
}
v___jp_1609_:
{
if (lean_obj_tag(v___y_1613_) == 0)
{
lean_dec_ref(v___y_1612_);
lean_dec_ref(v___y_1611_);
lean_dec_ref(v_binderType_1483_);
lean_dec_ref(v_expr_1254_);
return v___y_1613_;
}
else
{
lean_object* v_a_1614_; 
v_a_1614_ = lean_ctor_get(v___y_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref(v___y_1613_);
v___y_1603_ = v___y_1610_;
v___y_1604_ = v___y_1612_;
v___y_1605_ = v___y_1611_;
v_a_1606_ = v_a_1614_;
goto v___jp_1602_;
}
}
v___jp_1615_:
{
if (v___y_1618_ == 0)
{
lean_object* v___x_1619_; 
lean_dec_ref(v___y_1617_);
v___x_1619_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1469_);
if (lean_obj_tag(v___x_1619_) == 1)
{
lean_object* v_val_1620_; lean_object* v_snd_1621_; lean_object* v___x_1622_; 
v_val_1620_ = lean_ctor_get(v___x_1619_, 0);
lean_inc(v_val_1620_);
lean_dec_ref(v___x_1619_);
v_snd_1621_ = lean_ctor_get(v_val_1620_, 1);
lean_inc(v_snd_1621_);
lean_dec(v_val_1620_);
v___x_1622_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1467_, v_a_1258_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1623_);
lean_dec_ref(v___x_1622_);
if (lean_obj_tag(v_a_1623_) == 1)
{
lean_object* v_val_1624_; lean_object* v___x_1625_; 
v_val_1624_ = lean_ctor_get(v_a_1623_, 0);
lean_inc(v_val_1624_);
lean_dec_ref(v_a_1623_);
lean_inc(v_a_1258_);
lean_inc_ref(v_a_1257_);
lean_inc(v_a_1256_);
lean_inc_ref(v_a_1255_);
v___x_1625_ = lean_infer_type(v_val_1624_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1627_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1626_);
lean_dec_ref(v___x_1625_);
v___x_1627_ = l_Lean_Meta_mkNumeral(v_a_1626_, v_snd_1621_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_a_1628_; lean_object* v___x_1629_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1628_);
lean_dec_ref(v___x_1627_);
v___x_1629_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1628_, v_binderType_1483_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1631_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1630_);
lean_dec_ref(v___x_1629_);
lean_inc_ref(v_arg_1469_);
v___x_1631_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1469_, v_a_1630_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_a_1632_);
lean_dec_ref(v___x_1631_);
if (lean_obj_tag(v_a_1632_) == 1)
{
lean_object* v_val_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v_val_1633_ = lean_ctor_get(v_a_1632_, 0);
lean_inc(v_val_1633_);
lean_dec_ref(v_a_1632_);
v___x_1634_ = lean_box(0);
lean_inc_ref(v_fn_1468_);
v___x_1635_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1635_, 0, v_fn_1468_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
lean_ctor_set_uint8(v___x_1635_, sizeof(void*)*2, v___y_1616_);
v___x_1636_ = l_Lean_Meta_Simp_mkCongr(v___x_1635_, v_val_1633_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1638_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1637_);
lean_dec_ref(v___x_1636_);
lean_inc_ref(v_arg_1467_);
v___x_1638_ = l_Lean_Meta_Simp_mkCongrFun(v_a_1637_, v_arg_1467_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_dec_ref(v_expr_1254_);
return v___x_1638_;
}
else
{
lean_object* v_a_1639_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
lean_dec_ref(v___x_1638_);
v___y_1462_ = v___y_1616_;
v_a_1463_ = v_a_1639_;
goto v___jp_1461_;
}
}
else
{
lean_object* v_a_1640_; 
v_a_1640_ = lean_ctor_get(v___x_1636_, 0);
lean_inc(v_a_1640_);
lean_dec_ref(v___x_1636_);
v___y_1462_ = v___y_1616_;
v_a_1463_ = v_a_1640_;
goto v___jp_1461_;
}
}
else
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v_a_1643_; 
lean_dec(v_a_1632_);
v___x_1641_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1642_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1641_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
lean_inc(v_a_1643_);
lean_dec_ref(v___x_1642_);
v___y_1462_ = v___y_1616_;
v_a_1463_ = v_a_1643_;
goto v___jp_1461_;
}
}
else
{
lean_object* v_a_1644_; 
v_a_1644_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_a_1644_);
lean_dec_ref(v___x_1631_);
v___y_1462_ = v___y_1616_;
v_a_1463_ = v_a_1644_;
goto v___jp_1461_;
}
}
else
{
lean_object* v_a_1645_; 
v_a_1645_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_a_1645_);
lean_dec_ref(v___x_1629_);
v___y_1462_ = v___y_1616_;
v_a_1463_ = v_a_1645_;
goto v___jp_1461_;
}
}
else
{
lean_object* v_a_1646_; 
lean_dec_ref(v_binderType_1483_);
v_a_1646_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1646_);
lean_dec_ref(v___x_1627_);
v___y_1462_ = v___y_1616_;
v_a_1463_ = v_a_1646_;
goto v___jp_1461_;
}
}
else
{
lean_object* v_a_1647_; 
lean_dec(v_snd_1621_);
lean_dec_ref(v_binderType_1483_);
v_a_1647_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1647_);
lean_dec_ref(v___x_1625_);
v___y_1462_ = v___y_1616_;
v_a_1463_ = v_a_1647_;
goto v___jp_1461_;
}
}
else
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v_a_1650_; 
lean_dec(v_a_1623_);
lean_dec(v_snd_1621_);
lean_dec_ref(v_binderType_1483_);
v___x_1648_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1649_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1648_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_a_1650_);
lean_dec_ref(v___x_1649_);
v___y_1462_ = v___y_1616_;
v_a_1463_ = v_a_1650_;
goto v___jp_1461_;
}
}
else
{
lean_object* v_a_1651_; 
lean_dec(v_snd_1621_);
lean_dec_ref(v_binderType_1483_);
v_a_1651_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1651_);
lean_dec_ref(v___x_1622_);
v___y_1462_ = v___y_1616_;
v_a_1463_ = v_a_1651_;
goto v___jp_1461_;
}
}
else
{
lean_object* v___x_1652_; 
lean_dec_ref(v_binderType_1483_);
v___x_1652_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1619_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
lean_dec(v___x_1619_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; 
lean_dec_ref(v_expr_1254_);
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1653_);
lean_dec_ref(v___x_1652_);
v_a_1276_ = v_a_1653_;
goto v___jp_1275_;
}
else
{
lean_object* v_a_1654_; 
v_a_1654_ = lean_ctor_get(v___x_1652_, 0);
lean_inc(v_a_1654_);
lean_dec_ref(v___x_1652_);
v___y_1462_ = v___y_1616_;
v_a_1463_ = v_a_1654_;
goto v___jp_1461_;
}
}
}
else
{
lean_object* v___x_1655_; 
lean_dec_ref(v_binderType_1483_);
lean_dec_ref(v_expr_1254_);
v___x_1655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1655_, 0, v___y_1617_);
return v___x_1655_;
}
}
v___jp_1656_:
{
uint8_t v___x_1659_; 
v___x_1659_ = l_Lean_Exception_isInterrupt(v_a_1658_);
if (v___x_1659_ == 0)
{
uint8_t v___x_1660_; 
lean_inc_ref(v_a_1658_);
v___x_1660_ = l_Lean_Exception_isRuntime(v_a_1658_);
v___y_1616_ = v___y_1657_;
v___y_1617_ = v_a_1658_;
v___y_1618_ = v___x_1660_;
goto v___jp_1615_;
}
else
{
v___y_1616_ = v___y_1657_;
v___y_1617_ = v_a_1658_;
v___y_1618_ = v___x_1659_;
goto v___jp_1615_;
}
}
v___jp_1661_:
{
if (v___y_1664_ == 0)
{
lean_object* v___x_1665_; 
lean_dec_ref(v___y_1663_);
v___x_1665_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1467_);
if (lean_obj_tag(v___x_1665_) == 1)
{
lean_object* v_val_1666_; lean_object* v_snd_1667_; lean_object* v___x_1668_; 
v_val_1666_ = lean_ctor_get(v___x_1665_, 0);
lean_inc(v_val_1666_);
lean_dec_ref(v___x_1665_);
v_snd_1667_ = lean_ctor_get(v_val_1666_, 1);
lean_inc(v_snd_1667_);
lean_dec(v_val_1666_);
v___x_1668_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1469_, v_a_1258_);
if (lean_obj_tag(v___x_1668_) == 0)
{
lean_object* v_a_1669_; 
v_a_1669_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1669_);
lean_dec_ref(v___x_1668_);
if (lean_obj_tag(v_a_1669_) == 1)
{
lean_object* v_val_1670_; lean_object* v___x_1671_; 
v_val_1670_ = lean_ctor_get(v_a_1669_, 0);
lean_inc(v_val_1670_);
lean_dec_ref(v_a_1669_);
lean_inc(v_a_1258_);
lean_inc_ref(v_a_1257_);
lean_inc(v_a_1256_);
lean_inc_ref(v_a_1255_);
v___x_1671_ = lean_infer_type(v_val_1670_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1673_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_a_1672_);
lean_dec_ref(v___x_1671_);
v___x_1673_ = l_Lean_Meta_mkNumeral(v_a_1672_, v_snd_1667_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; lean_object* v___x_1675_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref(v___x_1673_);
lean_inc_ref(v_binderType_1483_);
v___x_1675_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1674_, v_binderType_1483_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v___x_1677_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1676_);
lean_dec_ref(v___x_1675_);
lean_inc_ref(v_arg_1467_);
v___x_1677_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1467_, v_a_1676_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_a_1678_; 
v_a_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_a_1678_);
lean_dec_ref(v___x_1677_);
if (lean_obj_tag(v_a_1678_) == 1)
{
lean_object* v_val_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v_val_1679_ = lean_ctor_get(v_a_1678_, 0);
lean_inc(v_val_1679_);
lean_dec_ref(v_a_1678_);
lean_inc_ref(v_arg_1469_);
lean_inc_ref(v_fn_1468_);
v___x_1680_ = l_Lean_Expr_app___override(v_fn_1468_, v_arg_1469_);
v___x_1681_ = lean_box(0);
v___x_1682_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1682_, 0, v___x_1680_);
lean_ctor_set(v___x_1682_, 1, v___x_1681_);
lean_ctor_set_uint8(v___x_1682_, sizeof(void*)*2, v___y_1662_);
v___x_1683_ = l_Lean_Meta_Simp_mkCongr(v___x_1682_, v_val_1679_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1683_) == 0)
{
lean_dec_ref(v_binderType_1483_);
lean_dec_ref(v_expr_1254_);
return v___x_1683_;
}
else
{
lean_object* v_a_1684_; 
v_a_1684_ = lean_ctor_get(v___x_1683_, 0);
lean_inc(v_a_1684_);
lean_dec_ref(v___x_1683_);
v___y_1657_ = v___y_1662_;
v_a_1658_ = v_a_1684_;
goto v___jp_1656_;
}
}
else
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v_a_1687_; 
lean_dec(v_a_1678_);
v___x_1685_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1686_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1685_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_a_1687_);
lean_dec_ref(v___x_1686_);
v___y_1657_ = v___y_1662_;
v_a_1658_ = v_a_1687_;
goto v___jp_1656_;
}
}
else
{
lean_object* v_a_1688_; 
v_a_1688_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_a_1688_);
lean_dec_ref(v___x_1677_);
v___y_1657_ = v___y_1662_;
v_a_1658_ = v_a_1688_;
goto v___jp_1656_;
}
}
else
{
lean_object* v_a_1689_; 
v_a_1689_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1689_);
lean_dec_ref(v___x_1675_);
v___y_1657_ = v___y_1662_;
v_a_1658_ = v_a_1689_;
goto v___jp_1656_;
}
}
else
{
lean_object* v_a_1690_; 
v_a_1690_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1690_);
lean_dec_ref(v___x_1673_);
v___y_1657_ = v___y_1662_;
v_a_1658_ = v_a_1690_;
goto v___jp_1656_;
}
}
else
{
lean_object* v_a_1691_; 
lean_dec(v_snd_1667_);
v_a_1691_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_a_1691_);
lean_dec_ref(v___x_1671_);
v___y_1657_ = v___y_1662_;
v_a_1658_ = v_a_1691_;
goto v___jp_1656_;
}
}
else
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v_a_1694_; 
lean_dec(v_a_1669_);
lean_dec(v_snd_1667_);
v___x_1692_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1693_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1692_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
lean_dec_ref(v___x_1693_);
v___y_1657_ = v___y_1662_;
v_a_1658_ = v_a_1694_;
goto v___jp_1656_;
}
}
else
{
lean_object* v_a_1695_; 
lean_dec(v_snd_1667_);
v_a_1695_ = lean_ctor_get(v___x_1668_, 0);
lean_inc(v_a_1695_);
lean_dec_ref(v___x_1668_);
v___y_1657_ = v___y_1662_;
v_a_1658_ = v_a_1695_;
goto v___jp_1656_;
}
}
else
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1665_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
lean_dec(v___x_1665_);
if (lean_obj_tag(v___x_1696_) == 0)
{
lean_object* v_a_1697_; 
lean_dec_ref(v_binderType_1483_);
lean_dec_ref(v_expr_1254_);
v_a_1697_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1697_);
lean_dec_ref(v___x_1696_);
v_a_1276_ = v_a_1697_;
goto v___jp_1275_;
}
else
{
lean_object* v_a_1698_; 
v_a_1698_ = lean_ctor_get(v___x_1696_, 0);
lean_inc(v_a_1698_);
lean_dec_ref(v___x_1696_);
v___y_1657_ = v___y_1662_;
v_a_1658_ = v_a_1698_;
goto v___jp_1656_;
}
}
}
else
{
lean_object* v___x_1699_; 
lean_dec_ref(v_binderType_1483_);
lean_dec_ref(v_expr_1254_);
v___x_1699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1699_, 0, v___y_1663_);
return v___x_1699_;
}
}
v___jp_1700_:
{
uint8_t v___x_1703_; 
v___x_1703_ = l_Lean_Exception_isInterrupt(v_a_1702_);
if (v___x_1703_ == 0)
{
uint8_t v___x_1704_; 
lean_inc_ref(v_a_1702_);
v___x_1704_ = l_Lean_Exception_isRuntime(v_a_1702_);
v___y_1662_ = v___y_1701_;
v___y_1663_ = v_a_1702_;
v___y_1664_ = v___x_1704_;
goto v___jp_1661_;
}
else
{
v___y_1662_ = v___y_1701_;
v___y_1663_ = v_a_1702_;
v___y_1664_ = v___x_1703_;
goto v___jp_1661_;
}
}
v___jp_1705_:
{
if (lean_obj_tag(v___y_1707_) == 0)
{
lean_dec_ref(v_binderType_1483_);
lean_dec_ref(v_expr_1254_);
return v___y_1707_;
}
else
{
lean_object* v_a_1708_; 
v_a_1708_ = lean_ctor_get(v___y_1707_, 0);
lean_inc(v_a_1708_);
lean_dec_ref(v___y_1707_);
v___y_1701_ = v___y_1706_;
v_a_1702_ = v_a_1708_;
goto v___jp_1700_;
}
}
v___jp_1709_:
{
if (v___y_1714_ == 0)
{
lean_object* v___x_1715_; 
lean_dec_ref(v___y_1712_);
v___x_1715_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v___y_1711_, v___y_1713_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; lean_object* v___x_1717_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_a_1716_);
lean_dec_ref(v___x_1715_);
lean_inc_ref(v_binderType_1483_);
v___x_1717_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1716_, v_binderType_1483_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1719_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1718_);
lean_dec_ref(v___x_1717_);
lean_inc_ref(v_arg_1467_);
v___x_1719_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1467_, v_a_1718_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref(v___x_1719_);
if (lean_obj_tag(v_a_1720_) == 1)
{
lean_object* v_val_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v_val_1721_ = lean_ctor_get(v_a_1720_, 0);
lean_inc(v_val_1721_);
lean_dec_ref(v_a_1720_);
lean_inc_ref(v_arg_1469_);
lean_inc_ref(v_fn_1468_);
v___x_1722_ = l_Lean_Expr_app___override(v_fn_1468_, v_arg_1469_);
v___x_1723_ = lean_box(0);
v___x_1724_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1724_, 0, v___x_1722_);
lean_ctor_set(v___x_1724_, 1, v___x_1723_);
lean_ctor_set_uint8(v___x_1724_, sizeof(void*)*2, v___y_1710_);
v___x_1725_ = l_Lean_Meta_Simp_mkCongr(v___x_1724_, v_val_1721_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v___y_1706_ = v___y_1710_;
v___y_1707_ = v___x_1725_;
goto v___jp_1705_;
}
else
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
lean_dec(v_a_1720_);
v___x_1726_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1727_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1726_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v___y_1706_ = v___y_1710_;
v___y_1707_ = v___x_1727_;
goto v___jp_1705_;
}
}
else
{
lean_object* v_a_1728_; 
v_a_1728_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1728_);
lean_dec_ref(v___x_1719_);
v___y_1701_ = v___y_1710_;
v_a_1702_ = v_a_1728_;
goto v___jp_1700_;
}
}
else
{
lean_object* v_a_1729_; 
v_a_1729_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1729_);
lean_dec_ref(v___x_1717_);
v___y_1701_ = v___y_1710_;
v_a_1702_ = v_a_1729_;
goto v___jp_1700_;
}
}
else
{
lean_object* v_a_1730_; 
v_a_1730_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_a_1730_);
lean_dec_ref(v___x_1715_);
v___y_1701_ = v___y_1710_;
v_a_1702_ = v_a_1730_;
goto v___jp_1700_;
}
}
else
{
lean_dec_ref(v___y_1713_);
lean_dec_ref(v___y_1711_);
v___y_1701_ = v___y_1710_;
v_a_1702_ = v___y_1712_;
goto v___jp_1700_;
}
}
v___jp_1731_:
{
uint8_t v___x_1736_; 
v___x_1736_ = l_Lean_Exception_isInterrupt(v_a_1735_);
if (v___x_1736_ == 0)
{
uint8_t v___x_1737_; 
lean_inc_ref(v_a_1735_);
v___x_1737_ = l_Lean_Exception_isRuntime(v_a_1735_);
v___y_1710_ = v___y_1732_;
v___y_1711_ = v___y_1733_;
v___y_1712_ = v_a_1735_;
v___y_1713_ = v___y_1734_;
v___y_1714_ = v___x_1737_;
goto v___jp_1709_;
}
else
{
v___y_1710_ = v___y_1732_;
v___y_1711_ = v___y_1733_;
v___y_1712_ = v_a_1735_;
v___y_1713_ = v___y_1734_;
v___y_1714_ = v___x_1736_;
goto v___jp_1709_;
}
}
v___jp_1738_:
{
if (lean_obj_tag(v___y_1742_) == 0)
{
lean_dec_ref(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec_ref(v_binderType_1483_);
lean_dec_ref(v_expr_1254_);
return v___y_1742_;
}
else
{
lean_object* v_a_1743_; 
v_a_1743_ = lean_ctor_get(v___y_1742_, 0);
lean_inc(v_a_1743_);
lean_dec_ref(v___y_1742_);
v___y_1732_ = v___y_1739_;
v___y_1733_ = v___y_1740_;
v___y_1734_ = v___y_1741_;
v_a_1735_ = v_a_1743_;
goto v___jp_1731_;
}
}
v___jp_1744_:
{
if (v___y_1754_ == 0)
{
lean_object* v___x_1755_; 
lean_dec_ref(v___y_1748_);
v___x_1755_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1469_);
if (lean_obj_tag(v___x_1755_) == 1)
{
lean_object* v_val_1756_; lean_object* v_snd_1757_; lean_object* v___x_1758_; 
v_val_1756_ = lean_ctor_get(v___x_1755_, 0);
lean_inc(v_val_1756_);
lean_dec_ref(v___x_1755_);
v_snd_1757_ = lean_ctor_get(v_val_1756_, 1);
lean_inc(v_snd_1757_);
lean_dec(v_val_1756_);
v___x_1758_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1467_, v_a_1258_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref(v___x_1758_);
if (lean_obj_tag(v_a_1759_) == 1)
{
lean_object* v_val_1760_; lean_object* v___x_1761_; 
v_val_1760_ = lean_ctor_get(v_a_1759_, 0);
lean_inc(v_val_1760_);
lean_dec_ref(v_a_1759_);
lean_inc(v_a_1258_);
lean_inc_ref(v_a_1257_);
lean_inc(v_a_1256_);
lean_inc_ref(v_a_1255_);
v___x_1761_ = lean_infer_type(v_val_1760_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1763_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref(v___x_1761_);
v___x_1763_ = l_Lean_Meta_mkNumeral(v_a_1762_, v_snd_1757_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; lean_object* v___x_1765_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref(v___x_1763_);
v___x_1765_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1764_, v_binderType_1483_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1767_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1766_);
lean_dec_ref(v___x_1765_);
lean_inc_ref(v_arg_1469_);
v___x_1767_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1469_, v_a_1766_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_a_1768_; 
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_a_1768_);
lean_dec_ref(v___x_1767_);
if (lean_obj_tag(v_a_1768_) == 1)
{
lean_object* v_val_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v_val_1769_ = lean_ctor_get(v_a_1768_, 0);
lean_inc(v_val_1769_);
lean_dec_ref(v_a_1768_);
v___x_1770_ = lean_box(0);
lean_inc_ref(v_fn_1468_);
v___x_1771_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1771_, 0, v_fn_1468_);
lean_ctor_set(v___x_1771_, 1, v___x_1770_);
lean_ctor_set_uint8(v___x_1771_, sizeof(void*)*2, v___y_1746_);
v___x_1772_ = l_Lean_Meta_Simp_mkCongr(v___x_1771_, v_val_1769_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_object* v_a_1773_; lean_object* v___x_1774_; 
v_a_1773_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1773_);
lean_dec_ref(v___x_1772_);
lean_inc_ref(v_arg_1467_);
v___x_1774_ = l_Lean_Meta_Simp_mkCongrFun(v_a_1773_, v_arg_1467_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; 
lean_dec_ref(v_expr_1254_);
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
lean_dec_ref(v___x_1774_);
v___y_1383_ = v___y_1746_;
v___y_1384_ = v___y_1745_;
v___y_1385_ = v___y_1747_;
v___y_1386_ = v___y_1750_;
v___y_1387_ = v___y_1749_;
v___y_1388_ = v___y_1751_;
v___y_1389_ = v___y_1752_;
v___y_1390_ = v___y_1753_;
v_a_1391_ = v_a_1775_;
goto v___jp_1382_;
}
else
{
lean_object* v_a_1776_; 
v_a_1776_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1776_);
lean_dec_ref(v___x_1774_);
v___y_1429_ = v___y_1746_;
v___y_1430_ = v___y_1745_;
v___y_1431_ = v___y_1747_;
v___y_1432_ = v___y_1750_;
v___y_1433_ = v___y_1749_;
v___y_1434_ = v___y_1751_;
v___y_1435_ = v___y_1752_;
v___y_1436_ = v___y_1753_;
v_a_1437_ = v_a_1776_;
goto v___jp_1428_;
}
}
else
{
lean_object* v_a_1777_; 
v_a_1777_ = lean_ctor_get(v___x_1772_, 0);
lean_inc(v_a_1777_);
lean_dec_ref(v___x_1772_);
v___y_1429_ = v___y_1746_;
v___y_1430_ = v___y_1745_;
v___y_1431_ = v___y_1747_;
v___y_1432_ = v___y_1750_;
v___y_1433_ = v___y_1749_;
v___y_1434_ = v___y_1751_;
v___y_1435_ = v___y_1752_;
v___y_1436_ = v___y_1753_;
v_a_1437_ = v_a_1777_;
goto v___jp_1428_;
}
}
else
{
lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v_a_1780_; 
lean_dec(v_a_1768_);
v___x_1778_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1779_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1778_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc(v_a_1780_);
lean_dec_ref(v___x_1779_);
v___y_1429_ = v___y_1746_;
v___y_1430_ = v___y_1745_;
v___y_1431_ = v___y_1747_;
v___y_1432_ = v___y_1750_;
v___y_1433_ = v___y_1749_;
v___y_1434_ = v___y_1751_;
v___y_1435_ = v___y_1752_;
v___y_1436_ = v___y_1753_;
v_a_1437_ = v_a_1780_;
goto v___jp_1428_;
}
}
else
{
lean_object* v_a_1781_; 
v_a_1781_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_a_1781_);
lean_dec_ref(v___x_1767_);
v___y_1429_ = v___y_1746_;
v___y_1430_ = v___y_1745_;
v___y_1431_ = v___y_1747_;
v___y_1432_ = v___y_1750_;
v___y_1433_ = v___y_1749_;
v___y_1434_ = v___y_1751_;
v___y_1435_ = v___y_1752_;
v___y_1436_ = v___y_1753_;
v_a_1437_ = v_a_1781_;
goto v___jp_1428_;
}
}
else
{
lean_object* v_a_1782_; 
v_a_1782_ = lean_ctor_get(v___x_1765_, 0);
lean_inc(v_a_1782_);
lean_dec_ref(v___x_1765_);
v___y_1429_ = v___y_1746_;
v___y_1430_ = v___y_1745_;
v___y_1431_ = v___y_1747_;
v___y_1432_ = v___y_1750_;
v___y_1433_ = v___y_1749_;
v___y_1434_ = v___y_1751_;
v___y_1435_ = v___y_1752_;
v___y_1436_ = v___y_1753_;
v_a_1437_ = v_a_1782_;
goto v___jp_1428_;
}
}
else
{
lean_object* v_a_1783_; 
lean_dec_ref(v_binderType_1483_);
v_a_1783_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1783_);
lean_dec_ref(v___x_1763_);
v___y_1429_ = v___y_1746_;
v___y_1430_ = v___y_1745_;
v___y_1431_ = v___y_1747_;
v___y_1432_ = v___y_1750_;
v___y_1433_ = v___y_1749_;
v___y_1434_ = v___y_1751_;
v___y_1435_ = v___y_1752_;
v___y_1436_ = v___y_1753_;
v_a_1437_ = v_a_1783_;
goto v___jp_1428_;
}
}
else
{
lean_object* v_a_1784_; 
lean_dec(v_snd_1757_);
lean_dec_ref(v_binderType_1483_);
v_a_1784_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1784_);
lean_dec_ref(v___x_1761_);
v___y_1429_ = v___y_1746_;
v___y_1430_ = v___y_1745_;
v___y_1431_ = v___y_1747_;
v___y_1432_ = v___y_1750_;
v___y_1433_ = v___y_1749_;
v___y_1434_ = v___y_1751_;
v___y_1435_ = v___y_1752_;
v___y_1436_ = v___y_1753_;
v_a_1437_ = v_a_1784_;
goto v___jp_1428_;
}
}
else
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v_a_1787_; 
lean_dec(v_a_1759_);
lean_dec(v_snd_1757_);
lean_dec_ref(v_binderType_1483_);
v___x_1785_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1786_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1785_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v_a_1787_ = lean_ctor_get(v___x_1786_, 0);
lean_inc(v_a_1787_);
lean_dec_ref(v___x_1786_);
v___y_1429_ = v___y_1746_;
v___y_1430_ = v___y_1745_;
v___y_1431_ = v___y_1747_;
v___y_1432_ = v___y_1750_;
v___y_1433_ = v___y_1749_;
v___y_1434_ = v___y_1751_;
v___y_1435_ = v___y_1752_;
v___y_1436_ = v___y_1753_;
v_a_1437_ = v_a_1787_;
goto v___jp_1428_;
}
}
else
{
lean_object* v_a_1788_; 
lean_dec(v_snd_1757_);
lean_dec_ref(v_binderType_1483_);
v_a_1788_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1788_);
lean_dec_ref(v___x_1758_);
v___y_1429_ = v___y_1746_;
v___y_1430_ = v___y_1745_;
v___y_1431_ = v___y_1747_;
v___y_1432_ = v___y_1750_;
v___y_1433_ = v___y_1749_;
v___y_1434_ = v___y_1751_;
v___y_1435_ = v___y_1752_;
v___y_1436_ = v___y_1753_;
v_a_1437_ = v_a_1788_;
goto v___jp_1428_;
}
}
else
{
lean_object* v___x_1789_; 
lean_dec_ref(v_binderType_1483_);
v___x_1789_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1755_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
lean_dec(v___x_1755_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_object* v_a_1790_; 
lean_dec_ref(v_expr_1254_);
v_a_1790_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_a_1790_);
lean_dec_ref(v___x_1789_);
v___y_1394_ = v___y_1745_;
v___y_1395_ = v___y_1746_;
v___y_1396_ = v___y_1747_;
v___y_1397_ = v___y_1749_;
v___y_1398_ = v___y_1750_;
v___y_1399_ = v___y_1751_;
v___y_1400_ = v___y_1752_;
v___y_1401_ = v___y_1753_;
v_a_1402_ = v_a_1790_;
goto v___jp_1393_;
}
else
{
lean_object* v_a_1791_; 
v_a_1791_ = lean_ctor_get(v___x_1789_, 0);
lean_inc(v_a_1791_);
lean_dec_ref(v___x_1789_);
v___y_1429_ = v___y_1746_;
v___y_1430_ = v___y_1745_;
v___y_1431_ = v___y_1747_;
v___y_1432_ = v___y_1750_;
v___y_1433_ = v___y_1749_;
v___y_1434_ = v___y_1751_;
v___y_1435_ = v___y_1752_;
v___y_1436_ = v___y_1753_;
v_a_1437_ = v_a_1791_;
goto v___jp_1428_;
}
}
}
else
{
lean_dec_ref(v_binderType_1483_);
lean_dec_ref(v_expr_1254_);
v___y_1405_ = v___y_1746_;
v___y_1406_ = v___y_1745_;
v___y_1407_ = v___y_1747_;
v___y_1408_ = v___y_1750_;
v___y_1409_ = v___y_1749_;
v___y_1410_ = v___y_1751_;
v___y_1411_ = v___y_1752_;
v___y_1412_ = v___y_1753_;
v_a_1413_ = v___y_1748_;
goto v___jp_1404_;
}
}
v___jp_1792_:
{
uint8_t v___x_1802_; 
v___x_1802_ = l_Lean_Exception_isInterrupt(v_a_1801_);
if (v___x_1802_ == 0)
{
uint8_t v___x_1803_; 
lean_inc_ref(v_a_1801_);
v___x_1803_ = l_Lean_Exception_isRuntime(v_a_1801_);
v___y_1745_ = v___y_1794_;
v___y_1746_ = v___y_1793_;
v___y_1747_ = v___y_1795_;
v___y_1748_ = v_a_1801_;
v___y_1749_ = v___y_1797_;
v___y_1750_ = v___y_1796_;
v___y_1751_ = v___y_1798_;
v___y_1752_ = v___y_1799_;
v___y_1753_ = v___y_1800_;
v___y_1754_ = v___x_1803_;
goto v___jp_1744_;
}
else
{
v___y_1745_ = v___y_1794_;
v___y_1746_ = v___y_1793_;
v___y_1747_ = v___y_1795_;
v___y_1748_ = v_a_1801_;
v___y_1749_ = v___y_1797_;
v___y_1750_ = v___y_1796_;
v___y_1751_ = v___y_1798_;
v___y_1752_ = v___y_1799_;
v___y_1753_ = v___y_1800_;
v___y_1754_ = v___x_1802_;
goto v___jp_1744_;
}
}
v___jp_1804_:
{
if (v___y_1814_ == 0)
{
lean_object* v___x_1815_; 
lean_dec_ref(v___y_1812_);
v___x_1815_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1467_);
if (lean_obj_tag(v___x_1815_) == 1)
{
lean_object* v_val_1816_; lean_object* v_snd_1817_; lean_object* v___x_1818_; 
v_val_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_val_1816_);
lean_dec_ref(v___x_1815_);
v_snd_1817_ = lean_ctor_get(v_val_1816_, 1);
lean_inc(v_snd_1817_);
lean_dec(v_val_1816_);
v___x_1818_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1469_, v_a_1258_);
if (lean_obj_tag(v___x_1818_) == 0)
{
lean_object* v_a_1819_; 
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1819_);
lean_dec_ref(v___x_1818_);
if (lean_obj_tag(v_a_1819_) == 1)
{
lean_object* v_val_1820_; lean_object* v___x_1821_; 
v_val_1820_ = lean_ctor_get(v_a_1819_, 0);
lean_inc(v_val_1820_);
lean_dec_ref(v_a_1819_);
lean_inc(v_a_1258_);
lean_inc_ref(v_a_1257_);
lean_inc(v_a_1256_);
lean_inc_ref(v_a_1255_);
v___x_1821_ = lean_infer_type(v_val_1820_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1823_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1822_);
lean_dec_ref(v___x_1821_);
v___x_1823_ = l_Lean_Meta_mkNumeral(v_a_1822_, v_snd_1817_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; lean_object* v___x_1825_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_a_1824_);
lean_dec_ref(v___x_1823_);
lean_inc_ref(v_binderType_1483_);
v___x_1825_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1824_, v_binderType_1483_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1827_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_a_1826_);
lean_dec_ref(v___x_1825_);
lean_inc_ref(v_arg_1467_);
v___x_1827_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1467_, v_a_1826_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v_a_1828_; 
v_a_1828_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_a_1828_);
lean_dec_ref(v___x_1827_);
if (lean_obj_tag(v_a_1828_) == 1)
{
lean_object* v_val_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
v_val_1829_ = lean_ctor_get(v_a_1828_, 0);
lean_inc(v_val_1829_);
lean_dec_ref(v_a_1828_);
lean_inc_ref(v_arg_1469_);
lean_inc_ref(v_fn_1468_);
v___x_1830_ = l_Lean_Expr_app___override(v_fn_1468_, v_arg_1469_);
v___x_1831_ = lean_box(0);
v___x_1832_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1832_, 0, v___x_1830_);
lean_ctor_set(v___x_1832_, 1, v___x_1831_);
lean_ctor_set_uint8(v___x_1832_, sizeof(void*)*2, v___y_1806_);
v___x_1833_ = l_Lean_Meta_Simp_mkCongr(v___x_1832_, v_val_1829_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; 
lean_dec_ref(v_binderType_1483_);
lean_dec_ref(v_expr_1254_);
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
lean_dec_ref(v___x_1833_);
v___y_1383_ = v___y_1806_;
v___y_1384_ = v___y_1805_;
v___y_1385_ = v___y_1807_;
v___y_1386_ = v___y_1809_;
v___y_1387_ = v___y_1808_;
v___y_1388_ = v___y_1810_;
v___y_1389_ = v___y_1811_;
v___y_1390_ = v___y_1813_;
v_a_1391_ = v_a_1834_;
goto v___jp_1382_;
}
else
{
lean_object* v_a_1835_; 
v_a_1835_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1835_);
lean_dec_ref(v___x_1833_);
v___y_1793_ = v___y_1806_;
v___y_1794_ = v___y_1805_;
v___y_1795_ = v___y_1807_;
v___y_1796_ = v___y_1809_;
v___y_1797_ = v___y_1808_;
v___y_1798_ = v___y_1810_;
v___y_1799_ = v___y_1811_;
v___y_1800_ = v___y_1813_;
v_a_1801_ = v_a_1835_;
goto v___jp_1792_;
}
}
else
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v_a_1838_; 
lean_dec(v_a_1828_);
v___x_1836_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1837_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1836_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v_a_1838_ = lean_ctor_get(v___x_1837_, 0);
lean_inc(v_a_1838_);
lean_dec_ref(v___x_1837_);
v___y_1793_ = v___y_1806_;
v___y_1794_ = v___y_1805_;
v___y_1795_ = v___y_1807_;
v___y_1796_ = v___y_1809_;
v___y_1797_ = v___y_1808_;
v___y_1798_ = v___y_1810_;
v___y_1799_ = v___y_1811_;
v___y_1800_ = v___y_1813_;
v_a_1801_ = v_a_1838_;
goto v___jp_1792_;
}
}
else
{
lean_object* v_a_1839_; 
v_a_1839_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_a_1839_);
lean_dec_ref(v___x_1827_);
v___y_1793_ = v___y_1806_;
v___y_1794_ = v___y_1805_;
v___y_1795_ = v___y_1807_;
v___y_1796_ = v___y_1809_;
v___y_1797_ = v___y_1808_;
v___y_1798_ = v___y_1810_;
v___y_1799_ = v___y_1811_;
v___y_1800_ = v___y_1813_;
v_a_1801_ = v_a_1839_;
goto v___jp_1792_;
}
}
else
{
lean_object* v_a_1840_; 
v_a_1840_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_a_1840_);
lean_dec_ref(v___x_1825_);
v___y_1793_ = v___y_1806_;
v___y_1794_ = v___y_1805_;
v___y_1795_ = v___y_1807_;
v___y_1796_ = v___y_1809_;
v___y_1797_ = v___y_1808_;
v___y_1798_ = v___y_1810_;
v___y_1799_ = v___y_1811_;
v___y_1800_ = v___y_1813_;
v_a_1801_ = v_a_1840_;
goto v___jp_1792_;
}
}
else
{
lean_object* v_a_1841_; 
v_a_1841_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_a_1841_);
lean_dec_ref(v___x_1823_);
v___y_1793_ = v___y_1806_;
v___y_1794_ = v___y_1805_;
v___y_1795_ = v___y_1807_;
v___y_1796_ = v___y_1809_;
v___y_1797_ = v___y_1808_;
v___y_1798_ = v___y_1810_;
v___y_1799_ = v___y_1811_;
v___y_1800_ = v___y_1813_;
v_a_1801_ = v_a_1841_;
goto v___jp_1792_;
}
}
else
{
lean_object* v_a_1842_; 
lean_dec(v_snd_1817_);
v_a_1842_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1842_);
lean_dec_ref(v___x_1821_);
v___y_1793_ = v___y_1806_;
v___y_1794_ = v___y_1805_;
v___y_1795_ = v___y_1807_;
v___y_1796_ = v___y_1809_;
v___y_1797_ = v___y_1808_;
v___y_1798_ = v___y_1810_;
v___y_1799_ = v___y_1811_;
v___y_1800_ = v___y_1813_;
v_a_1801_ = v_a_1842_;
goto v___jp_1792_;
}
}
else
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v_a_1845_; 
lean_dec(v_a_1819_);
lean_dec(v_snd_1817_);
v___x_1843_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1844_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1843_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v_a_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_a_1845_);
lean_dec_ref(v___x_1844_);
v___y_1793_ = v___y_1806_;
v___y_1794_ = v___y_1805_;
v___y_1795_ = v___y_1807_;
v___y_1796_ = v___y_1809_;
v___y_1797_ = v___y_1808_;
v___y_1798_ = v___y_1810_;
v___y_1799_ = v___y_1811_;
v___y_1800_ = v___y_1813_;
v_a_1801_ = v_a_1845_;
goto v___jp_1792_;
}
}
else
{
lean_object* v_a_1846_; 
lean_dec(v_snd_1817_);
v_a_1846_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_a_1846_);
lean_dec_ref(v___x_1818_);
v___y_1793_ = v___y_1806_;
v___y_1794_ = v___y_1805_;
v___y_1795_ = v___y_1807_;
v___y_1796_ = v___y_1809_;
v___y_1797_ = v___y_1808_;
v___y_1798_ = v___y_1810_;
v___y_1799_ = v___y_1811_;
v___y_1800_ = v___y_1813_;
v_a_1801_ = v_a_1846_;
goto v___jp_1792_;
}
}
else
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1815_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
lean_dec(v___x_1815_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; 
lean_dec_ref(v_binderType_1483_);
lean_dec_ref(v_expr_1254_);
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1848_);
lean_dec_ref(v___x_1847_);
v___y_1394_ = v___y_1805_;
v___y_1395_ = v___y_1806_;
v___y_1396_ = v___y_1807_;
v___y_1397_ = v___y_1808_;
v___y_1398_ = v___y_1809_;
v___y_1399_ = v___y_1810_;
v___y_1400_ = v___y_1811_;
v___y_1401_ = v___y_1813_;
v_a_1402_ = v_a_1848_;
goto v___jp_1393_;
}
else
{
lean_object* v_a_1849_; 
v_a_1849_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1849_);
lean_dec_ref(v___x_1847_);
v___y_1793_ = v___y_1806_;
v___y_1794_ = v___y_1805_;
v___y_1795_ = v___y_1807_;
v___y_1796_ = v___y_1809_;
v___y_1797_ = v___y_1808_;
v___y_1798_ = v___y_1810_;
v___y_1799_ = v___y_1811_;
v___y_1800_ = v___y_1813_;
v_a_1801_ = v_a_1849_;
goto v___jp_1792_;
}
}
}
else
{
lean_dec_ref(v_binderType_1483_);
lean_dec_ref(v_expr_1254_);
v___y_1405_ = v___y_1806_;
v___y_1406_ = v___y_1805_;
v___y_1407_ = v___y_1807_;
v___y_1408_ = v___y_1809_;
v___y_1409_ = v___y_1808_;
v___y_1410_ = v___y_1810_;
v___y_1411_ = v___y_1811_;
v___y_1412_ = v___y_1813_;
v_a_1413_ = v___y_1812_;
goto v___jp_1404_;
}
}
v___jp_1850_:
{
uint8_t v___x_1860_; 
v___x_1860_ = l_Lean_Exception_isInterrupt(v_a_1859_);
if (v___x_1860_ == 0)
{
uint8_t v___x_1861_; 
lean_inc_ref(v_a_1859_);
v___x_1861_ = l_Lean_Exception_isRuntime(v_a_1859_);
v___y_1805_ = v___y_1852_;
v___y_1806_ = v___y_1851_;
v___y_1807_ = v___y_1853_;
v___y_1808_ = v___y_1855_;
v___y_1809_ = v___y_1854_;
v___y_1810_ = v___y_1856_;
v___y_1811_ = v___y_1857_;
v___y_1812_ = v_a_1859_;
v___y_1813_ = v___y_1858_;
v___y_1814_ = v___x_1861_;
goto v___jp_1804_;
}
else
{
v___y_1805_ = v___y_1852_;
v___y_1806_ = v___y_1851_;
v___y_1807_ = v___y_1853_;
v___y_1808_ = v___y_1855_;
v___y_1809_ = v___y_1854_;
v___y_1810_ = v___y_1856_;
v___y_1811_ = v___y_1857_;
v___y_1812_ = v_a_1859_;
v___y_1813_ = v___y_1858_;
v___y_1814_ = v___x_1860_;
goto v___jp_1804_;
}
}
v___jp_1862_:
{
if (lean_obj_tag(v___y_1871_) == 0)
{
lean_object* v_a_1872_; 
lean_dec_ref(v_binderType_1483_);
lean_dec_ref(v_expr_1254_);
v_a_1872_ = lean_ctor_get(v___y_1871_, 0);
lean_inc(v_a_1872_);
lean_dec_ref(v___y_1871_);
v___y_1383_ = v___y_1864_;
v___y_1384_ = v___y_1863_;
v___y_1385_ = v___y_1865_;
v___y_1386_ = v___y_1867_;
v___y_1387_ = v___y_1866_;
v___y_1388_ = v___y_1868_;
v___y_1389_ = v___y_1869_;
v___y_1390_ = v___y_1870_;
v_a_1391_ = v_a_1872_;
goto v___jp_1382_;
}
else
{
lean_object* v_a_1873_; 
v_a_1873_ = lean_ctor_get(v___y_1871_, 0);
lean_inc(v_a_1873_);
lean_dec_ref(v___y_1871_);
v___y_1851_ = v___y_1864_;
v___y_1852_ = v___y_1863_;
v___y_1853_ = v___y_1865_;
v___y_1854_ = v___y_1867_;
v___y_1855_ = v___y_1866_;
v___y_1856_ = v___y_1868_;
v___y_1857_ = v___y_1869_;
v___y_1858_ = v___y_1870_;
v_a_1859_ = v_a_1873_;
goto v___jp_1850_;
}
}
v___jp_1874_:
{
if (v___y_1886_ == 0)
{
lean_object* v___x_1887_; 
lean_dec_ref(v___y_1877_);
v___x_1887_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v___y_1885_, v___y_1882_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1889_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1888_);
lean_dec_ref(v___x_1887_);
lean_inc_ref(v_binderType_1483_);
v___x_1889_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1888_, v_binderType_1483_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; lean_object* v___x_1891_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_a_1890_);
lean_dec_ref(v___x_1889_);
lean_inc_ref(v_arg_1467_);
v___x_1891_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1467_, v_a_1890_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1892_);
lean_dec_ref(v___x_1891_);
if (lean_obj_tag(v_a_1892_) == 1)
{
lean_object* v_val_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v_val_1893_ = lean_ctor_get(v_a_1892_, 0);
lean_inc(v_val_1893_);
lean_dec_ref(v_a_1892_);
lean_inc_ref(v_arg_1469_);
lean_inc_ref(v_fn_1468_);
v___x_1894_ = l_Lean_Expr_app___override(v_fn_1468_, v_arg_1469_);
v___x_1895_ = lean_box(0);
v___x_1896_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1896_, 0, v___x_1894_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
lean_ctor_set_uint8(v___x_1896_, sizeof(void*)*2, v___y_1876_);
v___x_1897_ = l_Lean_Meta_Simp_mkCongr(v___x_1896_, v_val_1893_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v___y_1863_ = v___y_1875_;
v___y_1864_ = v___y_1876_;
v___y_1865_ = v___y_1878_;
v___y_1866_ = v___y_1880_;
v___y_1867_ = v___y_1879_;
v___y_1868_ = v___y_1881_;
v___y_1869_ = v___y_1883_;
v___y_1870_ = v___y_1884_;
v___y_1871_ = v___x_1897_;
goto v___jp_1862_;
}
else
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
lean_dec(v_a_1892_);
v___x_1898_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1899_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1898_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v___y_1863_ = v___y_1875_;
v___y_1864_ = v___y_1876_;
v___y_1865_ = v___y_1878_;
v___y_1866_ = v___y_1880_;
v___y_1867_ = v___y_1879_;
v___y_1868_ = v___y_1881_;
v___y_1869_ = v___y_1883_;
v___y_1870_ = v___y_1884_;
v___y_1871_ = v___x_1899_;
goto v___jp_1862_;
}
}
else
{
lean_object* v_a_1900_; 
v_a_1900_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1900_);
lean_dec_ref(v___x_1891_);
v___y_1851_ = v___y_1876_;
v___y_1852_ = v___y_1875_;
v___y_1853_ = v___y_1878_;
v___y_1854_ = v___y_1879_;
v___y_1855_ = v___y_1880_;
v___y_1856_ = v___y_1881_;
v___y_1857_ = v___y_1883_;
v___y_1858_ = v___y_1884_;
v_a_1859_ = v_a_1900_;
goto v___jp_1850_;
}
}
else
{
lean_object* v_a_1901_; 
v_a_1901_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_a_1901_);
lean_dec_ref(v___x_1889_);
v___y_1851_ = v___y_1876_;
v___y_1852_ = v___y_1875_;
v___y_1853_ = v___y_1878_;
v___y_1854_ = v___y_1879_;
v___y_1855_ = v___y_1880_;
v___y_1856_ = v___y_1881_;
v___y_1857_ = v___y_1883_;
v___y_1858_ = v___y_1884_;
v_a_1859_ = v_a_1901_;
goto v___jp_1850_;
}
}
else
{
lean_object* v_a_1902_; 
v_a_1902_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1902_);
lean_dec_ref(v___x_1887_);
v___y_1851_ = v___y_1876_;
v___y_1852_ = v___y_1875_;
v___y_1853_ = v___y_1878_;
v___y_1854_ = v___y_1879_;
v___y_1855_ = v___y_1880_;
v___y_1856_ = v___y_1881_;
v___y_1857_ = v___y_1883_;
v___y_1858_ = v___y_1884_;
v_a_1859_ = v_a_1902_;
goto v___jp_1850_;
}
}
else
{
lean_dec_ref(v___y_1885_);
lean_dec_ref(v___y_1882_);
v___y_1851_ = v___y_1876_;
v___y_1852_ = v___y_1875_;
v___y_1853_ = v___y_1878_;
v___y_1854_ = v___y_1879_;
v___y_1855_ = v___y_1880_;
v___y_1856_ = v___y_1881_;
v___y_1857_ = v___y_1883_;
v___y_1858_ = v___y_1884_;
v_a_1859_ = v___y_1877_;
goto v___jp_1850_;
}
}
v___jp_1903_:
{
uint8_t v___x_1915_; 
v___x_1915_ = l_Lean_Exception_isInterrupt(v_a_1914_);
if (v___x_1915_ == 0)
{
uint8_t v___x_1916_; 
lean_inc_ref(v_a_1914_);
v___x_1916_ = l_Lean_Exception_isRuntime(v_a_1914_);
v___y_1875_ = v___y_1905_;
v___y_1876_ = v___y_1904_;
v___y_1877_ = v_a_1914_;
v___y_1878_ = v___y_1906_;
v___y_1879_ = v___y_1908_;
v___y_1880_ = v___y_1907_;
v___y_1881_ = v___y_1909_;
v___y_1882_ = v___y_1910_;
v___y_1883_ = v___y_1911_;
v___y_1884_ = v___y_1913_;
v___y_1885_ = v___y_1912_;
v___y_1886_ = v___x_1916_;
goto v___jp_1874_;
}
else
{
v___y_1875_ = v___y_1905_;
v___y_1876_ = v___y_1904_;
v___y_1877_ = v_a_1914_;
v___y_1878_ = v___y_1906_;
v___y_1879_ = v___y_1908_;
v___y_1880_ = v___y_1907_;
v___y_1881_ = v___y_1909_;
v___y_1882_ = v___y_1910_;
v___y_1883_ = v___y_1911_;
v___y_1884_ = v___y_1913_;
v___y_1885_ = v___y_1912_;
v___y_1886_ = v___x_1915_;
goto v___jp_1874_;
}
}
v___jp_1917_:
{
if (lean_obj_tag(v___y_1928_) == 0)
{
lean_object* v_a_1929_; 
lean_dec_ref(v___y_1926_);
lean_dec_ref(v___y_1924_);
lean_dec_ref(v_binderType_1483_);
lean_dec_ref(v_expr_1254_);
v_a_1929_ = lean_ctor_get(v___y_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref(v___y_1928_);
v___y_1383_ = v___y_1919_;
v___y_1384_ = v___y_1918_;
v___y_1385_ = v___y_1920_;
v___y_1386_ = v___y_1922_;
v___y_1387_ = v___y_1921_;
v___y_1388_ = v___y_1923_;
v___y_1389_ = v___y_1925_;
v___y_1390_ = v___y_1927_;
v_a_1391_ = v_a_1929_;
goto v___jp_1382_;
}
else
{
lean_object* v_a_1930_; 
v_a_1930_ = lean_ctor_get(v___y_1928_, 0);
lean_inc(v_a_1930_);
lean_dec_ref(v___y_1928_);
v___y_1904_ = v___y_1919_;
v___y_1905_ = v___y_1918_;
v___y_1906_ = v___y_1920_;
v___y_1907_ = v___y_1921_;
v___y_1908_ = v___y_1922_;
v___y_1909_ = v___y_1923_;
v___y_1910_ = v___y_1924_;
v___y_1911_ = v___y_1925_;
v___y_1912_ = v___y_1926_;
v___y_1913_ = v___y_1927_;
v_a_1914_ = v_a_1930_;
goto v___jp_1903_;
}
}
v___jp_1931_:
{
if (v___y_1941_ == 0)
{
lean_object* v___x_1942_; 
lean_dec_ref(v___y_1934_);
v___x_1942_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1469_);
if (lean_obj_tag(v___x_1942_) == 1)
{
lean_object* v_val_1943_; lean_object* v_snd_1944_; lean_object* v___x_1945_; 
v_val_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_val_1943_);
lean_dec_ref(v___x_1942_);
v_snd_1944_ = lean_ctor_get(v_val_1943_, 1);
lean_inc(v_snd_1944_);
lean_dec(v_val_1943_);
v___x_1945_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1467_, v_a_1258_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1946_);
lean_dec_ref(v___x_1945_);
if (lean_obj_tag(v_a_1946_) == 1)
{
lean_object* v_val_1947_; lean_object* v___x_1948_; 
v_val_1947_ = lean_ctor_get(v_a_1946_, 0);
lean_inc(v_val_1947_);
lean_dec_ref(v_a_1946_);
lean_inc(v_a_1258_);
lean_inc_ref(v_a_1257_);
lean_inc(v_a_1256_);
lean_inc_ref(v_a_1255_);
v___x_1948_ = lean_infer_type(v_val_1947_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v___x_1950_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1949_);
lean_dec_ref(v___x_1948_);
v___x_1950_ = l_Lean_Meta_mkNumeral(v_a_1949_, v_snd_1944_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; lean_object* v___x_1952_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1951_);
lean_dec_ref(v___x_1950_);
v___x_1952_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1951_, v_binderType_1483_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v___x_1954_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref(v___x_1952_);
lean_inc_ref(v_arg_1469_);
v___x_1954_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1469_, v_a_1953_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_1955_);
lean_dec_ref(v___x_1954_);
if (lean_obj_tag(v_a_1955_) == 1)
{
lean_object* v_val_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; 
v_val_1956_ = lean_ctor_get(v_a_1955_, 0);
lean_inc(v_val_1956_);
lean_dec_ref(v_a_1955_);
v___x_1957_ = lean_box(0);
lean_inc_ref(v_fn_1468_);
v___x_1958_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1958_, 0, v_fn_1468_);
lean_ctor_set(v___x_1958_, 1, v___x_1957_);
lean_ctor_set_uint8(v___x_1958_, sizeof(void*)*2, v___y_1933_);
v___x_1959_ = l_Lean_Meta_Simp_mkCongr(v___x_1958_, v_val_1956_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; lean_object* v___x_1961_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1960_);
lean_dec_ref(v___x_1959_);
lean_inc_ref(v_arg_1467_);
v___x_1961_ = l_Lean_Meta_Simp_mkCongrFun(v_a_1960_, v_arg_1467_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; 
lean_dec_ref(v_expr_1254_);
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_a_1962_);
lean_dec_ref(v___x_1961_);
v___y_1304_ = v___y_1933_;
v___y_1305_ = v___y_1932_;
v___y_1306_ = v___y_1935_;
v___y_1307_ = v___y_1936_;
v___y_1308_ = v___y_1938_;
v___y_1309_ = v___y_1937_;
v___y_1310_ = v___y_1939_;
v___y_1311_ = v___y_1940_;
v_a_1312_ = v_a_1962_;
goto v___jp_1303_;
}
else
{
lean_object* v_a_1963_; 
v_a_1963_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_a_1963_);
lean_dec_ref(v___x_1961_);
v___y_1350_ = v___y_1933_;
v___y_1351_ = v___y_1932_;
v___y_1352_ = v___y_1935_;
v___y_1353_ = v___y_1936_;
v___y_1354_ = v___y_1938_;
v___y_1355_ = v___y_1937_;
v___y_1356_ = v___y_1939_;
v___y_1357_ = v___y_1940_;
v_a_1358_ = v_a_1963_;
goto v___jp_1349_;
}
}
else
{
lean_object* v_a_1964_; 
v_a_1964_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1964_);
lean_dec_ref(v___x_1959_);
v___y_1350_ = v___y_1933_;
v___y_1351_ = v___y_1932_;
v___y_1352_ = v___y_1935_;
v___y_1353_ = v___y_1936_;
v___y_1354_ = v___y_1938_;
v___y_1355_ = v___y_1937_;
v___y_1356_ = v___y_1939_;
v___y_1357_ = v___y_1940_;
v_a_1358_ = v_a_1964_;
goto v___jp_1349_;
}
}
else
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v_a_1967_; 
lean_dec(v_a_1955_);
v___x_1965_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1966_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1965_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
lean_inc(v_a_1967_);
lean_dec_ref(v___x_1966_);
v___y_1350_ = v___y_1933_;
v___y_1351_ = v___y_1932_;
v___y_1352_ = v___y_1935_;
v___y_1353_ = v___y_1936_;
v___y_1354_ = v___y_1938_;
v___y_1355_ = v___y_1937_;
v___y_1356_ = v___y_1939_;
v___y_1357_ = v___y_1940_;
v_a_1358_ = v_a_1967_;
goto v___jp_1349_;
}
}
else
{
lean_object* v_a_1968_; 
v_a_1968_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_1968_);
lean_dec_ref(v___x_1954_);
v___y_1350_ = v___y_1933_;
v___y_1351_ = v___y_1932_;
v___y_1352_ = v___y_1935_;
v___y_1353_ = v___y_1936_;
v___y_1354_ = v___y_1938_;
v___y_1355_ = v___y_1937_;
v___y_1356_ = v___y_1939_;
v___y_1357_ = v___y_1940_;
v_a_1358_ = v_a_1968_;
goto v___jp_1349_;
}
}
else
{
lean_object* v_a_1969_; 
v_a_1969_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1969_);
lean_dec_ref(v___x_1952_);
v___y_1350_ = v___y_1933_;
v___y_1351_ = v___y_1932_;
v___y_1352_ = v___y_1935_;
v___y_1353_ = v___y_1936_;
v___y_1354_ = v___y_1938_;
v___y_1355_ = v___y_1937_;
v___y_1356_ = v___y_1939_;
v___y_1357_ = v___y_1940_;
v_a_1358_ = v_a_1969_;
goto v___jp_1349_;
}
}
else
{
lean_object* v_a_1970_; 
lean_dec_ref(v_binderType_1483_);
v_a_1970_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1970_);
lean_dec_ref(v___x_1950_);
v___y_1350_ = v___y_1933_;
v___y_1351_ = v___y_1932_;
v___y_1352_ = v___y_1935_;
v___y_1353_ = v___y_1936_;
v___y_1354_ = v___y_1938_;
v___y_1355_ = v___y_1937_;
v___y_1356_ = v___y_1939_;
v___y_1357_ = v___y_1940_;
v_a_1358_ = v_a_1970_;
goto v___jp_1349_;
}
}
else
{
lean_object* v_a_1971_; 
lean_dec(v_snd_1944_);
lean_dec_ref(v_binderType_1483_);
v_a_1971_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1971_);
lean_dec_ref(v___x_1948_);
v___y_1350_ = v___y_1933_;
v___y_1351_ = v___y_1932_;
v___y_1352_ = v___y_1935_;
v___y_1353_ = v___y_1936_;
v___y_1354_ = v___y_1938_;
v___y_1355_ = v___y_1937_;
v___y_1356_ = v___y_1939_;
v___y_1357_ = v___y_1940_;
v_a_1358_ = v_a_1971_;
goto v___jp_1349_;
}
}
else
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v_a_1974_; 
lean_dec(v_a_1946_);
lean_dec(v_snd_1944_);
lean_dec_ref(v_binderType_1483_);
v___x_1972_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1973_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1972_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_1974_);
lean_dec_ref(v___x_1973_);
v___y_1350_ = v___y_1933_;
v___y_1351_ = v___y_1932_;
v___y_1352_ = v___y_1935_;
v___y_1353_ = v___y_1936_;
v___y_1354_ = v___y_1938_;
v___y_1355_ = v___y_1937_;
v___y_1356_ = v___y_1939_;
v___y_1357_ = v___y_1940_;
v_a_1358_ = v_a_1974_;
goto v___jp_1349_;
}
}
else
{
lean_object* v_a_1975_; 
lean_dec(v_snd_1944_);
lean_dec_ref(v_binderType_1483_);
v_a_1975_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1975_);
lean_dec_ref(v___x_1945_);
v___y_1350_ = v___y_1933_;
v___y_1351_ = v___y_1932_;
v___y_1352_ = v___y_1935_;
v___y_1353_ = v___y_1936_;
v___y_1354_ = v___y_1938_;
v___y_1355_ = v___y_1937_;
v___y_1356_ = v___y_1939_;
v___y_1357_ = v___y_1940_;
v_a_1358_ = v_a_1975_;
goto v___jp_1349_;
}
}
else
{
lean_object* v___x_1976_; 
lean_dec_ref(v_binderType_1483_);
v___x_1976_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1942_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
lean_dec(v___x_1942_);
if (lean_obj_tag(v___x_1976_) == 0)
{
lean_object* v_a_1977_; 
lean_dec_ref(v_expr_1254_);
v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1977_);
lean_dec_ref(v___x_1976_);
v___y_1315_ = v___y_1932_;
v___y_1316_ = v___y_1933_;
v___y_1317_ = v___y_1935_;
v___y_1318_ = v___y_1936_;
v___y_1319_ = v___y_1937_;
v___y_1320_ = v___y_1938_;
v___y_1321_ = v___y_1939_;
v___y_1322_ = v___y_1940_;
v_a_1323_ = v_a_1977_;
goto v___jp_1314_;
}
else
{
lean_object* v_a_1978_; 
v_a_1978_ = lean_ctor_get(v___x_1976_, 0);
lean_inc(v_a_1978_);
lean_dec_ref(v___x_1976_);
v___y_1350_ = v___y_1933_;
v___y_1351_ = v___y_1932_;
v___y_1352_ = v___y_1935_;
v___y_1353_ = v___y_1936_;
v___y_1354_ = v___y_1938_;
v___y_1355_ = v___y_1937_;
v___y_1356_ = v___y_1939_;
v___y_1357_ = v___y_1940_;
v_a_1358_ = v_a_1978_;
goto v___jp_1349_;
}
}
}
else
{
lean_dec_ref(v_binderType_1483_);
lean_dec_ref(v_expr_1254_);
v___y_1326_ = v___y_1933_;
v___y_1327_ = v___y_1932_;
v___y_1328_ = v___y_1935_;
v___y_1329_ = v___y_1936_;
v___y_1330_ = v___y_1938_;
v___y_1331_ = v___y_1937_;
v___y_1332_ = v___y_1939_;
v___y_1333_ = v___y_1940_;
v_a_1334_ = v___y_1934_;
goto v___jp_1325_;
}
}
v___jp_1979_:
{
uint8_t v___x_1989_; 
v___x_1989_ = l_Lean_Exception_isInterrupt(v_a_1988_);
if (v___x_1989_ == 0)
{
uint8_t v___x_1990_; 
lean_inc_ref(v_a_1988_);
v___x_1990_ = l_Lean_Exception_isRuntime(v_a_1988_);
v___y_1932_ = v___y_1981_;
v___y_1933_ = v___y_1980_;
v___y_1934_ = v_a_1988_;
v___y_1935_ = v___y_1982_;
v___y_1936_ = v___y_1983_;
v___y_1937_ = v___y_1985_;
v___y_1938_ = v___y_1984_;
v___y_1939_ = v___y_1986_;
v___y_1940_ = v___y_1987_;
v___y_1941_ = v___x_1990_;
goto v___jp_1931_;
}
else
{
v___y_1932_ = v___y_1981_;
v___y_1933_ = v___y_1980_;
v___y_1934_ = v_a_1988_;
v___y_1935_ = v___y_1982_;
v___y_1936_ = v___y_1983_;
v___y_1937_ = v___y_1985_;
v___y_1938_ = v___y_1984_;
v___y_1939_ = v___y_1986_;
v___y_1940_ = v___y_1987_;
v___y_1941_ = v___x_1989_;
goto v___jp_1931_;
}
}
v___jp_1991_:
{
if (v___y_2001_ == 0)
{
lean_object* v___x_2002_; 
lean_dec_ref(v___y_1994_);
v___x_2002_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1467_);
if (lean_obj_tag(v___x_2002_) == 1)
{
lean_object* v_val_2003_; lean_object* v_snd_2004_; lean_object* v___x_2005_; 
v_val_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_val_2003_);
lean_dec_ref(v___x_2002_);
v_snd_2004_ = lean_ctor_get(v_val_2003_, 1);
lean_inc(v_snd_2004_);
lean_dec(v_val_2003_);
v___x_2005_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1469_, v_a_1258_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_a_2006_);
lean_dec_ref(v___x_2005_);
if (lean_obj_tag(v_a_2006_) == 1)
{
lean_object* v_val_2007_; lean_object* v___x_2008_; 
v_val_2007_ = lean_ctor_get(v_a_2006_, 0);
lean_inc(v_val_2007_);
lean_dec_ref(v_a_2006_);
lean_inc(v_a_1258_);
lean_inc_ref(v_a_1257_);
lean_inc(v_a_1256_);
lean_inc_ref(v_a_1255_);
v___x_2008_ = lean_infer_type(v_val_2007_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2010_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2009_);
lean_dec_ref(v___x_2008_);
v___x_2010_ = l_Lean_Meta_mkNumeral(v_a_2009_, v_snd_2004_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2012_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref(v___x_2010_);
lean_inc_ref(v_binderType_1483_);
v___x_2012_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2011_, v_binderType_1483_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2014_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref(v___x_2012_);
lean_inc_ref(v_arg_1467_);
v___x_2014_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1467_, v_a_2013_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref(v___x_2014_);
if (lean_obj_tag(v_a_2015_) == 1)
{
lean_object* v_val_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v_val_2016_ = lean_ctor_get(v_a_2015_, 0);
lean_inc(v_val_2016_);
lean_dec_ref(v_a_2015_);
lean_inc_ref(v_arg_1469_);
lean_inc_ref(v_fn_1468_);
v___x_2017_ = l_Lean_Expr_app___override(v_fn_1468_, v_arg_1469_);
v___x_2018_ = lean_box(0);
v___x_2019_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2019_, 0, v___x_2017_);
lean_ctor_set(v___x_2019_, 1, v___x_2018_);
lean_ctor_set_uint8(v___x_2019_, sizeof(void*)*2, v___y_1993_);
v___x_2020_ = l_Lean_Meta_Simp_mkCongr(v___x_2019_, v_val_2016_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_a_2021_; 
lean_dec_ref(v_binderType_1483_);
lean_dec_ref(v_expr_1254_);
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref(v___x_2020_);
v___y_1304_ = v___y_1993_;
v___y_1305_ = v___y_1992_;
v___y_1306_ = v___y_1995_;
v___y_1307_ = v___y_1996_;
v___y_1308_ = v___y_1998_;
v___y_1309_ = v___y_1997_;
v___y_1310_ = v___y_1999_;
v___y_1311_ = v___y_2000_;
v_a_1312_ = v_a_2021_;
goto v___jp_1303_;
}
else
{
lean_object* v_a_2022_; 
v_a_2022_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2022_);
lean_dec_ref(v___x_2020_);
v___y_1980_ = v___y_1993_;
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1995_;
v___y_1983_ = v___y_1996_;
v___y_1984_ = v___y_1998_;
v___y_1985_ = v___y_1997_;
v___y_1986_ = v___y_1999_;
v___y_1987_ = v___y_2000_;
v_a_1988_ = v_a_2022_;
goto v___jp_1979_;
}
}
else
{
lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v_a_2025_; 
lean_dec(v_a_2015_);
v___x_2023_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2024_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2023_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref(v___x_2024_);
v___y_1980_ = v___y_1993_;
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1995_;
v___y_1983_ = v___y_1996_;
v___y_1984_ = v___y_1998_;
v___y_1985_ = v___y_1997_;
v___y_1986_ = v___y_1999_;
v___y_1987_ = v___y_2000_;
v_a_1988_ = v_a_2025_;
goto v___jp_1979_;
}
}
else
{
lean_object* v_a_2026_; 
v_a_2026_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2026_);
lean_dec_ref(v___x_2014_);
v___y_1980_ = v___y_1993_;
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1995_;
v___y_1983_ = v___y_1996_;
v___y_1984_ = v___y_1998_;
v___y_1985_ = v___y_1997_;
v___y_1986_ = v___y_1999_;
v___y_1987_ = v___y_2000_;
v_a_1988_ = v_a_2026_;
goto v___jp_1979_;
}
}
else
{
lean_object* v_a_2027_; 
v_a_2027_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2027_);
lean_dec_ref(v___x_2012_);
v___y_1980_ = v___y_1993_;
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1995_;
v___y_1983_ = v___y_1996_;
v___y_1984_ = v___y_1998_;
v___y_1985_ = v___y_1997_;
v___y_1986_ = v___y_1999_;
v___y_1987_ = v___y_2000_;
v_a_1988_ = v_a_2027_;
goto v___jp_1979_;
}
}
else
{
lean_object* v_a_2028_; 
v_a_2028_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2028_);
lean_dec_ref(v___x_2010_);
v___y_1980_ = v___y_1993_;
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1995_;
v___y_1983_ = v___y_1996_;
v___y_1984_ = v___y_1998_;
v___y_1985_ = v___y_1997_;
v___y_1986_ = v___y_1999_;
v___y_1987_ = v___y_2000_;
v_a_1988_ = v_a_2028_;
goto v___jp_1979_;
}
}
else
{
lean_object* v_a_2029_; 
lean_dec(v_snd_2004_);
v_a_2029_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2029_);
lean_dec_ref(v___x_2008_);
v___y_1980_ = v___y_1993_;
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1995_;
v___y_1983_ = v___y_1996_;
v___y_1984_ = v___y_1998_;
v___y_1985_ = v___y_1997_;
v___y_1986_ = v___y_1999_;
v___y_1987_ = v___y_2000_;
v_a_1988_ = v_a_2029_;
goto v___jp_1979_;
}
}
else
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v_a_2032_; 
lean_dec(v_a_2006_);
lean_dec(v_snd_2004_);
v___x_2030_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2031_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2030_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2032_);
lean_dec_ref(v___x_2031_);
v___y_1980_ = v___y_1993_;
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1995_;
v___y_1983_ = v___y_1996_;
v___y_1984_ = v___y_1998_;
v___y_1985_ = v___y_1997_;
v___y_1986_ = v___y_1999_;
v___y_1987_ = v___y_2000_;
v_a_1988_ = v_a_2032_;
goto v___jp_1979_;
}
}
else
{
lean_object* v_a_2033_; 
lean_dec(v_snd_2004_);
v_a_2033_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_a_2033_);
lean_dec_ref(v___x_2005_);
v___y_1980_ = v___y_1993_;
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1995_;
v___y_1983_ = v___y_1996_;
v___y_1984_ = v___y_1998_;
v___y_1985_ = v___y_1997_;
v___y_1986_ = v___y_1999_;
v___y_1987_ = v___y_2000_;
v_a_1988_ = v_a_2033_;
goto v___jp_1979_;
}
}
else
{
lean_object* v___x_2034_; 
v___x_2034_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_2002_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
lean_dec(v___x_2002_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; 
lean_dec_ref(v_binderType_1483_);
lean_dec_ref(v_expr_1254_);
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref(v___x_2034_);
v___y_1315_ = v___y_1992_;
v___y_1316_ = v___y_1993_;
v___y_1317_ = v___y_1995_;
v___y_1318_ = v___y_1996_;
v___y_1319_ = v___y_1997_;
v___y_1320_ = v___y_1998_;
v___y_1321_ = v___y_1999_;
v___y_1322_ = v___y_2000_;
v_a_1323_ = v_a_2035_;
goto v___jp_1314_;
}
else
{
lean_object* v_a_2036_; 
v_a_2036_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2036_);
lean_dec_ref(v___x_2034_);
v___y_1980_ = v___y_1993_;
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1995_;
v___y_1983_ = v___y_1996_;
v___y_1984_ = v___y_1998_;
v___y_1985_ = v___y_1997_;
v___y_1986_ = v___y_1999_;
v___y_1987_ = v___y_2000_;
v_a_1988_ = v_a_2036_;
goto v___jp_1979_;
}
}
}
else
{
lean_dec_ref(v_binderType_1483_);
lean_dec_ref(v_expr_1254_);
v___y_1326_ = v___y_1993_;
v___y_1327_ = v___y_1992_;
v___y_1328_ = v___y_1995_;
v___y_1329_ = v___y_1996_;
v___y_1330_ = v___y_1998_;
v___y_1331_ = v___y_1997_;
v___y_1332_ = v___y_1999_;
v___y_1333_ = v___y_2000_;
v_a_1334_ = v___y_1994_;
goto v___jp_1325_;
}
}
v___jp_2037_:
{
uint8_t v___x_2047_; 
v___x_2047_ = l_Lean_Exception_isInterrupt(v_a_2046_);
if (v___x_2047_ == 0)
{
uint8_t v___x_2048_; 
lean_inc_ref(v_a_2046_);
v___x_2048_ = l_Lean_Exception_isRuntime(v_a_2046_);
v___y_1992_ = v___y_2039_;
v___y_1993_ = v___y_2038_;
v___y_1994_ = v_a_2046_;
v___y_1995_ = v___y_2040_;
v___y_1996_ = v___y_2041_;
v___y_1997_ = v___y_2043_;
v___y_1998_ = v___y_2042_;
v___y_1999_ = v___y_2044_;
v___y_2000_ = v___y_2045_;
v___y_2001_ = v___x_2048_;
goto v___jp_1991_;
}
else
{
v___y_1992_ = v___y_2039_;
v___y_1993_ = v___y_2038_;
v___y_1994_ = v_a_2046_;
v___y_1995_ = v___y_2040_;
v___y_1996_ = v___y_2041_;
v___y_1997_ = v___y_2043_;
v___y_1998_ = v___y_2042_;
v___y_1999_ = v___y_2044_;
v___y_2000_ = v___y_2045_;
v___y_2001_ = v___x_2047_;
goto v___jp_1991_;
}
}
v___jp_2049_:
{
if (lean_obj_tag(v___y_2058_) == 0)
{
lean_object* v_a_2059_; 
lean_dec_ref(v_binderType_1483_);
lean_dec_ref(v_expr_1254_);
v_a_2059_ = lean_ctor_get(v___y_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref(v___y_2058_);
v___y_1304_ = v___y_2051_;
v___y_1305_ = v___y_2050_;
v___y_1306_ = v___y_2052_;
v___y_1307_ = v___y_2053_;
v___y_1308_ = v___y_2055_;
v___y_1309_ = v___y_2054_;
v___y_1310_ = v___y_2056_;
v___y_1311_ = v___y_2057_;
v_a_1312_ = v_a_2059_;
goto v___jp_1303_;
}
else
{
lean_object* v_a_2060_; 
v_a_2060_ = lean_ctor_get(v___y_2058_, 0);
lean_inc(v_a_2060_);
lean_dec_ref(v___y_2058_);
v___y_2038_ = v___y_2051_;
v___y_2039_ = v___y_2050_;
v___y_2040_ = v___y_2052_;
v___y_2041_ = v___y_2053_;
v___y_2042_ = v___y_2055_;
v___y_2043_ = v___y_2054_;
v___y_2044_ = v___y_2056_;
v___y_2045_ = v___y_2057_;
v_a_2046_ = v_a_2060_;
goto v___jp_2037_;
}
}
v___jp_2061_:
{
if (v___y_2073_ == 0)
{
lean_object* v___x_2074_; 
lean_dec_ref(v___y_2070_);
v___x_2074_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v___y_2069_, v___y_2068_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; lean_object* v___x_2076_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2075_);
lean_dec_ref(v___x_2074_);
lean_inc_ref(v_binderType_1483_);
v___x_2076_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2075_, v_binderType_1483_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v___x_2078_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_a_2077_);
lean_dec_ref(v___x_2076_);
lean_inc_ref(v_arg_1467_);
v___x_2078_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1467_, v_a_2077_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2078_) == 0)
{
lean_object* v_a_2079_; 
v_a_2079_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2079_);
lean_dec_ref(v___x_2078_);
if (lean_obj_tag(v_a_2079_) == 1)
{
lean_object* v_val_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; 
v_val_2080_ = lean_ctor_get(v_a_2079_, 0);
lean_inc(v_val_2080_);
lean_dec_ref(v_a_2079_);
lean_inc_ref(v_arg_1469_);
lean_inc_ref(v_fn_1468_);
v___x_2081_ = l_Lean_Expr_app___override(v_fn_1468_, v_arg_1469_);
v___x_2082_ = lean_box(0);
v___x_2083_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2083_, 0, v___x_2081_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
lean_ctor_set_uint8(v___x_2083_, sizeof(void*)*2, v___y_2063_);
v___x_2084_ = l_Lean_Meta_Simp_mkCongr(v___x_2083_, v_val_2080_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v___y_2050_ = v___y_2062_;
v___y_2051_ = v___y_2063_;
v___y_2052_ = v___y_2064_;
v___y_2053_ = v___y_2065_;
v___y_2054_ = v___y_2067_;
v___y_2055_ = v___y_2066_;
v___y_2056_ = v___y_2071_;
v___y_2057_ = v___y_2072_;
v___y_2058_ = v___x_2084_;
goto v___jp_2049_;
}
else
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
lean_dec(v_a_2079_);
v___x_2085_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2086_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2085_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v___y_2050_ = v___y_2062_;
v___y_2051_ = v___y_2063_;
v___y_2052_ = v___y_2064_;
v___y_2053_ = v___y_2065_;
v___y_2054_ = v___y_2067_;
v___y_2055_ = v___y_2066_;
v___y_2056_ = v___y_2071_;
v___y_2057_ = v___y_2072_;
v___y_2058_ = v___x_2086_;
goto v___jp_2049_;
}
}
else
{
lean_object* v_a_2087_; 
v_a_2087_ = lean_ctor_get(v___x_2078_, 0);
lean_inc(v_a_2087_);
lean_dec_ref(v___x_2078_);
v___y_2038_ = v___y_2063_;
v___y_2039_ = v___y_2062_;
v___y_2040_ = v___y_2064_;
v___y_2041_ = v___y_2065_;
v___y_2042_ = v___y_2066_;
v___y_2043_ = v___y_2067_;
v___y_2044_ = v___y_2071_;
v___y_2045_ = v___y_2072_;
v_a_2046_ = v_a_2087_;
goto v___jp_2037_;
}
}
else
{
lean_object* v_a_2088_; 
v_a_2088_ = lean_ctor_get(v___x_2076_, 0);
lean_inc(v_a_2088_);
lean_dec_ref(v___x_2076_);
v___y_2038_ = v___y_2063_;
v___y_2039_ = v___y_2062_;
v___y_2040_ = v___y_2064_;
v___y_2041_ = v___y_2065_;
v___y_2042_ = v___y_2066_;
v___y_2043_ = v___y_2067_;
v___y_2044_ = v___y_2071_;
v___y_2045_ = v___y_2072_;
v_a_2046_ = v_a_2088_;
goto v___jp_2037_;
}
}
else
{
lean_object* v_a_2089_; 
v_a_2089_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2089_);
lean_dec_ref(v___x_2074_);
v___y_2038_ = v___y_2063_;
v___y_2039_ = v___y_2062_;
v___y_2040_ = v___y_2064_;
v___y_2041_ = v___y_2065_;
v___y_2042_ = v___y_2066_;
v___y_2043_ = v___y_2067_;
v___y_2044_ = v___y_2071_;
v___y_2045_ = v___y_2072_;
v_a_2046_ = v_a_2089_;
goto v___jp_2037_;
}
}
else
{
lean_dec_ref(v___y_2069_);
lean_dec_ref(v___y_2068_);
v___y_2038_ = v___y_2063_;
v___y_2039_ = v___y_2062_;
v___y_2040_ = v___y_2064_;
v___y_2041_ = v___y_2065_;
v___y_2042_ = v___y_2066_;
v___y_2043_ = v___y_2067_;
v___y_2044_ = v___y_2071_;
v___y_2045_ = v___y_2072_;
v_a_2046_ = v___y_2070_;
goto v___jp_2037_;
}
}
v___jp_2090_:
{
uint8_t v___x_2102_; 
v___x_2102_ = l_Lean_Exception_isInterrupt(v_a_2101_);
if (v___x_2102_ == 0)
{
uint8_t v___x_2103_; 
lean_inc_ref(v_a_2101_);
v___x_2103_ = l_Lean_Exception_isRuntime(v_a_2101_);
v___y_2062_ = v___y_2092_;
v___y_2063_ = v___y_2091_;
v___y_2064_ = v___y_2093_;
v___y_2065_ = v___y_2094_;
v___y_2066_ = v___y_2096_;
v___y_2067_ = v___y_2095_;
v___y_2068_ = v___y_2097_;
v___y_2069_ = v___y_2098_;
v___y_2070_ = v_a_2101_;
v___y_2071_ = v___y_2099_;
v___y_2072_ = v___y_2100_;
v___y_2073_ = v___x_2103_;
goto v___jp_2061_;
}
else
{
v___y_2062_ = v___y_2092_;
v___y_2063_ = v___y_2091_;
v___y_2064_ = v___y_2093_;
v___y_2065_ = v___y_2094_;
v___y_2066_ = v___y_2096_;
v___y_2067_ = v___y_2095_;
v___y_2068_ = v___y_2097_;
v___y_2069_ = v___y_2098_;
v___y_2070_ = v_a_2101_;
v___y_2071_ = v___y_2099_;
v___y_2072_ = v___y_2100_;
v___y_2073_ = v___x_2102_;
goto v___jp_2061_;
}
}
v___jp_2104_:
{
if (lean_obj_tag(v___y_2115_) == 0)
{
lean_object* v_a_2116_; 
lean_dec_ref(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec_ref(v_binderType_1483_);
lean_dec_ref(v_expr_1254_);
v_a_2116_ = lean_ctor_get(v___y_2115_, 0);
lean_inc(v_a_2116_);
lean_dec_ref(v___y_2115_);
v___y_1304_ = v___y_2106_;
v___y_1305_ = v___y_2105_;
v___y_1306_ = v___y_2107_;
v___y_1307_ = v___y_2108_;
v___y_1308_ = v___y_2110_;
v___y_1309_ = v___y_2109_;
v___y_1310_ = v___y_2113_;
v___y_1311_ = v___y_2114_;
v_a_1312_ = v_a_2116_;
goto v___jp_1303_;
}
else
{
lean_object* v_a_2117_; 
v_a_2117_ = lean_ctor_get(v___y_2115_, 0);
lean_inc(v_a_2117_);
lean_dec_ref(v___y_2115_);
v___y_2091_ = v___y_2106_;
v___y_2092_ = v___y_2105_;
v___y_2093_ = v___y_2107_;
v___y_2094_ = v___y_2108_;
v___y_2095_ = v___y_2109_;
v___y_2096_ = v___y_2110_;
v___y_2097_ = v___y_2111_;
v___y_2098_ = v___y_2112_;
v___y_2099_ = v___y_2113_;
v___y_2100_ = v___y_2114_;
v_a_2101_ = v_a_2117_;
goto v___jp_2090_;
}
}
v___jp_2118_:
{
lean_object* v___x_2125_; lean_object* v_a_2126_; lean_object* v___x_2127_; uint8_t v___x_2128_; 
v___x_2125_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v_a_1258_);
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref(v___x_2125_);
v___x_2127_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2128_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v___y_2120_, v___x_2127_);
if (v___x_2128_ == 0)
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = lean_io_mono_nanos_now();
v___x_2130_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1469_, v_a_1258_);
if (lean_obj_tag(v___x_2130_) == 0)
{
lean_object* v_a_2131_; 
v_a_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2131_);
lean_dec_ref(v___x_2130_);
if (lean_obj_tag(v_a_2131_) == 1)
{
lean_object* v_val_2132_; lean_object* v___x_2133_; 
v_val_2132_ = lean_ctor_get(v_a_2131_, 0);
lean_inc(v_val_2132_);
lean_dec_ref(v_a_2131_);
v___x_2133_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1467_, v_a_1258_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2134_);
lean_dec_ref(v___x_2133_);
if (lean_obj_tag(v_a_2134_) == 1)
{
lean_object* v_val_2135_; lean_object* v___x_2136_; 
v_val_2135_ = lean_ctor_get(v_a_2134_, 0);
lean_inc(v_val_2135_);
lean_dec_ref(v_a_2134_);
lean_inc(v_a_1258_);
lean_inc_ref(v_a_1257_);
lean_inc(v_a_1256_);
lean_inc_ref(v_a_1255_);
lean_inc(v_val_2132_);
v___x_2136_ = lean_infer_type(v_val_2132_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2138_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref(v___x_2136_);
lean_inc(v_a_1258_);
lean_inc_ref(v_a_1257_);
lean_inc(v_a_1256_);
lean_inc_ref(v_a_1255_);
lean_inc(v_val_2135_);
v___x_2138_ = lean_infer_type(v_val_2135_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2140_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref(v___x_2138_);
v___x_2140_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_val_2132_, v_a_2139_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v___x_2142_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref(v___x_2140_);
lean_inc_ref(v_binderType_1483_);
v___x_2142_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2141_, v_binderType_1483_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v_a_2143_; lean_object* v___x_2144_; 
v_a_2143_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref(v___x_2142_);
lean_inc_ref(v_arg_1469_);
v___x_2144_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1469_, v_a_2143_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v_a_2145_; 
v_a_2145_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2145_);
lean_dec_ref(v___x_2144_);
if (lean_obj_tag(v_a_2145_) == 1)
{
lean_object* v_val_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
v_val_2146_ = lean_ctor_get(v_a_2145_, 0);
lean_inc(v_val_2146_);
lean_dec_ref(v_a_2145_);
v___x_2147_ = lean_box(0);
lean_inc_ref(v_fn_1468_);
v___x_2148_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2148_, 0, v_fn_1468_);
lean_ctor_set(v___x_2148_, 1, v___x_2147_);
lean_ctor_set_uint8(v___x_2148_, sizeof(void*)*2, v___y_2119_);
v___x_2149_ = l_Lean_Meta_Simp_mkCongr(v___x_2148_, v_val_2146_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2151_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref(v___x_2149_);
lean_inc_ref(v_arg_1467_);
v___x_2151_ = l_Lean_Meta_Simp_mkCongrFun(v_a_2150_, v_arg_1467_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v___y_1918_ = v_a_2126_;
v___y_1919_ = v___y_2119_;
v___y_1920_ = v___y_2120_;
v___y_1921_ = v___y_2122_;
v___y_1922_ = v___y_2121_;
v___y_1923_ = v___x_2129_;
v___y_1924_ = v_a_2137_;
v___y_1925_ = v___y_2123_;
v___y_1926_ = v_val_2135_;
v___y_1927_ = v___y_2124_;
v___y_1928_ = v___x_2151_;
goto v___jp_1917_;
}
else
{
v___y_1918_ = v_a_2126_;
v___y_1919_ = v___y_2119_;
v___y_1920_ = v___y_2120_;
v___y_1921_ = v___y_2122_;
v___y_1922_ = v___y_2121_;
v___y_1923_ = v___x_2129_;
v___y_1924_ = v_a_2137_;
v___y_1925_ = v___y_2123_;
v___y_1926_ = v_val_2135_;
v___y_1927_ = v___y_2124_;
v___y_1928_ = v___x_2149_;
goto v___jp_1917_;
}
}
else
{
lean_object* v___x_2152_; lean_object* v___x_2153_; 
lean_dec(v_a_2145_);
v___x_2152_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2153_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2152_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v___y_1918_ = v_a_2126_;
v___y_1919_ = v___y_2119_;
v___y_1920_ = v___y_2120_;
v___y_1921_ = v___y_2122_;
v___y_1922_ = v___y_2121_;
v___y_1923_ = v___x_2129_;
v___y_1924_ = v_a_2137_;
v___y_1925_ = v___y_2123_;
v___y_1926_ = v_val_2135_;
v___y_1927_ = v___y_2124_;
v___y_1928_ = v___x_2153_;
goto v___jp_1917_;
}
}
else
{
lean_object* v_a_2154_; 
v_a_2154_ = lean_ctor_get(v___x_2144_, 0);
lean_inc(v_a_2154_);
lean_dec_ref(v___x_2144_);
v___y_1904_ = v___y_2119_;
v___y_1905_ = v_a_2126_;
v___y_1906_ = v___y_2120_;
v___y_1907_ = v___y_2122_;
v___y_1908_ = v___y_2121_;
v___y_1909_ = v___x_2129_;
v___y_1910_ = v_a_2137_;
v___y_1911_ = v___y_2123_;
v___y_1912_ = v_val_2135_;
v___y_1913_ = v___y_2124_;
v_a_1914_ = v_a_2154_;
goto v___jp_1903_;
}
}
else
{
lean_object* v_a_2155_; 
v_a_2155_ = lean_ctor_get(v___x_2142_, 0);
lean_inc(v_a_2155_);
lean_dec_ref(v___x_2142_);
v___y_1904_ = v___y_2119_;
v___y_1905_ = v_a_2126_;
v___y_1906_ = v___y_2120_;
v___y_1907_ = v___y_2122_;
v___y_1908_ = v___y_2121_;
v___y_1909_ = v___x_2129_;
v___y_1910_ = v_a_2137_;
v___y_1911_ = v___y_2123_;
v___y_1912_ = v_val_2135_;
v___y_1913_ = v___y_2124_;
v_a_1914_ = v_a_2155_;
goto v___jp_1903_;
}
}
else
{
lean_object* v_a_2156_; 
v_a_2156_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2156_);
lean_dec_ref(v___x_2140_);
v___y_1904_ = v___y_2119_;
v___y_1905_ = v_a_2126_;
v___y_1906_ = v___y_2120_;
v___y_1907_ = v___y_2122_;
v___y_1908_ = v___y_2121_;
v___y_1909_ = v___x_2129_;
v___y_1910_ = v_a_2137_;
v___y_1911_ = v___y_2123_;
v___y_1912_ = v_val_2135_;
v___y_1913_ = v___y_2124_;
v_a_1914_ = v_a_2156_;
goto v___jp_1903_;
}
}
else
{
lean_object* v_a_2157_; 
lean_dec(v_a_2137_);
lean_dec(v_val_2135_);
lean_dec(v_val_2132_);
v_a_2157_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2157_);
lean_dec_ref(v___x_2138_);
v___y_1851_ = v___y_2119_;
v___y_1852_ = v_a_2126_;
v___y_1853_ = v___y_2120_;
v___y_1854_ = v___y_2121_;
v___y_1855_ = v___y_2122_;
v___y_1856_ = v___x_2129_;
v___y_1857_ = v___y_2123_;
v___y_1858_ = v___y_2124_;
v_a_1859_ = v_a_2157_;
goto v___jp_1850_;
}
}
else
{
lean_object* v_a_2158_; 
lean_dec(v_val_2135_);
lean_dec(v_val_2132_);
v_a_2158_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2158_);
lean_dec_ref(v___x_2136_);
v___y_1851_ = v___y_2119_;
v___y_1852_ = v_a_2126_;
v___y_1853_ = v___y_2120_;
v___y_1854_ = v___y_2121_;
v___y_1855_ = v___y_2122_;
v___y_1856_ = v___x_2129_;
v___y_1857_ = v___y_2123_;
v___y_1858_ = v___y_2124_;
v_a_1859_ = v_a_2158_;
goto v___jp_1850_;
}
}
else
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v_a_2161_; 
lean_dec(v_a_2134_);
lean_dec(v_val_2132_);
v___x_2159_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2160_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2159_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2161_);
lean_dec_ref(v___x_2160_);
v___y_1851_ = v___y_2119_;
v___y_1852_ = v_a_2126_;
v___y_1853_ = v___y_2120_;
v___y_1854_ = v___y_2121_;
v___y_1855_ = v___y_2122_;
v___y_1856_ = v___x_2129_;
v___y_1857_ = v___y_2123_;
v___y_1858_ = v___y_2124_;
v_a_1859_ = v_a_2161_;
goto v___jp_1850_;
}
}
else
{
lean_object* v_a_2162_; 
lean_dec(v_val_2132_);
v_a_2162_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2162_);
lean_dec_ref(v___x_2133_);
v___y_1851_ = v___y_2119_;
v___y_1852_ = v_a_2126_;
v___y_1853_ = v___y_2120_;
v___y_1854_ = v___y_2121_;
v___y_1855_ = v___y_2122_;
v___y_1856_ = v___x_2129_;
v___y_1857_ = v___y_2123_;
v___y_1858_ = v___y_2124_;
v_a_1859_ = v_a_2162_;
goto v___jp_1850_;
}
}
else
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v_a_2165_; 
lean_dec(v_a_2131_);
v___x_2163_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2164_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2163_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2165_);
lean_dec_ref(v___x_2164_);
v___y_1851_ = v___y_2119_;
v___y_1852_ = v_a_2126_;
v___y_1853_ = v___y_2120_;
v___y_1854_ = v___y_2121_;
v___y_1855_ = v___y_2122_;
v___y_1856_ = v___x_2129_;
v___y_1857_ = v___y_2123_;
v___y_1858_ = v___y_2124_;
v_a_1859_ = v_a_2165_;
goto v___jp_1850_;
}
}
else
{
lean_object* v_a_2166_; 
v_a_2166_ = lean_ctor_get(v___x_2130_, 0);
lean_inc(v_a_2166_);
lean_dec_ref(v___x_2130_);
v___y_1851_ = v___y_2119_;
v___y_1852_ = v_a_2126_;
v___y_1853_ = v___y_2120_;
v___y_1854_ = v___y_2121_;
v___y_1855_ = v___y_2122_;
v___y_1856_ = v___x_2129_;
v___y_1857_ = v___y_2123_;
v___y_1858_ = v___y_2124_;
v_a_1859_ = v_a_2166_;
goto v___jp_1850_;
}
}
else
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2167_ = lean_io_get_num_heartbeats();
v___x_2168_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1469_, v_a_1258_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v_a_2169_; 
v_a_2169_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2169_);
lean_dec_ref(v___x_2168_);
if (lean_obj_tag(v_a_2169_) == 1)
{
lean_object* v_val_2170_; lean_object* v___x_2171_; 
v_val_2170_ = lean_ctor_get(v_a_2169_, 0);
lean_inc(v_val_2170_);
lean_dec_ref(v_a_2169_);
v___x_2171_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1467_, v_a_1258_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2172_);
lean_dec_ref(v___x_2171_);
if (lean_obj_tag(v_a_2172_) == 1)
{
lean_object* v_val_2173_; lean_object* v___x_2174_; 
v_val_2173_ = lean_ctor_get(v_a_2172_, 0);
lean_inc(v_val_2173_);
lean_dec_ref(v_a_2172_);
lean_inc(v_a_1258_);
lean_inc_ref(v_a_1257_);
lean_inc(v_a_1256_);
lean_inc_ref(v_a_1255_);
lean_inc(v_val_2170_);
v___x_2174_ = lean_infer_type(v_val_2170_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2176_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref(v___x_2174_);
lean_inc(v_a_1258_);
lean_inc_ref(v_a_1257_);
lean_inc(v_a_1256_);
lean_inc_ref(v_a_1255_);
lean_inc(v_val_2173_);
v___x_2176_ = lean_infer_type(v_val_2173_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___x_2178_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref(v___x_2176_);
v___x_2178_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_val_2170_, v_a_2177_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2180_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2179_);
lean_dec_ref(v___x_2178_);
lean_inc_ref(v_binderType_1483_);
v___x_2180_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2179_, v_binderType_1483_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_object* v_a_2181_; lean_object* v___x_2182_; 
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2181_);
lean_dec_ref(v___x_2180_);
lean_inc_ref(v_arg_1469_);
v___x_2182_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1469_, v_a_2181_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2182_) == 0)
{
lean_object* v_a_2183_; 
v_a_2183_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2183_);
lean_dec_ref(v___x_2182_);
if (lean_obj_tag(v_a_2183_) == 1)
{
lean_object* v_val_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v_val_2184_ = lean_ctor_get(v_a_2183_, 0);
lean_inc(v_val_2184_);
lean_dec_ref(v_a_2183_);
v___x_2185_ = lean_box(0);
lean_inc_ref(v_fn_1468_);
v___x_2186_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2186_, 0, v_fn_1468_);
lean_ctor_set(v___x_2186_, 1, v___x_2185_);
lean_ctor_set_uint8(v___x_2186_, sizeof(void*)*2, v___y_2119_);
v___x_2187_ = l_Lean_Meta_Simp_mkCongr(v___x_2186_, v_val_2184_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; lean_object* v___x_2189_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
lean_inc(v_a_2188_);
lean_dec_ref(v___x_2187_);
lean_inc_ref(v_arg_1467_);
v___x_2189_ = l_Lean_Meta_Simp_mkCongrFun(v_a_2188_, v_arg_1467_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v___y_2105_ = v_a_2126_;
v___y_2106_ = v___y_2119_;
v___y_2107_ = v___y_2120_;
v___y_2108_ = v___x_2167_;
v___y_2109_ = v___y_2122_;
v___y_2110_ = v___y_2121_;
v___y_2111_ = v_a_2175_;
v___y_2112_ = v_val_2173_;
v___y_2113_ = v___y_2123_;
v___y_2114_ = v___y_2124_;
v___y_2115_ = v___x_2189_;
goto v___jp_2104_;
}
else
{
v___y_2105_ = v_a_2126_;
v___y_2106_ = v___y_2119_;
v___y_2107_ = v___y_2120_;
v___y_2108_ = v___x_2167_;
v___y_2109_ = v___y_2122_;
v___y_2110_ = v___y_2121_;
v___y_2111_ = v_a_2175_;
v___y_2112_ = v_val_2173_;
v___y_2113_ = v___y_2123_;
v___y_2114_ = v___y_2124_;
v___y_2115_ = v___x_2187_;
goto v___jp_2104_;
}
}
else
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_dec(v_a_2183_);
v___x_2190_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2191_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2190_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v___y_2105_ = v_a_2126_;
v___y_2106_ = v___y_2119_;
v___y_2107_ = v___y_2120_;
v___y_2108_ = v___x_2167_;
v___y_2109_ = v___y_2122_;
v___y_2110_ = v___y_2121_;
v___y_2111_ = v_a_2175_;
v___y_2112_ = v_val_2173_;
v___y_2113_ = v___y_2123_;
v___y_2114_ = v___y_2124_;
v___y_2115_ = v___x_2191_;
goto v___jp_2104_;
}
}
else
{
lean_object* v_a_2192_; 
v_a_2192_ = lean_ctor_get(v___x_2182_, 0);
lean_inc(v_a_2192_);
lean_dec_ref(v___x_2182_);
v___y_2091_ = v___y_2119_;
v___y_2092_ = v_a_2126_;
v___y_2093_ = v___y_2120_;
v___y_2094_ = v___x_2167_;
v___y_2095_ = v___y_2122_;
v___y_2096_ = v___y_2121_;
v___y_2097_ = v_a_2175_;
v___y_2098_ = v_val_2173_;
v___y_2099_ = v___y_2123_;
v___y_2100_ = v___y_2124_;
v_a_2101_ = v_a_2192_;
goto v___jp_2090_;
}
}
else
{
lean_object* v_a_2193_; 
v_a_2193_ = lean_ctor_get(v___x_2180_, 0);
lean_inc(v_a_2193_);
lean_dec_ref(v___x_2180_);
v___y_2091_ = v___y_2119_;
v___y_2092_ = v_a_2126_;
v___y_2093_ = v___y_2120_;
v___y_2094_ = v___x_2167_;
v___y_2095_ = v___y_2122_;
v___y_2096_ = v___y_2121_;
v___y_2097_ = v_a_2175_;
v___y_2098_ = v_val_2173_;
v___y_2099_ = v___y_2123_;
v___y_2100_ = v___y_2124_;
v_a_2101_ = v_a_2193_;
goto v___jp_2090_;
}
}
else
{
lean_object* v_a_2194_; 
v_a_2194_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2194_);
lean_dec_ref(v___x_2178_);
v___y_2091_ = v___y_2119_;
v___y_2092_ = v_a_2126_;
v___y_2093_ = v___y_2120_;
v___y_2094_ = v___x_2167_;
v___y_2095_ = v___y_2122_;
v___y_2096_ = v___y_2121_;
v___y_2097_ = v_a_2175_;
v___y_2098_ = v_val_2173_;
v___y_2099_ = v___y_2123_;
v___y_2100_ = v___y_2124_;
v_a_2101_ = v_a_2194_;
goto v___jp_2090_;
}
}
else
{
lean_object* v_a_2195_; 
lean_dec(v_a_2175_);
lean_dec(v_val_2173_);
lean_dec(v_val_2170_);
v_a_2195_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2195_);
lean_dec_ref(v___x_2176_);
v___y_2038_ = v___y_2119_;
v___y_2039_ = v_a_2126_;
v___y_2040_ = v___y_2120_;
v___y_2041_ = v___x_2167_;
v___y_2042_ = v___y_2121_;
v___y_2043_ = v___y_2122_;
v___y_2044_ = v___y_2123_;
v___y_2045_ = v___y_2124_;
v_a_2046_ = v_a_2195_;
goto v___jp_2037_;
}
}
else
{
lean_object* v_a_2196_; 
lean_dec(v_val_2173_);
lean_dec(v_val_2170_);
v_a_2196_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2196_);
lean_dec_ref(v___x_2174_);
v___y_2038_ = v___y_2119_;
v___y_2039_ = v_a_2126_;
v___y_2040_ = v___y_2120_;
v___y_2041_ = v___x_2167_;
v___y_2042_ = v___y_2121_;
v___y_2043_ = v___y_2122_;
v___y_2044_ = v___y_2123_;
v___y_2045_ = v___y_2124_;
v_a_2046_ = v_a_2196_;
goto v___jp_2037_;
}
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v_a_2199_; 
lean_dec(v_a_2172_);
lean_dec(v_val_2170_);
v___x_2197_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2198_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2197_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref(v___x_2198_);
v___y_2038_ = v___y_2119_;
v___y_2039_ = v_a_2126_;
v___y_2040_ = v___y_2120_;
v___y_2041_ = v___x_2167_;
v___y_2042_ = v___y_2121_;
v___y_2043_ = v___y_2122_;
v___y_2044_ = v___y_2123_;
v___y_2045_ = v___y_2124_;
v_a_2046_ = v_a_2199_;
goto v___jp_2037_;
}
}
else
{
lean_object* v_a_2200_; 
lean_dec(v_val_2170_);
v_a_2200_ = lean_ctor_get(v___x_2171_, 0);
lean_inc(v_a_2200_);
lean_dec_ref(v___x_2171_);
v___y_2038_ = v___y_2119_;
v___y_2039_ = v_a_2126_;
v___y_2040_ = v___y_2120_;
v___y_2041_ = v___x_2167_;
v___y_2042_ = v___y_2121_;
v___y_2043_ = v___y_2122_;
v___y_2044_ = v___y_2123_;
v___y_2045_ = v___y_2124_;
v_a_2046_ = v_a_2200_;
goto v___jp_2037_;
}
}
else
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v_a_2203_; 
lean_dec(v_a_2169_);
v___x_2201_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2202_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2201_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref(v___x_2202_);
v___y_2038_ = v___y_2119_;
v___y_2039_ = v_a_2126_;
v___y_2040_ = v___y_2120_;
v___y_2041_ = v___x_2167_;
v___y_2042_ = v___y_2121_;
v___y_2043_ = v___y_2122_;
v___y_2044_ = v___y_2123_;
v___y_2045_ = v___y_2124_;
v_a_2046_ = v_a_2203_;
goto v___jp_2037_;
}
}
else
{
lean_object* v_a_2204_; 
v_a_2204_ = lean_ctor_get(v___x_2168_, 0);
lean_inc(v_a_2204_);
lean_dec_ref(v___x_2168_);
v___y_2038_ = v___y_2119_;
v___y_2039_ = v_a_2126_;
v___y_2040_ = v___y_2120_;
v___y_2041_ = v___x_2167_;
v___y_2042_ = v___y_2121_;
v___y_2043_ = v___y_2122_;
v___y_2044_ = v___y_2123_;
v___y_2045_ = v___y_2124_;
v_a_2046_ = v_a_2204_;
goto v___jp_2037_;
}
}
}
v___jp_2205_:
{
uint8_t v___x_2207_; 
v___x_2207_ = 1;
if (v___y_2206_ == 0)
{
lean_object* v___x_2208_; 
lean_inc_ref(v_binderType_1483_);
v___x_2208_ = l_Lean_Meta_isExprDefEq(v_binderType_1483_, v_binderType_1484_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2208_) == 0)
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2306_; 
v_a_2209_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2211_ = v___x_2208_;
v_isShared_2212_ = v_isSharedCheck_2306_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___x_2208_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2306_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
uint8_t v___x_2213_; 
v___x_2213_ = lean_unbox(v_a_2209_);
lean_dec(v_a_2209_);
if (v___x_2213_ == 0)
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2217_; 
lean_dec_ref(v_binderType_1483_);
v___x_2214_ = lean_box(0);
v___x_2215_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2215_, 0, v_expr_1254_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
lean_ctor_set_uint8(v___x_2215_, sizeof(void*)*2, v___x_2207_);
if (v_isShared_2212_ == 0)
{
lean_ctor_set(v___x_2211_, 0, v___x_2215_);
v___x_2217_ = v___x_2211_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
else
{
lean_object* v_options_2219_; uint8_t v_hasTrace_2220_; 
lean_del_object(v___x_2211_);
v_options_2219_ = lean_ctor_get(v_a_1257_, 2);
v_hasTrace_2220_ = lean_ctor_get_uint8(v_options_2219_, sizeof(void*)*1);
if (v_hasTrace_2220_ == 0)
{
lean_object* v___x_2221_; 
v___x_2221_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1469_, v_a_1258_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2222_);
lean_dec_ref(v___x_2221_);
if (lean_obj_tag(v_a_2222_) == 1)
{
lean_object* v_val_2223_; lean_object* v___x_2224_; 
v_val_2223_ = lean_ctor_get(v_a_2222_, 0);
lean_inc(v_val_2223_);
lean_dec_ref(v_a_2222_);
v___x_2224_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1467_, v_a_1258_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
lean_dec_ref(v___x_2224_);
if (lean_obj_tag(v_a_2225_) == 1)
{
lean_object* v_val_2226_; lean_object* v___x_2227_; 
v_val_2226_ = lean_ctor_get(v_a_2225_, 0);
lean_inc(v_val_2226_);
lean_dec_ref(v_a_2225_);
lean_inc(v_a_1258_);
lean_inc_ref(v_a_1257_);
lean_inc(v_a_1256_);
lean_inc_ref(v_a_1255_);
lean_inc(v_val_2223_);
v___x_2227_ = lean_infer_type(v_val_2223_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v___x_2229_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2228_);
lean_dec_ref(v___x_2227_);
lean_inc(v_a_1258_);
lean_inc_ref(v_a_1257_);
lean_inc(v_a_1256_);
lean_inc_ref(v_a_1255_);
lean_inc(v_val_2226_);
v___x_2229_ = lean_infer_type(v_val_2226_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2231_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2230_);
lean_dec_ref(v___x_2229_);
v___x_2231_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_val_2223_, v_a_2230_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; lean_object* v___x_2233_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2232_);
lean_dec_ref(v___x_2231_);
lean_inc_ref(v_binderType_1483_);
v___x_2233_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2232_, v_binderType_1483_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2235_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_a_2234_);
lean_dec_ref(v___x_2233_);
lean_inc_ref(v_arg_1469_);
v___x_2235_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1469_, v_a_2234_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref(v___x_2235_);
if (lean_obj_tag(v_a_2236_) == 1)
{
lean_object* v_val_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v_val_2237_ = lean_ctor_get(v_a_2236_, 0);
lean_inc(v_val_2237_);
lean_dec_ref(v_a_2236_);
v___x_2238_ = lean_box(0);
lean_inc_ref(v_fn_1468_);
v___x_2239_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2239_, 0, v_fn_1468_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
lean_ctor_set_uint8(v___x_2239_, sizeof(void*)*2, v___x_2207_);
v___x_2240_ = l_Lean_Meta_Simp_mkCongr(v___x_2239_, v_val_2237_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v___x_2242_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_a_2241_);
lean_dec_ref(v___x_2240_);
lean_inc_ref(v_arg_1467_);
v___x_2242_ = l_Lean_Meta_Simp_mkCongrFun(v_a_2241_, v_arg_1467_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v___y_1610_ = v___x_2207_;
v___y_1611_ = v_a_2228_;
v___y_1612_ = v_val_2226_;
v___y_1613_ = v___x_2242_;
goto v___jp_1609_;
}
else
{
v___y_1610_ = v___x_2207_;
v___y_1611_ = v_a_2228_;
v___y_1612_ = v_val_2226_;
v___y_1613_ = v___x_2240_;
goto v___jp_1609_;
}
}
else
{
lean_object* v___x_2243_; lean_object* v___x_2244_; 
lean_dec(v_a_2236_);
v___x_2243_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2244_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2243_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v___y_1610_ = v___x_2207_;
v___y_1611_ = v_a_2228_;
v___y_1612_ = v_val_2226_;
v___y_1613_ = v___x_2244_;
goto v___jp_1609_;
}
}
else
{
lean_object* v_a_2245_; 
v_a_2245_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2245_);
lean_dec_ref(v___x_2235_);
v___y_1603_ = v___x_2207_;
v___y_1604_ = v_val_2226_;
v___y_1605_ = v_a_2228_;
v_a_1606_ = v_a_2245_;
goto v___jp_1602_;
}
}
else
{
lean_object* v_a_2246_; 
v_a_2246_ = lean_ctor_get(v___x_2233_, 0);
lean_inc(v_a_2246_);
lean_dec_ref(v___x_2233_);
v___y_1603_ = v___x_2207_;
v___y_1604_ = v_val_2226_;
v___y_1605_ = v_a_2228_;
v_a_1606_ = v_a_2246_;
goto v___jp_1602_;
}
}
else
{
lean_object* v_a_2247_; 
v_a_2247_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2247_);
lean_dec_ref(v___x_2231_);
v___y_1603_ = v___x_2207_;
v___y_1604_ = v_val_2226_;
v___y_1605_ = v_a_2228_;
v_a_1606_ = v_a_2247_;
goto v___jp_1602_;
}
}
else
{
lean_object* v_a_2248_; 
lean_dec(v_a_2228_);
lean_dec(v_val_2226_);
lean_dec(v_val_2223_);
v_a_2248_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2248_);
lean_dec_ref(v___x_2229_);
v___y_1572_ = v___x_2207_;
v_a_1573_ = v_a_2248_;
goto v___jp_1571_;
}
}
else
{
lean_object* v_a_2249_; 
lean_dec(v_val_2226_);
lean_dec(v_val_2223_);
v_a_2249_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2249_);
lean_dec_ref(v___x_2227_);
v___y_1572_ = v___x_2207_;
v_a_1573_ = v_a_2249_;
goto v___jp_1571_;
}
}
else
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v_a_2252_; 
lean_dec(v_a_2225_);
lean_dec(v_val_2223_);
v___x_2250_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2251_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2250_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_a_2252_);
lean_dec_ref(v___x_2251_);
v___y_1572_ = v___x_2207_;
v_a_1573_ = v_a_2252_;
goto v___jp_1571_;
}
}
else
{
lean_object* v_a_2253_; 
lean_dec(v_val_2223_);
v_a_2253_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2253_);
lean_dec_ref(v___x_2224_);
v___y_1572_ = v___x_2207_;
v_a_1573_ = v_a_2253_;
goto v___jp_1571_;
}
}
else
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v_a_2256_; 
lean_dec(v_a_2222_);
v___x_2254_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2255_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v_a_2256_ = lean_ctor_get(v___x_2255_, 0);
lean_inc(v_a_2256_);
lean_dec_ref(v___x_2255_);
v___y_1572_ = v___x_2207_;
v_a_1573_ = v_a_2256_;
goto v___jp_1571_;
}
}
else
{
lean_object* v_a_2257_; 
v_a_2257_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2257_);
lean_dec_ref(v___x_2221_);
v___y_1572_ = v___x_2207_;
v_a_1573_ = v_a_2257_;
goto v___jp_1571_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___f_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; uint8_t v___x_2266_; 
v_inheritedTraceOptions_2258_ = lean_ctor_get(v_a_1257_, 13);
v___x_2259_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_splittingProcedure___closed__1, &l_Lean_Elab_Tactic_NormCast_splittingProcedure___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___closed__1);
lean_inc_ref_n(v_expr_1254_, 2);
v___x_2260_ = l_Lean_MessageData_ofExpr(v_expr_1254_);
v___x_2261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2259_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
v___f_2262_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___boxed), 8, 2);
lean_closure_set(v___f_2262_, 0, v___x_2261_);
lean_closure_set(v___f_2262_, 1, v_expr_1254_);
v___x_2263_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__2_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_));
v___x_2264_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_2265_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3);
v___x_2266_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2258_, v_options_2219_, v___x_2265_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2267_; uint8_t v___x_2268_; 
v___x_2267_ = l_Lean_trace_profiler;
v___x_2268_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_2219_, v___x_2267_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; 
lean_dec_ref(v___f_2262_);
v___x_2269_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1469_, v_a_1258_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_a_2270_);
lean_dec_ref(v___x_2269_);
if (lean_obj_tag(v_a_2270_) == 1)
{
lean_object* v_val_2271_; lean_object* v___x_2272_; 
v_val_2271_ = lean_ctor_get(v_a_2270_, 0);
lean_inc(v_val_2271_);
lean_dec_ref(v_a_2270_);
v___x_2272_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1467_, v_a_1258_);
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
lean_inc(v_a_1258_);
lean_inc_ref(v_a_1257_);
lean_inc(v_a_1256_);
lean_inc_ref(v_a_1255_);
lean_inc(v_val_2271_);
v___x_2275_ = lean_infer_type(v_val_2271_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; lean_object* v___x_2277_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2276_);
lean_dec_ref(v___x_2275_);
lean_inc(v_a_1258_);
lean_inc_ref(v_a_1257_);
lean_inc(v_a_1256_);
lean_inc_ref(v_a_1255_);
lean_inc(v_val_2274_);
v___x_2277_ = lean_infer_type(v_val_2274_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2278_; lean_object* v___x_2279_; 
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_a_2278_);
lean_dec_ref(v___x_2277_);
v___x_2279_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_val_2271_, v_a_2278_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2281_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref(v___x_2279_);
lean_inc_ref(v_binderType_1483_);
v___x_2281_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2280_, v_binderType_1483_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; lean_object* v___x_2283_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
lean_dec_ref(v___x_2281_);
lean_inc_ref(v_arg_1469_);
v___x_2283_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1469_, v_a_2282_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_a_2284_);
lean_dec_ref(v___x_2283_);
if (lean_obj_tag(v_a_2284_) == 1)
{
lean_object* v_val_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v_val_2285_ = lean_ctor_get(v_a_2284_, 0);
lean_inc(v_val_2285_);
lean_dec_ref(v_a_2284_);
v___x_2286_ = lean_box(0);
lean_inc_ref(v_fn_1468_);
v___x_2287_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2287_, 0, v_fn_1468_);
lean_ctor_set(v___x_2287_, 1, v___x_2286_);
lean_ctor_set_uint8(v___x_2287_, sizeof(void*)*2, v___x_2207_);
v___x_2288_ = l_Lean_Meta_Simp_mkCongr(v___x_2287_, v_val_2285_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
if (lean_obj_tag(v___x_2288_) == 0)
{
lean_object* v_a_2289_; lean_object* v___x_2290_; 
v_a_2289_ = lean_ctor_get(v___x_2288_, 0);
lean_inc(v_a_2289_);
lean_dec_ref(v___x_2288_);
lean_inc_ref(v_arg_1467_);
v___x_2290_ = l_Lean_Meta_Simp_mkCongrFun(v_a_2289_, v_arg_1467_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v___y_1739_ = v___x_2207_;
v___y_1740_ = v_val_2274_;
v___y_1741_ = v_a_2276_;
v___y_1742_ = v___x_2290_;
goto v___jp_1738_;
}
else
{
v___y_1739_ = v___x_2207_;
v___y_1740_ = v_val_2274_;
v___y_1741_ = v_a_2276_;
v___y_1742_ = v___x_2288_;
goto v___jp_1738_;
}
}
else
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
lean_dec(v_a_2284_);
v___x_2291_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2292_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2291_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v___y_1739_ = v___x_2207_;
v___y_1740_ = v_val_2274_;
v___y_1741_ = v_a_2276_;
v___y_1742_ = v___x_2292_;
goto v___jp_1738_;
}
}
else
{
lean_object* v_a_2293_; 
v_a_2293_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_a_2293_);
lean_dec_ref(v___x_2283_);
v___y_1732_ = v___x_2207_;
v___y_1733_ = v_val_2274_;
v___y_1734_ = v_a_2276_;
v_a_1735_ = v_a_2293_;
goto v___jp_1731_;
}
}
else
{
lean_object* v_a_2294_; 
v_a_2294_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2294_);
lean_dec_ref(v___x_2281_);
v___y_1732_ = v___x_2207_;
v___y_1733_ = v_val_2274_;
v___y_1734_ = v_a_2276_;
v_a_1735_ = v_a_2294_;
goto v___jp_1731_;
}
}
else
{
lean_object* v_a_2295_; 
v_a_2295_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2295_);
lean_dec_ref(v___x_2279_);
v___y_1732_ = v___x_2207_;
v___y_1733_ = v_val_2274_;
v___y_1734_ = v_a_2276_;
v_a_1735_ = v_a_2295_;
goto v___jp_1731_;
}
}
else
{
lean_object* v_a_2296_; 
lean_dec(v_a_2276_);
lean_dec(v_val_2274_);
lean_dec(v_val_2271_);
v_a_2296_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_a_2296_);
lean_dec_ref(v___x_2277_);
v___y_1701_ = v___x_2207_;
v_a_1702_ = v_a_2296_;
goto v___jp_1700_;
}
}
else
{
lean_object* v_a_2297_; 
lean_dec(v_val_2274_);
lean_dec(v_val_2271_);
v_a_2297_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2297_);
lean_dec_ref(v___x_2275_);
v___y_1701_ = v___x_2207_;
v_a_1702_ = v_a_2297_;
goto v___jp_1700_;
}
}
else
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v_a_2300_; 
lean_dec(v_a_2273_);
lean_dec(v_val_2271_);
v___x_2298_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2299_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2298_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref(v___x_2299_);
v___y_1701_ = v___x_2207_;
v_a_1702_ = v_a_2300_;
goto v___jp_1700_;
}
}
else
{
lean_object* v_a_2301_; 
lean_dec(v_val_2271_);
v_a_2301_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_a_2301_);
lean_dec_ref(v___x_2272_);
v___y_1701_ = v___x_2207_;
v_a_1702_ = v_a_2301_;
goto v___jp_1700_;
}
}
else
{
lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v_a_2304_; 
lean_dec(v_a_2270_);
v___x_2302_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2303_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2302_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref(v___x_2303_);
v___y_1701_ = v___x_2207_;
v_a_1702_ = v_a_2304_;
goto v___jp_1700_;
}
}
else
{
lean_object* v_a_2305_; 
v_a_2305_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_a_2305_);
lean_dec_ref(v___x_2269_);
v___y_1701_ = v___x_2207_;
v_a_1702_ = v_a_2305_;
goto v___jp_1700_;
}
}
else
{
v___y_2119_ = v___x_2207_;
v___y_2120_ = v_options_2219_;
v___y_2121_ = v___x_2264_;
v___y_2122_ = v___x_2266_;
v___y_2123_ = v___x_2263_;
v___y_2124_ = v___f_2262_;
goto v___jp_2118_;
}
}
else
{
v___y_2119_ = v___x_2207_;
v___y_2120_ = v_options_2219_;
v___y_2121_ = v___x_2264_;
v___y_2122_ = v___x_2266_;
v___y_2123_ = v___x_2263_;
v___y_2124_ = v___f_2262_;
goto v___jp_2118_;
}
}
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_dec_ref(v_binderType_1483_);
lean_dec_ref(v_expr_1254_);
v_a_2307_ = lean_ctor_get(v___x_2208_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2208_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2208_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
else
{
lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
lean_dec_ref(v_binderType_1484_);
lean_dec_ref(v_binderType_1483_);
v___x_2315_ = lean_box(0);
v___x_2316_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2316_, 0, v_expr_1254_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
lean_ctor_set_uint8(v___x_2316_, sizeof(void*)*2, v___x_2207_);
v___x_2317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2316_);
return v___x_2317_;
}
}
}
else
{
lean_dec_ref(v_a_1471_);
lean_dec_ref(v_body_1482_);
goto v___jp_1475_;
}
}
else
{
lean_dec(v_a_1471_);
goto v___jp_1475_;
}
v___jp_1475_:
{
lean_object* v___x_1476_; uint8_t v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; 
v___x_1476_ = lean_box(0);
v___x_1477_ = 1;
v___x_1478_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1478_, 0, v_expr_1254_);
lean_ctor_set(v___x_1478_, 1, v___x_1476_);
lean_ctor_set_uint8(v___x_1478_, sizeof(void*)*2, v___x_1477_);
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 0, v___x_1478_);
v___x_1480_ = v___x_1473_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1478_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2328_; 
lean_dec_ref(v_expr_1254_);
v_a_2321_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_2328_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2323_ = v___x_1470_;
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_1470_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2328_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2326_; 
if (v_isShared_2324_ == 0)
{
v___x_2326_ = v___x_2323_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
v___x_2326_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
return v___x_2326_;
}
}
}
}
else
{
goto v___jp_1260_;
}
}
else
{
goto v___jp_1260_;
}
v___jp_1260_:
{
lean_object* v___x_1261_; uint8_t v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1261_ = lean_box(0);
v___x_1262_ = 1;
v___x_1263_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1263_, 0, v_expr_1254_);
lean_ctor_set(v___x_1263_, 1, v___x_1261_);
lean_ctor_set_uint8(v___x_1263_, sizeof(void*)*2, v___x_1262_);
v___x_1264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
return v___x_1264_;
}
v___jp_1265_:
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1274_; 
v_a_1267_ = lean_ctor_get(v_a_1266_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_a_1266_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1269_ = v_a_1266_;
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v_a_1266_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1274_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1272_; 
if (v_isShared_1270_ == 0)
{
lean_ctor_set_tag(v___x_1269_, 0);
v___x_1272_ = v___x_1269_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1267_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
v___jp_1275_:
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
v_a_1277_ = lean_ctor_get(v_a_1276_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v_a_1276_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v_a_1276_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v_a_1276_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
lean_ctor_set_tag(v___x_1279_, 0);
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
v___jp_1285_:
{
lean_object* v___x_1295_; double v___x_1296_; double v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1295_ = lean_io_get_num_heartbeats();
v___x_1296_ = lean_float_of_nat(v___y_1289_);
v___x_1297_ = lean_float_of_nat(v___x_1295_);
v___x_1298_ = lean_box_float(v___x_1296_);
v___x_1299_ = lean_box_float(v___x_1297_);
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1298_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
v___x_1301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1301_, 0, v_a_1294_);
lean_ctor_set(v___x_1301_, 1, v___x_1300_);
lean_inc_ref(v___y_1291_);
lean_inc(v___y_1292_);
v___x_1302_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___y_1292_, v___y_1287_, v___y_1291_, v___y_1288_, v___y_1290_, v___y_1286_, v___y_1293_, v___x_1301_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
return v___x_1302_;
}
v___jp_1303_:
{
lean_object* v___x_1313_; 
v___x_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1313_, 0, v_a_1312_);
v___y_1286_ = v___y_1305_;
v___y_1287_ = v___y_1304_;
v___y_1288_ = v___y_1306_;
v___y_1289_ = v___y_1307_;
v___y_1290_ = v___y_1309_;
v___y_1291_ = v___y_1308_;
v___y_1292_ = v___y_1310_;
v___y_1293_ = v___y_1311_;
v_a_1294_ = v___x_1313_;
goto v___jp_1285_;
}
v___jp_1314_:
{
lean_object* v_a_1324_; 
v_a_1324_ = lean_ctor_get(v_a_1323_, 0);
lean_inc(v_a_1324_);
lean_dec_ref(v_a_1323_);
v___y_1304_ = v___y_1316_;
v___y_1305_ = v___y_1315_;
v___y_1306_ = v___y_1317_;
v___y_1307_ = v___y_1318_;
v___y_1308_ = v___y_1320_;
v___y_1309_ = v___y_1319_;
v___y_1310_ = v___y_1321_;
v___y_1311_ = v___y_1322_;
v_a_1312_ = v_a_1324_;
goto v___jp_1303_;
}
v___jp_1325_:
{
lean_object* v___x_1335_; 
v___x_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1335_, 0, v_a_1334_);
v___y_1286_ = v___y_1327_;
v___y_1287_ = v___y_1326_;
v___y_1288_ = v___y_1328_;
v___y_1289_ = v___y_1329_;
v___y_1290_ = v___y_1331_;
v___y_1291_ = v___y_1330_;
v___y_1292_ = v___y_1332_;
v___y_1293_ = v___y_1333_;
v_a_1294_ = v___x_1335_;
goto v___jp_1285_;
}
v___jp_1336_:
{
if (v___y_1346_ == 0)
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
lean_dec_ref(v___y_1341_);
v___x_1347_ = lean_box(0);
v___x_1348_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1348_, 0, v_expr_1254_);
lean_ctor_set(v___x_1348_, 1, v___x_1347_);
lean_ctor_set_uint8(v___x_1348_, sizeof(void*)*2, v___y_1338_);
v___y_1304_ = v___y_1338_;
v___y_1305_ = v___y_1337_;
v___y_1306_ = v___y_1339_;
v___y_1307_ = v___y_1340_;
v___y_1308_ = v___y_1343_;
v___y_1309_ = v___y_1342_;
v___y_1310_ = v___y_1344_;
v___y_1311_ = v___y_1345_;
v_a_1312_ = v___x_1348_;
goto v___jp_1303_;
}
else
{
lean_dec_ref(v_expr_1254_);
v___y_1326_ = v___y_1338_;
v___y_1327_ = v___y_1337_;
v___y_1328_ = v___y_1339_;
v___y_1329_ = v___y_1340_;
v___y_1330_ = v___y_1343_;
v___y_1331_ = v___y_1342_;
v___y_1332_ = v___y_1344_;
v___y_1333_ = v___y_1345_;
v_a_1334_ = v___y_1341_;
goto v___jp_1325_;
}
}
v___jp_1349_:
{
uint8_t v___x_1359_; 
v___x_1359_ = l_Lean_Exception_isInterrupt(v_a_1358_);
if (v___x_1359_ == 0)
{
uint8_t v___x_1360_; 
lean_inc_ref(v_a_1358_);
v___x_1360_ = l_Lean_Exception_isRuntime(v_a_1358_);
v___y_1337_ = v___y_1351_;
v___y_1338_ = v___y_1350_;
v___y_1339_ = v___y_1352_;
v___y_1340_ = v___y_1353_;
v___y_1341_ = v_a_1358_;
v___y_1342_ = v___y_1355_;
v___y_1343_ = v___y_1354_;
v___y_1344_ = v___y_1356_;
v___y_1345_ = v___y_1357_;
v___y_1346_ = v___x_1360_;
goto v___jp_1336_;
}
else
{
v___y_1337_ = v___y_1351_;
v___y_1338_ = v___y_1350_;
v___y_1339_ = v___y_1352_;
v___y_1340_ = v___y_1353_;
v___y_1341_ = v_a_1358_;
v___y_1342_ = v___y_1355_;
v___y_1343_ = v___y_1354_;
v___y_1344_ = v___y_1356_;
v___y_1345_ = v___y_1357_;
v___y_1346_ = v___x_1359_;
goto v___jp_1336_;
}
}
v___jp_1361_:
{
lean_object* v___x_1371_; double v___x_1372_; double v___x_1373_; double v___x_1374_; double v___x_1375_; double v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1371_ = lean_io_mono_nanos_now();
v___x_1372_ = lean_float_of_nat(v___y_1367_);
v___x_1373_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4);
v___x_1374_ = lean_float_div(v___x_1372_, v___x_1373_);
v___x_1375_ = lean_float_of_nat(v___x_1371_);
v___x_1376_ = lean_float_div(v___x_1375_, v___x_1373_);
v___x_1377_ = lean_box_float(v___x_1374_);
v___x_1378_ = lean_box_float(v___x_1376_);
v___x_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1377_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
v___x_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1380_, 0, v_a_1370_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
lean_inc_ref(v___y_1366_);
lean_inc(v___y_1368_);
v___x_1381_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___y_1368_, v___y_1363_, v___y_1366_, v___y_1364_, v___y_1365_, v___y_1362_, v___y_1369_, v___x_1380_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
return v___x_1381_;
}
v___jp_1382_:
{
lean_object* v___x_1392_; 
v___x_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1392_, 0, v_a_1391_);
v___y_1362_ = v___y_1384_;
v___y_1363_ = v___y_1383_;
v___y_1364_ = v___y_1385_;
v___y_1365_ = v___y_1387_;
v___y_1366_ = v___y_1386_;
v___y_1367_ = v___y_1388_;
v___y_1368_ = v___y_1389_;
v___y_1369_ = v___y_1390_;
v_a_1370_ = v___x_1392_;
goto v___jp_1361_;
}
v___jp_1393_:
{
lean_object* v_a_1403_; 
v_a_1403_ = lean_ctor_get(v_a_1402_, 0);
lean_inc(v_a_1403_);
lean_dec_ref(v_a_1402_);
v___y_1383_ = v___y_1395_;
v___y_1384_ = v___y_1394_;
v___y_1385_ = v___y_1396_;
v___y_1386_ = v___y_1398_;
v___y_1387_ = v___y_1397_;
v___y_1388_ = v___y_1399_;
v___y_1389_ = v___y_1400_;
v___y_1390_ = v___y_1401_;
v_a_1391_ = v_a_1403_;
goto v___jp_1382_;
}
v___jp_1404_:
{
lean_object* v___x_1414_; 
v___x_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1414_, 0, v_a_1413_);
v___y_1362_ = v___y_1406_;
v___y_1363_ = v___y_1405_;
v___y_1364_ = v___y_1407_;
v___y_1365_ = v___y_1409_;
v___y_1366_ = v___y_1408_;
v___y_1367_ = v___y_1410_;
v___y_1368_ = v___y_1411_;
v___y_1369_ = v___y_1412_;
v_a_1370_ = v___x_1414_;
goto v___jp_1361_;
}
v___jp_1415_:
{
if (v___y_1425_ == 0)
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_dec_ref(v___y_1416_);
v___x_1426_ = lean_box(0);
v___x_1427_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1427_, 0, v_expr_1254_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
lean_ctor_set_uint8(v___x_1427_, sizeof(void*)*2, v___y_1418_);
v___y_1383_ = v___y_1418_;
v___y_1384_ = v___y_1417_;
v___y_1385_ = v___y_1419_;
v___y_1386_ = v___y_1421_;
v___y_1387_ = v___y_1420_;
v___y_1388_ = v___y_1422_;
v___y_1389_ = v___y_1423_;
v___y_1390_ = v___y_1424_;
v_a_1391_ = v___x_1427_;
goto v___jp_1382_;
}
else
{
lean_dec_ref(v_expr_1254_);
v___y_1405_ = v___y_1418_;
v___y_1406_ = v___y_1417_;
v___y_1407_ = v___y_1419_;
v___y_1408_ = v___y_1421_;
v___y_1409_ = v___y_1420_;
v___y_1410_ = v___y_1422_;
v___y_1411_ = v___y_1423_;
v___y_1412_ = v___y_1424_;
v_a_1413_ = v___y_1416_;
goto v___jp_1404_;
}
}
v___jp_1428_:
{
uint8_t v___x_1438_; 
v___x_1438_ = l_Lean_Exception_isInterrupt(v_a_1437_);
if (v___x_1438_ == 0)
{
uint8_t v___x_1439_; 
lean_inc_ref(v_a_1437_);
v___x_1439_ = l_Lean_Exception_isRuntime(v_a_1437_);
v___y_1416_ = v_a_1437_;
v___y_1417_ = v___y_1430_;
v___y_1418_ = v___y_1429_;
v___y_1419_ = v___y_1431_;
v___y_1420_ = v___y_1433_;
v___y_1421_ = v___y_1432_;
v___y_1422_ = v___y_1434_;
v___y_1423_ = v___y_1435_;
v___y_1424_ = v___y_1436_;
v___y_1425_ = v___x_1439_;
goto v___jp_1415_;
}
else
{
v___y_1416_ = v_a_1437_;
v___y_1417_ = v___y_1430_;
v___y_1418_ = v___y_1429_;
v___y_1419_ = v___y_1431_;
v___y_1420_ = v___y_1433_;
v___y_1421_ = v___y_1432_;
v___y_1422_ = v___y_1434_;
v___y_1423_ = v___y_1435_;
v___y_1424_ = v___y_1436_;
v___y_1425_ = v___x_1438_;
goto v___jp_1415_;
}
}
v___jp_1440_:
{
if (v___y_1443_ == 0)
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
lean_dec_ref(v___y_1442_);
v___x_1444_ = lean_box(0);
v___x_1445_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1445_, 0, v_expr_1254_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
lean_ctor_set_uint8(v___x_1445_, sizeof(void*)*2, v___y_1441_);
v___x_1446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
return v___x_1446_;
}
else
{
lean_object* v___x_1447_; 
lean_dec_ref(v_expr_1254_);
v___x_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1447_, 0, v___y_1442_);
return v___x_1447_;
}
}
v___jp_1448_:
{
uint8_t v___x_1451_; 
v___x_1451_ = l_Lean_Exception_isInterrupt(v_a_1450_);
if (v___x_1451_ == 0)
{
uint8_t v___x_1452_; 
lean_inc_ref(v_a_1450_);
v___x_1452_ = l_Lean_Exception_isRuntime(v_a_1450_);
v___y_1441_ = v___y_1449_;
v___y_1442_ = v_a_1450_;
v___y_1443_ = v___x_1452_;
goto v___jp_1440_;
}
else
{
v___y_1441_ = v___y_1449_;
v___y_1442_ = v_a_1450_;
v___y_1443_ = v___x_1451_;
goto v___jp_1440_;
}
}
v___jp_1453_:
{
if (v___y_1456_ == 0)
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
lean_dec_ref(v___y_1455_);
v___x_1457_ = lean_box(0);
v___x_1458_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1458_, 0, v_expr_1254_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
lean_ctor_set_uint8(v___x_1458_, sizeof(void*)*2, v___y_1454_);
v___x_1459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1458_);
return v___x_1459_;
}
else
{
lean_object* v___x_1460_; 
lean_dec_ref(v_expr_1254_);
v___x_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___y_1455_);
return v___x_1460_;
}
}
v___jp_1461_:
{
uint8_t v___x_1464_; 
v___x_1464_ = l_Lean_Exception_isInterrupt(v_a_1463_);
if (v___x_1464_ == 0)
{
uint8_t v___x_1465_; 
lean_inc_ref(v_a_1463_);
v___x_1465_ = l_Lean_Exception_isRuntime(v_a_1463_);
v___y_1454_ = v___y_1462_;
v___y_1455_ = v_a_1463_;
v___y_1456_ = v___x_1465_;
goto v___jp_1453_;
}
else
{
v___y_1454_ = v___y_1462_;
v___y_1455_ = v_a_1463_;
v___y_1456_ = v___x_1464_;
goto v___jp_1453_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___boxed(lean_object* v_expr_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_){
_start:
{
lean_object* v_res_2335_; 
v_res_2335_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure(v_expr_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_);
lean_dec(v_a_2333_);
lean_dec_ref(v_a_2332_);
lean_dec(v_a_2331_);
lean_dec_ref(v_a_2330_);
return v_res_2335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___redArg(lean_object* v___y_2336_){
_start:
{
lean_object* v___x_2338_; lean_object* v_traceState_2339_; lean_object* v_traces_2340_; lean_object* v___x_2341_; lean_object* v_traceState_2342_; lean_object* v_env_2343_; lean_object* v_nextMacroScope_2344_; lean_object* v_ngen_2345_; lean_object* v_auxDeclNGen_2346_; lean_object* v_cache_2347_; lean_object* v_messages_2348_; lean_object* v_infoState_2349_; lean_object* v_snapshotTasks_2350_; lean_object* v_newDecls_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2372_; 
v___x_2338_ = lean_st_ref_get(v___y_2336_);
v_traceState_2339_ = lean_ctor_get(v___x_2338_, 4);
lean_inc_ref(v_traceState_2339_);
lean_dec(v___x_2338_);
v_traces_2340_ = lean_ctor_get(v_traceState_2339_, 0);
lean_inc_ref(v_traces_2340_);
lean_dec_ref(v_traceState_2339_);
v___x_2341_ = lean_st_ref_take(v___y_2336_);
v_traceState_2342_ = lean_ctor_get(v___x_2341_, 4);
v_env_2343_ = lean_ctor_get(v___x_2341_, 0);
v_nextMacroScope_2344_ = lean_ctor_get(v___x_2341_, 1);
v_ngen_2345_ = lean_ctor_get(v___x_2341_, 2);
v_auxDeclNGen_2346_ = lean_ctor_get(v___x_2341_, 3);
v_cache_2347_ = lean_ctor_get(v___x_2341_, 5);
v_messages_2348_ = lean_ctor_get(v___x_2341_, 6);
v_infoState_2349_ = lean_ctor_get(v___x_2341_, 7);
v_snapshotTasks_2350_ = lean_ctor_get(v___x_2341_, 8);
v_newDecls_2351_ = lean_ctor_get(v___x_2341_, 9);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2353_ = v___x_2341_;
v_isShared_2354_ = v_isSharedCheck_2372_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_newDecls_2351_);
lean_inc(v_snapshotTasks_2350_);
lean_inc(v_infoState_2349_);
lean_inc(v_messages_2348_);
lean_inc(v_cache_2347_);
lean_inc(v_traceState_2342_);
lean_inc(v_auxDeclNGen_2346_);
lean_inc(v_ngen_2345_);
lean_inc(v_nextMacroScope_2344_);
lean_inc(v_env_2343_);
lean_dec(v___x_2341_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2372_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
uint64_t v_tid_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2370_; 
v_tid_2355_ = lean_ctor_get_uint64(v_traceState_2342_, sizeof(void*)*1);
v_isSharedCheck_2370_ = !lean_is_exclusive(v_traceState_2342_);
if (v_isSharedCheck_2370_ == 0)
{
lean_object* v_unused_2371_; 
v_unused_2371_ = lean_ctor_get(v_traceState_2342_, 0);
lean_dec(v_unused_2371_);
v___x_2357_ = v_traceState_2342_;
v_isShared_2358_ = v_isSharedCheck_2370_;
goto v_resetjp_2356_;
}
else
{
lean_dec(v_traceState_2342_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2370_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2363_; 
v___x_2359_ = lean_unsigned_to_nat(32u);
v___x_2360_ = lean_mk_empty_array_with_capacity(v___x_2359_);
lean_dec_ref(v___x_2360_);
v___x_2361_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__1);
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 0, v___x_2361_);
v___x_2363_ = v___x_2357_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2361_);
lean_ctor_set_uint64(v_reuseFailAlloc_2369_, sizeof(void*)*1, v_tid_2355_);
v___x_2363_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
lean_object* v___x_2365_; 
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 4, v___x_2363_);
v___x_2365_ = v___x_2353_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_env_2343_);
lean_ctor_set(v_reuseFailAlloc_2368_, 1, v_nextMacroScope_2344_);
lean_ctor_set(v_reuseFailAlloc_2368_, 2, v_ngen_2345_);
lean_ctor_set(v_reuseFailAlloc_2368_, 3, v_auxDeclNGen_2346_);
lean_ctor_set(v_reuseFailAlloc_2368_, 4, v___x_2363_);
lean_ctor_set(v_reuseFailAlloc_2368_, 5, v_cache_2347_);
lean_ctor_set(v_reuseFailAlloc_2368_, 6, v_messages_2348_);
lean_ctor_set(v_reuseFailAlloc_2368_, 7, v_infoState_2349_);
lean_ctor_set(v_reuseFailAlloc_2368_, 8, v_snapshotTasks_2350_);
lean_ctor_set(v_reuseFailAlloc_2368_, 9, v_newDecls_2351_);
v___x_2365_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2366_ = lean_st_ref_set(v___y_2336_, v___x_2365_);
v___x_2367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2367_, 0, v_traces_2340_);
return v___x_2367_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___redArg___boxed(lean_object* v___y_2373_, lean_object* v___y_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___redArg(v___y_2373_);
lean_dec(v___y_2373_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__0(lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v___x_2384_; 
v___x_2384_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___redArg(v___y_2382_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___boxed(lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__0(v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v___y_2385_);
return v_res_2393_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__0));
v___x_2396_ = l_Lean_stringToMessageData(v___x_2395_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lam__0(lean_object* v_e_2397_, lean_object* v_x_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2407_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__1, &l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__1);
v___x_2408_ = l_Lean_MessageData_ofExpr(v_e_2397_);
v___x_2409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2407_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
v___x_2410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
return v___x_2410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lam__0___boxed(lean_object* v_e_2411_, lean_object* v_x_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l_Lean_Elab_Tactic_NormCast_prove___lam__0(v_e_2411_, v_x_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec(v___y_2413_);
lean_dec_ref(v_x_2412_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__2___redArg(lean_object* v_oldTraces_2422_, lean_object* v_data_2423_, lean_object* v_ref_2424_, lean_object* v_msg_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v_fileName_2431_; lean_object* v_fileMap_2432_; lean_object* v_options_2433_; lean_object* v_currRecDepth_2434_; lean_object* v_maxRecDepth_2435_; lean_object* v_ref_2436_; lean_object* v_currNamespace_2437_; lean_object* v_openDecls_2438_; lean_object* v_initHeartbeats_2439_; lean_object* v_maxHeartbeats_2440_; lean_object* v_quotContext_2441_; lean_object* v_currMacroScope_2442_; uint8_t v_diag_2443_; lean_object* v_cancelTk_x3f_2444_; uint8_t v_suppressElabErrors_2445_; lean_object* v_inheritedTraceOptions_2446_; lean_object* v___x_2447_; lean_object* v_traceState_2448_; lean_object* v_traces_2449_; lean_object* v_ref_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; size_t v_sz_2453_; size_t v___x_2454_; lean_object* v___x_2455_; lean_object* v_msg_2456_; lean_object* v___x_2457_; lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2496_; 
v_fileName_2431_ = lean_ctor_get(v___y_2428_, 0);
v_fileMap_2432_ = lean_ctor_get(v___y_2428_, 1);
v_options_2433_ = lean_ctor_get(v___y_2428_, 2);
v_currRecDepth_2434_ = lean_ctor_get(v___y_2428_, 3);
v_maxRecDepth_2435_ = lean_ctor_get(v___y_2428_, 4);
v_ref_2436_ = lean_ctor_get(v___y_2428_, 5);
v_currNamespace_2437_ = lean_ctor_get(v___y_2428_, 6);
v_openDecls_2438_ = lean_ctor_get(v___y_2428_, 7);
v_initHeartbeats_2439_ = lean_ctor_get(v___y_2428_, 8);
v_maxHeartbeats_2440_ = lean_ctor_get(v___y_2428_, 9);
v_quotContext_2441_ = lean_ctor_get(v___y_2428_, 10);
v_currMacroScope_2442_ = lean_ctor_get(v___y_2428_, 11);
v_diag_2443_ = lean_ctor_get_uint8(v___y_2428_, sizeof(void*)*14);
v_cancelTk_x3f_2444_ = lean_ctor_get(v___y_2428_, 12);
v_suppressElabErrors_2445_ = lean_ctor_get_uint8(v___y_2428_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2446_ = lean_ctor_get(v___y_2428_, 13);
v___x_2447_ = lean_st_ref_get(v___y_2429_);
v_traceState_2448_ = lean_ctor_get(v___x_2447_, 4);
lean_inc_ref(v_traceState_2448_);
lean_dec(v___x_2447_);
v_traces_2449_ = lean_ctor_get(v_traceState_2448_, 0);
lean_inc_ref(v_traces_2449_);
lean_dec_ref(v_traceState_2448_);
v_ref_2450_ = l_Lean_replaceRef(v_ref_2424_, v_ref_2436_);
lean_inc_ref(v_inheritedTraceOptions_2446_);
lean_inc(v_cancelTk_x3f_2444_);
lean_inc(v_currMacroScope_2442_);
lean_inc(v_quotContext_2441_);
lean_inc(v_maxHeartbeats_2440_);
lean_inc(v_initHeartbeats_2439_);
lean_inc(v_openDecls_2438_);
lean_inc(v_currNamespace_2437_);
lean_inc(v_maxRecDepth_2435_);
lean_inc(v_currRecDepth_2434_);
lean_inc_ref(v_options_2433_);
lean_inc_ref(v_fileMap_2432_);
lean_inc_ref(v_fileName_2431_);
v___x_2451_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2451_, 0, v_fileName_2431_);
lean_ctor_set(v___x_2451_, 1, v_fileMap_2432_);
lean_ctor_set(v___x_2451_, 2, v_options_2433_);
lean_ctor_set(v___x_2451_, 3, v_currRecDepth_2434_);
lean_ctor_set(v___x_2451_, 4, v_maxRecDepth_2435_);
lean_ctor_set(v___x_2451_, 5, v_ref_2450_);
lean_ctor_set(v___x_2451_, 6, v_currNamespace_2437_);
lean_ctor_set(v___x_2451_, 7, v_openDecls_2438_);
lean_ctor_set(v___x_2451_, 8, v_initHeartbeats_2439_);
lean_ctor_set(v___x_2451_, 9, v_maxHeartbeats_2440_);
lean_ctor_set(v___x_2451_, 10, v_quotContext_2441_);
lean_ctor_set(v___x_2451_, 11, v_currMacroScope_2442_);
lean_ctor_set(v___x_2451_, 12, v_cancelTk_x3f_2444_);
lean_ctor_set(v___x_2451_, 13, v_inheritedTraceOptions_2446_);
lean_ctor_set_uint8(v___x_2451_, sizeof(void*)*14, v_diag_2443_);
lean_ctor_set_uint8(v___x_2451_, sizeof(void*)*14 + 1, v_suppressElabErrors_2445_);
v___x_2452_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2449_);
lean_dec_ref(v_traces_2449_);
v_sz_2453_ = lean_array_size(v___x_2452_);
v___x_2454_ = ((size_t)0ULL);
v___x_2455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__4(v_sz_2453_, v___x_2454_, v___x_2452_);
v_msg_2456_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2456_, 0, v_data_2423_);
lean_ctor_set(v_msg_2456_, 1, v_msg_2425_);
lean_ctor_set(v_msg_2456_, 2, v___x_2455_);
v___x_2457_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__5(v_msg_2456_, v___y_2426_, v___y_2427_, v___x_2451_, v___y_2429_);
lean_dec_ref(v___x_2451_);
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2460_ = v___x_2457_;
v_isShared_2461_ = v_isSharedCheck_2496_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2457_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2496_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2462_; lean_object* v_traceState_2463_; lean_object* v_env_2464_; lean_object* v_nextMacroScope_2465_; lean_object* v_ngen_2466_; lean_object* v_auxDeclNGen_2467_; lean_object* v_cache_2468_; lean_object* v_messages_2469_; lean_object* v_infoState_2470_; lean_object* v_snapshotTasks_2471_; lean_object* v_newDecls_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2495_; 
v___x_2462_ = lean_st_ref_take(v___y_2429_);
v_traceState_2463_ = lean_ctor_get(v___x_2462_, 4);
v_env_2464_ = lean_ctor_get(v___x_2462_, 0);
v_nextMacroScope_2465_ = lean_ctor_get(v___x_2462_, 1);
v_ngen_2466_ = lean_ctor_get(v___x_2462_, 2);
v_auxDeclNGen_2467_ = lean_ctor_get(v___x_2462_, 3);
v_cache_2468_ = lean_ctor_get(v___x_2462_, 5);
v_messages_2469_ = lean_ctor_get(v___x_2462_, 6);
v_infoState_2470_ = lean_ctor_get(v___x_2462_, 7);
v_snapshotTasks_2471_ = lean_ctor_get(v___x_2462_, 8);
v_newDecls_2472_ = lean_ctor_get(v___x_2462_, 9);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2474_ = v___x_2462_;
v_isShared_2475_ = v_isSharedCheck_2495_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_newDecls_2472_);
lean_inc(v_snapshotTasks_2471_);
lean_inc(v_infoState_2470_);
lean_inc(v_messages_2469_);
lean_inc(v_cache_2468_);
lean_inc(v_traceState_2463_);
lean_inc(v_auxDeclNGen_2467_);
lean_inc(v_ngen_2466_);
lean_inc(v_nextMacroScope_2465_);
lean_inc(v_env_2464_);
lean_dec(v___x_2462_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2495_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
uint64_t v_tid_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2493_; 
v_tid_2476_ = lean_ctor_get_uint64(v_traceState_2463_, sizeof(void*)*1);
v_isSharedCheck_2493_ = !lean_is_exclusive(v_traceState_2463_);
if (v_isSharedCheck_2493_ == 0)
{
lean_object* v_unused_2494_; 
v_unused_2494_ = lean_ctor_get(v_traceState_2463_, 0);
lean_dec(v_unused_2494_);
v___x_2478_ = v_traceState_2463_;
v_isShared_2479_ = v_isSharedCheck_2493_;
goto v_resetjp_2477_;
}
else
{
lean_dec(v_traceState_2463_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2493_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2483_; 
v___x_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2480_, 0, v_ref_2424_);
lean_ctor_set(v___x_2480_, 1, v_a_2458_);
v___x_2481_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2422_, v___x_2480_);
if (v_isShared_2479_ == 0)
{
lean_ctor_set(v___x_2478_, 0, v___x_2481_);
v___x_2483_ = v___x_2478_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2481_);
lean_ctor_set_uint64(v_reuseFailAlloc_2492_, sizeof(void*)*1, v_tid_2476_);
v___x_2483_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
lean_object* v___x_2485_; 
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 4, v___x_2483_);
v___x_2485_ = v___x_2474_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_env_2464_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v_nextMacroScope_2465_);
lean_ctor_set(v_reuseFailAlloc_2491_, 2, v_ngen_2466_);
lean_ctor_set(v_reuseFailAlloc_2491_, 3, v_auxDeclNGen_2467_);
lean_ctor_set(v_reuseFailAlloc_2491_, 4, v___x_2483_);
lean_ctor_set(v_reuseFailAlloc_2491_, 5, v_cache_2468_);
lean_ctor_set(v_reuseFailAlloc_2491_, 6, v_messages_2469_);
lean_ctor_set(v_reuseFailAlloc_2491_, 7, v_infoState_2470_);
lean_ctor_set(v_reuseFailAlloc_2491_, 8, v_snapshotTasks_2471_);
lean_ctor_set(v_reuseFailAlloc_2491_, 9, v_newDecls_2472_);
v___x_2485_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2489_; 
v___x_2486_ = lean_st_ref_set(v___y_2429_, v___x_2485_);
v___x_2487_ = lean_box(0);
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 0, v___x_2487_);
v___x_2489_ = v___x_2460_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2487_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__2___redArg___boxed(lean_object* v_oldTraces_2497_, lean_object* v_data_2498_, lean_object* v_ref_2499_, lean_object* v_msg_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__2___redArg(v_oldTraces_2497_, v_data_2498_, v_ref_2499_, v_msg_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
return v_res_2506_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__1(lean_object* v_e_2507_){
_start:
{
if (lean_obj_tag(v_e_2507_) == 0)
{
uint8_t v___x_2508_; 
v___x_2508_ = 2;
return v___x_2508_;
}
else
{
lean_object* v_a_2509_; 
v_a_2509_ = lean_ctor_get(v_e_2507_, 0);
if (lean_obj_tag(v_a_2509_) == 0)
{
uint8_t v___x_2510_; 
v___x_2510_ = 1;
return v___x_2510_;
}
else
{
uint8_t v___x_2511_; 
v___x_2511_ = 0;
return v___x_2511_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__1___boxed(lean_object* v_e_2512_){
_start:
{
uint8_t v_res_2513_; lean_object* v_r_2514_; 
v_res_2513_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__1(v_e_2512_);
lean_dec_ref(v_e_2512_);
v_r_2514_ = lean_box(v_res_2513_);
return v_r_2514_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__3___redArg(lean_object* v_x_2515_){
_start:
{
if (lean_obj_tag(v_x_2515_) == 0)
{
lean_object* v_a_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2524_; 
v_a_2517_ = lean_ctor_get(v_x_2515_, 0);
v_isSharedCheck_2524_ = !lean_is_exclusive(v_x_2515_);
if (v_isSharedCheck_2524_ == 0)
{
v___x_2519_ = v_x_2515_;
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_a_2517_);
lean_dec(v_x_2515_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2524_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2522_; 
if (v_isShared_2520_ == 0)
{
lean_ctor_set_tag(v___x_2519_, 1);
v___x_2522_ = v___x_2519_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_a_2517_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
}
else
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2532_; 
v_a_2525_ = lean_ctor_get(v_x_2515_, 0);
v_isSharedCheck_2532_ = !lean_is_exclusive(v_x_2515_);
if (v_isSharedCheck_2532_ == 0)
{
v___x_2527_ = v_x_2515_;
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v_x_2515_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2532_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v___x_2530_; 
if (v_isShared_2528_ == 0)
{
lean_ctor_set_tag(v___x_2527_, 0);
v___x_2530_ = v___x_2527_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_a_2525_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__3___redArg___boxed(lean_object* v_x_2533_, lean_object* v___y_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__3___redArg(v_x_2533_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1(lean_object* v_cls_2536_, uint8_t v_collapsed_2537_, lean_object* v_tag_2538_, lean_object* v_opts_2539_, uint8_t v_clsEnabled_2540_, lean_object* v_oldTraces_2541_, lean_object* v_msg_2542_, lean_object* v_resStartStop_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v_fst_2552_; lean_object* v_snd_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2652_; 
v_fst_2552_ = lean_ctor_get(v_resStartStop_2543_, 0);
v_snd_2553_ = lean_ctor_get(v_resStartStop_2543_, 1);
v_isSharedCheck_2652_ = !lean_is_exclusive(v_resStartStop_2543_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2555_ = v_resStartStop_2543_;
v_isShared_2556_ = v_isSharedCheck_2652_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_snd_2553_);
lean_inc(v_fst_2552_);
lean_dec(v_resStartStop_2543_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2652_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v_data_2560_; lean_object* v_fst_2571_; lean_object* v_snd_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2651_; 
v_fst_2571_ = lean_ctor_get(v_snd_2553_, 0);
v_snd_2572_ = lean_ctor_get(v_snd_2553_, 1);
v_isSharedCheck_2651_ = !lean_is_exclusive(v_snd_2553_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2574_ = v_snd_2553_;
v_isShared_2575_ = v_isSharedCheck_2651_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_snd_2572_);
lean_inc(v_fst_2571_);
lean_dec(v_snd_2553_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2651_;
goto v_resetjp_2573_;
}
v___jp_2557_:
{
lean_object* v___x_2561_; 
lean_inc(v___y_2558_);
v___x_2561_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__2___redArg(v_oldTraces_2541_, v_data_2560_, v___y_2558_, v___y_2559_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v___x_2562_; 
lean_dec_ref(v___x_2561_);
v___x_2562_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__3___redArg(v_fst_2552_);
return v___x_2562_;
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec(v_fst_2552_);
v_a_2563_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2561_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2561_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
v_resetjp_2573_:
{
lean_object* v___x_2576_; uint8_t v___x_2577_; lean_object* v___y_2579_; lean_object* v_a_2580_; uint8_t v___y_2604_; double v___y_2636_; 
v___x_2576_ = l_Lean_trace_profiler;
v___x_2577_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_opts_2539_, v___x_2576_);
if (v___x_2577_ == 0)
{
v___y_2604_ = v___x_2577_;
goto v___jp_2603_;
}
else
{
lean_object* v___x_2641_; uint8_t v___x_2642_; 
v___x_2641_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2642_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_opts_2539_, v___x_2641_);
if (v___x_2642_ == 0)
{
lean_object* v___x_2643_; lean_object* v___x_2644_; double v___x_2645_; double v___x_2646_; double v___x_2647_; 
v___x_2643_ = l_Lean_trace_profiler_threshold;
v___x_2644_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__5(v_opts_2539_, v___x_2643_);
v___x_2645_ = lean_float_of_nat(v___x_2644_);
v___x_2646_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__5);
v___x_2647_ = lean_float_div(v___x_2645_, v___x_2646_);
v___y_2636_ = v___x_2647_;
goto v___jp_2635_;
}
else
{
lean_object* v___x_2648_; lean_object* v___x_2649_; double v___x_2650_; 
v___x_2648_ = l_Lean_trace_profiler_threshold;
v___x_2649_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__5(v_opts_2539_, v___x_2648_);
v___x_2650_ = lean_float_of_nat(v___x_2649_);
v___y_2636_ = v___x_2650_;
goto v___jp_2635_;
}
}
v___jp_2578_:
{
uint8_t v_result_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2586_; 
v_result_2581_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__1(v_fst_2552_);
v___x_2582_ = l_Lean_TraceResult_toEmoji(v_result_2581_);
v___x_2583_ = l_Lean_stringToMessageData(v___x_2582_);
v___x_2584_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1);
if (v_isShared_2575_ == 0)
{
lean_ctor_set_tag(v___x_2574_, 7);
lean_ctor_set(v___x_2574_, 1, v___x_2584_);
lean_ctor_set(v___x_2574_, 0, v___x_2583_);
v___x_2586_ = v___x_2574_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2583_);
lean_ctor_set(v_reuseFailAlloc_2597_, 1, v___x_2584_);
v___x_2586_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
lean_object* v_m_2588_; 
if (v_isShared_2556_ == 0)
{
lean_ctor_set_tag(v___x_2555_, 7);
lean_ctor_set(v___x_2555_, 1, v_a_2580_);
lean_ctor_set(v___x_2555_, 0, v___x_2586_);
v_m_2588_ = v___x_2555_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___x_2586_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v_a_2580_);
v_m_2588_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; double v___x_2591_; lean_object* v_data_2592_; 
v___x_2589_ = lean_box(v_result_2581_);
v___x_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
v___x_2591_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2);
lean_inc_ref(v_tag_2538_);
lean_inc_ref(v___x_2590_);
lean_inc(v_cls_2536_);
v_data_2592_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2592_, 0, v_cls_2536_);
lean_ctor_set(v_data_2592_, 1, v___x_2590_);
lean_ctor_set(v_data_2592_, 2, v_tag_2538_);
lean_ctor_set_float(v_data_2592_, sizeof(void*)*3, v___x_2591_);
lean_ctor_set_float(v_data_2592_, sizeof(void*)*3 + 8, v___x_2591_);
lean_ctor_set_uint8(v_data_2592_, sizeof(void*)*3 + 16, v_collapsed_2537_);
if (v___x_2577_ == 0)
{
lean_dec_ref(v___x_2590_);
lean_dec(v_snd_2572_);
lean_dec(v_fst_2571_);
lean_dec_ref(v_tag_2538_);
lean_dec(v_cls_2536_);
v___y_2558_ = v___y_2579_;
v___y_2559_ = v_m_2588_;
v_data_2560_ = v_data_2592_;
goto v___jp_2557_;
}
else
{
lean_object* v_data_2593_; double v___x_2594_; double v___x_2595_; 
lean_dec_ref(v_data_2592_);
v_data_2593_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2593_, 0, v_cls_2536_);
lean_ctor_set(v_data_2593_, 1, v___x_2590_);
lean_ctor_set(v_data_2593_, 2, v_tag_2538_);
v___x_2594_ = lean_unbox_float(v_fst_2571_);
lean_dec(v_fst_2571_);
lean_ctor_set_float(v_data_2593_, sizeof(void*)*3, v___x_2594_);
v___x_2595_ = lean_unbox_float(v_snd_2572_);
lean_dec(v_snd_2572_);
lean_ctor_set_float(v_data_2593_, sizeof(void*)*3 + 8, v___x_2595_);
lean_ctor_set_uint8(v_data_2593_, sizeof(void*)*3 + 16, v_collapsed_2537_);
v___y_2558_ = v___y_2579_;
v___y_2559_ = v_m_2588_;
v_data_2560_ = v_data_2593_;
goto v___jp_2557_;
}
}
}
}
v___jp_2598_:
{
lean_object* v_ref_2599_; lean_object* v___x_2600_; 
v_ref_2599_ = lean_ctor_get(v___y_2549_, 5);
lean_inc(v___y_2550_);
lean_inc_ref(v___y_2549_);
lean_inc(v___y_2548_);
lean_inc_ref(v___y_2547_);
lean_inc(v___y_2546_);
lean_inc_ref(v___y_2545_);
lean_inc(v___y_2544_);
lean_inc(v_fst_2552_);
v___x_2600_ = lean_apply_9(v_msg_2542_, v_fst_2552_, v___y_2544_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_, lean_box(0));
if (lean_obj_tag(v___x_2600_) == 0)
{
lean_object* v_a_2601_; 
v_a_2601_ = lean_ctor_get(v___x_2600_, 0);
lean_inc(v_a_2601_);
lean_dec_ref(v___x_2600_);
v___y_2579_ = v_ref_2599_;
v_a_2580_ = v_a_2601_;
goto v___jp_2578_;
}
else
{
lean_object* v___x_2602_; 
lean_dec_ref(v___x_2600_);
v___x_2602_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__4);
v___y_2579_ = v_ref_2599_;
v_a_2580_ = v___x_2602_;
goto v___jp_2578_;
}
}
v___jp_2603_:
{
if (v_clsEnabled_2540_ == 0)
{
if (v___y_2604_ == 0)
{
lean_object* v___x_2605_; lean_object* v_traceState_2606_; lean_object* v_env_2607_; lean_object* v_nextMacroScope_2608_; lean_object* v_ngen_2609_; lean_object* v_auxDeclNGen_2610_; lean_object* v_cache_2611_; lean_object* v_messages_2612_; lean_object* v_infoState_2613_; lean_object* v_snapshotTasks_2614_; lean_object* v_newDecls_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2634_; 
lean_del_object(v___x_2574_);
lean_dec(v_snd_2572_);
lean_dec(v_fst_2571_);
lean_del_object(v___x_2555_);
lean_dec_ref(v_msg_2542_);
lean_dec_ref(v_tag_2538_);
lean_dec(v_cls_2536_);
v___x_2605_ = lean_st_ref_take(v___y_2550_);
v_traceState_2606_ = lean_ctor_get(v___x_2605_, 4);
v_env_2607_ = lean_ctor_get(v___x_2605_, 0);
v_nextMacroScope_2608_ = lean_ctor_get(v___x_2605_, 1);
v_ngen_2609_ = lean_ctor_get(v___x_2605_, 2);
v_auxDeclNGen_2610_ = lean_ctor_get(v___x_2605_, 3);
v_cache_2611_ = lean_ctor_get(v___x_2605_, 5);
v_messages_2612_ = lean_ctor_get(v___x_2605_, 6);
v_infoState_2613_ = lean_ctor_get(v___x_2605_, 7);
v_snapshotTasks_2614_ = lean_ctor_get(v___x_2605_, 8);
v_newDecls_2615_ = lean_ctor_get(v___x_2605_, 9);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2617_ = v___x_2605_;
v_isShared_2618_ = v_isSharedCheck_2634_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_newDecls_2615_);
lean_inc(v_snapshotTasks_2614_);
lean_inc(v_infoState_2613_);
lean_inc(v_messages_2612_);
lean_inc(v_cache_2611_);
lean_inc(v_traceState_2606_);
lean_inc(v_auxDeclNGen_2610_);
lean_inc(v_ngen_2609_);
lean_inc(v_nextMacroScope_2608_);
lean_inc(v_env_2607_);
lean_dec(v___x_2605_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2634_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
uint64_t v_tid_2619_; lean_object* v_traces_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2633_; 
v_tid_2619_ = lean_ctor_get_uint64(v_traceState_2606_, sizeof(void*)*1);
v_traces_2620_ = lean_ctor_get(v_traceState_2606_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v_traceState_2606_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2622_ = v_traceState_2606_;
v_isShared_2623_ = v_isSharedCheck_2633_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_traces_2620_);
lean_dec(v_traceState_2606_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2633_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2624_; lean_object* v___x_2626_; 
v___x_2624_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2541_, v_traces_2620_);
lean_dec_ref(v_traces_2620_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 0, v___x_2624_);
v___x_2626_ = v___x_2622_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v___x_2624_);
lean_ctor_set_uint64(v_reuseFailAlloc_2632_, sizeof(void*)*1, v_tid_2619_);
v___x_2626_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
lean_object* v___x_2628_; 
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 4, v___x_2626_);
v___x_2628_ = v___x_2617_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_env_2607_);
lean_ctor_set(v_reuseFailAlloc_2631_, 1, v_nextMacroScope_2608_);
lean_ctor_set(v_reuseFailAlloc_2631_, 2, v_ngen_2609_);
lean_ctor_set(v_reuseFailAlloc_2631_, 3, v_auxDeclNGen_2610_);
lean_ctor_set(v_reuseFailAlloc_2631_, 4, v___x_2626_);
lean_ctor_set(v_reuseFailAlloc_2631_, 5, v_cache_2611_);
lean_ctor_set(v_reuseFailAlloc_2631_, 6, v_messages_2612_);
lean_ctor_set(v_reuseFailAlloc_2631_, 7, v_infoState_2613_);
lean_ctor_set(v_reuseFailAlloc_2631_, 8, v_snapshotTasks_2614_);
lean_ctor_set(v_reuseFailAlloc_2631_, 9, v_newDecls_2615_);
v___x_2628_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; 
v___x_2629_ = lean_st_ref_set(v___y_2550_, v___x_2628_);
v___x_2630_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__3___redArg(v_fst_2552_);
return v___x_2630_;
}
}
}
}
}
else
{
goto v___jp_2598_;
}
}
else
{
goto v___jp_2598_;
}
}
v___jp_2635_:
{
double v___x_2637_; double v___x_2638_; double v___x_2639_; uint8_t v___x_2640_; 
v___x_2637_ = lean_unbox_float(v_snd_2572_);
v___x_2638_ = lean_unbox_float(v_fst_2571_);
v___x_2639_ = lean_float_sub(v___x_2637_, v___x_2638_);
v___x_2640_ = lean_float_decLt(v___y_2636_, v___x_2639_);
v___y_2604_ = v___x_2640_;
goto v___jp_2603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1___boxed(lean_object* v_cls_2653_, lean_object* v_collapsed_2654_, lean_object* v_tag_2655_, lean_object* v_opts_2656_, lean_object* v_clsEnabled_2657_, lean_object* v_oldTraces_2658_, lean_object* v_msg_2659_, lean_object* v_resStartStop_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
uint8_t v_collapsed_boxed_2669_; uint8_t v_clsEnabled_boxed_2670_; lean_object* v_res_2671_; 
v_collapsed_boxed_2669_ = lean_unbox(v_collapsed_2654_);
v_clsEnabled_boxed_2670_ = lean_unbox(v_clsEnabled_2657_);
v_res_2671_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1(v_cls_2653_, v_collapsed_boxed_2669_, v_tag_2655_, v_opts_2656_, v_clsEnabled_boxed_2670_, v_oldTraces_2658_, v_msg_2659_, v_resStartStop_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
lean_dec(v___y_2667_);
lean_dec_ref(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec_ref(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec_ref(v___y_2662_);
lean_dec(v___y_2661_);
lean_dec_ref(v_opts_2656_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove(lean_object* v_e_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_){
_start:
{
lean_object* v_____do__lift_2682_; lean_object* v_options_2695_; uint8_t v_hasTrace_2696_; 
v_options_2695_ = lean_ctor_get(v_a_2678_, 2);
v_hasTrace_2696_ = lean_ctor_get_uint8(v_options_2695_, sizeof(void*)*1);
if (v_hasTrace_2696_ == 0)
{
lean_object* v___x_2697_; 
v___x_2697_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_e_2672_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2698_);
lean_dec_ref(v___x_2697_);
v_____do__lift_2682_ = v_a_2698_;
goto v___jp_2681_;
}
else
{
lean_object* v_a_2699_; lean_object* v___x_2701_; uint8_t v_isShared_2702_; uint8_t v_isSharedCheck_2706_; 
v_a_2699_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2706_ == 0)
{
v___x_2701_ = v___x_2697_;
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
else
{
lean_inc(v_a_2699_);
lean_dec(v___x_2697_);
v___x_2701_ = lean_box(0);
v_isShared_2702_ = v_isSharedCheck_2706_;
goto v_resetjp_2700_;
}
v_resetjp_2700_:
{
lean_object* v___x_2704_; 
if (v_isShared_2702_ == 0)
{
v___x_2704_ = v___x_2701_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v_a_2699_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2707_; lean_object* v___f_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; uint8_t v___x_2712_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v_a_2716_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v_a_2731_; lean_object* v___y_2734_; lean_object* v___y_2735_; lean_object* v_a_2736_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v_a_2748_; 
v_inheritedTraceOptions_2707_ = lean_ctor_get(v_a_2678_, 13);
lean_inc_ref(v_e_2672_);
v___f_2708_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_prove___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2708_, 0, v_e_2672_);
v___x_2709_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__2_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_));
v___x_2710_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_2711_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3);
v___x_2712_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2707_, v_options_2695_, v___x_2711_);
if (v___x_2712_ == 0)
{
lean_object* v___x_2797_; uint8_t v___x_2798_; 
v___x_2797_ = l_Lean_trace_profiler;
v___x_2798_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_2695_, v___x_2797_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2799_; 
lean_dec_ref(v___f_2708_);
v___x_2799_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_e_2672_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref(v___x_2799_);
v_____do__lift_2682_ = v_a_2800_;
goto v___jp_2681_;
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
v_a_2801_ = lean_ctor_get(v___x_2799_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2799_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2799_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2799_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
else
{
goto v___jp_2750_;
}
}
else
{
goto v___jp_2750_;
}
v___jp_2713_:
{
lean_object* v___x_2717_; double v___x_2718_; double v___x_2719_; double v___x_2720_; double v___x_2721_; double v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2717_ = lean_io_mono_nanos_now();
v___x_2718_ = lean_float_of_nat(v___y_2715_);
v___x_2719_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4);
v___x_2720_ = lean_float_div(v___x_2718_, v___x_2719_);
v___x_2721_ = lean_float_of_nat(v___x_2717_);
v___x_2722_ = lean_float_div(v___x_2721_, v___x_2719_);
v___x_2723_ = lean_box_float(v___x_2720_);
v___x_2724_ = lean_box_float(v___x_2722_);
v___x_2725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___x_2723_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
v___x_2726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2726_, 0, v_a_2716_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
v___x_2727_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1(v___x_2709_, v_hasTrace_2696_, v___x_2710_, v_options_2695_, v___x_2712_, v___y_2714_, v___f_2708_, v___x_2726_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
return v___x_2727_;
}
v___jp_2728_:
{
lean_object* v___x_2732_; 
v___x_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2732_, 0, v_a_2731_);
v___y_2714_ = v___y_2729_;
v___y_2715_ = v___y_2730_;
v_a_2716_ = v___x_2732_;
goto v___jp_2713_;
}
v___jp_2733_:
{
lean_object* v___x_2737_; double v___x_2738_; double v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2737_ = lean_io_get_num_heartbeats();
v___x_2738_ = lean_float_of_nat(v___y_2735_);
v___x_2739_ = lean_float_of_nat(v___x_2737_);
v___x_2740_ = lean_box_float(v___x_2738_);
v___x_2741_ = lean_box_float(v___x_2739_);
v___x_2742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2740_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
v___x_2743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2743_, 0, v_a_2736_);
lean_ctor_set(v___x_2743_, 1, v___x_2742_);
v___x_2744_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1(v___x_2709_, v_hasTrace_2696_, v___x_2710_, v_options_2695_, v___x_2712_, v___y_2734_, v___f_2708_, v___x_2743_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
return v___x_2744_;
}
v___jp_2745_:
{
lean_object* v___x_2749_; 
v___x_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2749_, 0, v_a_2748_);
v___y_2734_ = v___y_2746_;
v___y_2735_ = v___y_2747_;
v_a_2736_ = v___x_2749_;
goto v___jp_2733_;
}
v___jp_2750_:
{
lean_object* v___x_2751_; lean_object* v_a_2752_; lean_object* v___x_2753_; uint8_t v___x_2754_; 
v___x_2751_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___redArg(v_a_2679_);
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
lean_inc(v_a_2752_);
lean_dec_ref(v___x_2751_);
v___x_2753_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2754_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_2695_, v___x_2753_);
if (v___x_2754_ == 0)
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = lean_io_mono_nanos_now();
v___x_2756_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_e_2672_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2757_);
lean_dec_ref(v___x_2756_);
if (lean_obj_tag(v_a_2757_) == 0)
{
lean_object* v___x_2758_; 
v___x_2758_ = lean_box(0);
v___y_2729_ = v_a_2752_;
v___y_2730_ = v___x_2755_;
v_a_2731_ = v___x_2758_;
goto v___jp_2728_;
}
else
{
lean_object* v_val_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2767_; 
v_val_2759_ = lean_ctor_get(v_a_2757_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v_a_2757_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2761_ = v_a_2757_;
v_isShared_2762_ = v_isSharedCheck_2767_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_val_2759_);
lean_dec(v_a_2757_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2767_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2763_; lean_object* v___x_2765_; 
v___x_2763_ = l_Lean_mkFVar(v_val_2759_);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 0, v___x_2763_);
v___x_2765_ = v___x_2761_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2763_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
v___y_2729_ = v_a_2752_;
v___y_2730_ = v___x_2755_;
v_a_2731_ = v___x_2765_;
goto v___jp_2728_;
}
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
v_a_2768_ = lean_ctor_get(v___x_2756_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2756_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2756_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
lean_ctor_set_tag(v___x_2770_, 0);
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
v___y_2714_ = v_a_2752_;
v___y_2715_ = v___x_2755_;
v_a_2716_ = v___x_2773_;
goto v___jp_2713_;
}
}
}
}
else
{
lean_object* v___x_2776_; lean_object* v___x_2777_; 
v___x_2776_ = lean_io_get_num_heartbeats();
v___x_2777_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_e_2672_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc(v_a_2778_);
lean_dec_ref(v___x_2777_);
if (lean_obj_tag(v_a_2778_) == 0)
{
lean_object* v___x_2779_; 
v___x_2779_ = lean_box(0);
v___y_2746_ = v_a_2752_;
v___y_2747_ = v___x_2776_;
v_a_2748_ = v___x_2779_;
goto v___jp_2745_;
}
else
{
lean_object* v_val_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2788_; 
v_val_2780_ = lean_ctor_get(v_a_2778_, 0);
v_isSharedCheck_2788_ = !lean_is_exclusive(v_a_2778_);
if (v_isSharedCheck_2788_ == 0)
{
v___x_2782_ = v_a_2778_;
v_isShared_2783_ = v_isSharedCheck_2788_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_val_2780_);
lean_dec(v_a_2778_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2788_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2784_; lean_object* v___x_2786_; 
v___x_2784_ = l_Lean_mkFVar(v_val_2780_);
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 0, v___x_2784_);
v___x_2786_ = v___x_2782_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v___x_2784_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
v___y_2746_ = v_a_2752_;
v___y_2747_ = v___x_2776_;
v_a_2748_ = v___x_2786_;
goto v___jp_2745_;
}
}
}
}
else
{
lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2796_; 
v_a_2789_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2796_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2796_ == 0)
{
v___x_2791_ = v___x_2777_;
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2777_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2796_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2794_; 
if (v_isShared_2792_ == 0)
{
lean_ctor_set_tag(v___x_2791_, 0);
v___x_2794_ = v___x_2791_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
v___y_2734_ = v_a_2752_;
v___y_2735_ = v___x_2776_;
v_a_2736_ = v___x_2794_;
goto v___jp_2733_;
}
}
}
}
}
}
v___jp_2681_:
{
if (lean_obj_tag(v_____do__lift_2682_) == 0)
{
lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2683_ = lean_box(0);
v___x_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2683_);
return v___x_2684_;
}
else
{
lean_object* v_val_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2694_; 
v_val_2685_ = lean_ctor_get(v_____do__lift_2682_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v_____do__lift_2682_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2687_ = v_____do__lift_2682_;
v_isShared_2688_ = v_isSharedCheck_2694_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_val_2685_);
lean_dec(v_____do__lift_2682_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2694_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2689_; lean_object* v___x_2691_; 
v___x_2689_ = l_Lean_mkFVar(v_val_2685_);
if (v_isShared_2688_ == 0)
{
lean_ctor_set(v___x_2687_, 0, v___x_2689_);
v___x_2691_ = v___x_2687_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v___x_2689_);
v___x_2691_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
lean_object* v___x_2692_; 
v___x_2692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2691_);
return v___x_2692_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___boxed(lean_object* v_e_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_Lean_Elab_Tactic_NormCast_prove(v_e_2809_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_);
lean_dec(v_a_2816_);
lean_dec_ref(v_a_2815_);
lean_dec(v_a_2814_);
lean_dec_ref(v_a_2813_);
lean_dec(v_a_2812_);
lean_dec_ref(v_a_2811_);
lean_dec(v_a_2810_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__3(lean_object* v_00_u03b1_2819_, lean_object* v_x_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_){
_start:
{
lean_object* v___x_2829_; 
v___x_2829_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__3___redArg(v_x_2820_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2830_, lean_object* v_x_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__3(v_00_u03b1_2830_, v_x_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec(v___y_2832_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__2(lean_object* v_oldTraces_2841_, lean_object* v_data_2842_, lean_object* v_ref_2843_, lean_object* v_msg_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v___x_2853_; 
v___x_2853_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__2___redArg(v_oldTraces_2841_, v_data_2842_, v_ref_2843_, v_msg_2844_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__2___boxed(lean_object* v_oldTraces_2854_, lean_object* v_data_2855_, lean_object* v_ref_2856_, lean_object* v_msg_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__2(v_oldTraces_2854_, v_data_2855_, v_ref_2856_, v_msg_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
lean_dec(v___y_2864_);
lean_dec_ref(v___y_2863_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec(v___y_2858_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0(lean_object* v_a_2867_, lean_object* v_cache_2868_, lean_object* v_a_x3f_2869_){
_start:
{
lean_object* v___x_2871_; lean_object* v_congrCache_2872_; lean_object* v_dsimpCache_2873_; lean_object* v_usedTheorems_2874_; lean_object* v_numSteps_2875_; lean_object* v_diag_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2886_; 
v___x_2871_ = lean_st_ref_take(v_a_2867_);
v_congrCache_2872_ = lean_ctor_get(v___x_2871_, 1);
v_dsimpCache_2873_ = lean_ctor_get(v___x_2871_, 2);
v_usedTheorems_2874_ = lean_ctor_get(v___x_2871_, 3);
v_numSteps_2875_ = lean_ctor_get(v___x_2871_, 4);
v_diag_2876_ = lean_ctor_get(v___x_2871_, 5);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2886_ == 0)
{
lean_object* v_unused_2887_; 
v_unused_2887_ = lean_ctor_get(v___x_2871_, 0);
lean_dec(v_unused_2887_);
v___x_2878_ = v___x_2871_;
v_isShared_2879_ = v_isSharedCheck_2886_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_diag_2876_);
lean_inc(v_numSteps_2875_);
lean_inc(v_usedTheorems_2874_);
lean_inc(v_dsimpCache_2873_);
lean_inc(v_congrCache_2872_);
lean_dec(v___x_2871_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2886_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 0, v_cache_2868_);
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_cache_2868_);
lean_ctor_set(v_reuseFailAlloc_2885_, 1, v_congrCache_2872_);
lean_ctor_set(v_reuseFailAlloc_2885_, 2, v_dsimpCache_2873_);
lean_ctor_set(v_reuseFailAlloc_2885_, 3, v_usedTheorems_2874_);
lean_ctor_set(v_reuseFailAlloc_2885_, 4, v_numSteps_2875_);
lean_ctor_set(v_reuseFailAlloc_2885_, 5, v_diag_2876_);
v___x_2881_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2882_ = lean_st_ref_set(v_a_2867_, v___x_2881_);
v___x_2883_ = lean_box(0);
v___x_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2883_);
return v___x_2884_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0___boxed(lean_object* v_a_2888_, lean_object* v_cache_2889_, lean_object* v_a_x3f_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0(v_a_2888_, v_cache_2889_, v_a_x3f_2890_);
lean_dec(v_a_x3f_2890_);
lean_dec(v_a_2888_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim(lean_object* v_up_2895_, lean_object* v_e_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_){
_start:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v_congrCache_2907_; lean_object* v_dsimpCache_2908_; lean_object* v_usedTheorems_2909_; lean_object* v_numSteps_2910_; lean_object* v_diag_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_3013_; 
v___x_2905_ = lean_st_ref_get(v_a_2899_);
v___x_2906_ = lean_st_ref_take(v_a_2899_);
v_congrCache_2907_ = lean_ctor_get(v___x_2906_, 1);
v_dsimpCache_2908_ = lean_ctor_get(v___x_2906_, 2);
v_usedTheorems_2909_ = lean_ctor_get(v___x_2906_, 3);
v_numSteps_2910_ = lean_ctor_get(v___x_2906_, 4);
v_diag_2911_ = lean_ctor_get(v___x_2906_, 5);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_3013_ == 0)
{
lean_object* v_unused_3014_; 
v_unused_3014_ = lean_ctor_get(v___x_2906_, 0);
lean_dec(v_unused_3014_);
v___x_2913_ = v___x_2906_;
v_isShared_2914_ = v_isSharedCheck_3013_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_diag_2911_);
lean_inc(v_numSteps_2910_);
lean_inc(v_usedTheorems_2909_);
lean_inc(v_dsimpCache_2908_);
lean_inc(v_congrCache_2907_);
lean_dec(v___x_2906_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_3013_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
uint8_t v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2918_; 
v___x_2915_ = 1;
v___x_2916_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 0, v___x_2916_);
v___x_2918_ = v___x_2913_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_2916_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_congrCache_2907_);
lean_ctor_set(v_reuseFailAlloc_3012_, 2, v_dsimpCache_2908_);
lean_ctor_set(v_reuseFailAlloc_3012_, 3, v_usedTheorems_2909_);
lean_ctor_set(v_reuseFailAlloc_3012_, 4, v_numSteps_2910_);
lean_ctor_set(v_reuseFailAlloc_3012_, 5, v_diag_2911_);
v___x_2918_ = v_reuseFailAlloc_3012_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
lean_object* v___x_2919_; lean_object* v_post_2920_; lean_object* v_erased_2921_; lean_object* v_cache_2922_; lean_object* v_pre_2923_; lean_object* v_post_2924_; lean_object* v_dpre_2925_; lean_object* v_dpost_2926_; lean_object* v___x_2927_; uint8_t v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v_r_2931_; 
v___x_2919_ = lean_st_ref_set(v_a_2899_, v___x_2918_);
v_post_2920_ = lean_ctor_get(v_up_2895_, 1);
v_erased_2921_ = lean_ctor_get(v_up_2895_, 4);
v_cache_2922_ = lean_ctor_get(v___x_2905_, 0);
lean_inc_ref(v_cache_2922_);
lean_dec(v___x_2905_);
v_pre_2923_ = lean_ctor_get(v_a_2897_, 0);
v_post_2924_ = lean_ctor_get(v_a_2897_, 1);
v_dpre_2925_ = lean_ctor_get(v_a_2897_, 2);
v_dpost_2926_ = lean_ctor_get(v_a_2897_, 3);
v___x_2927_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__0));
v___x_2928_ = 0;
v___x_2929_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__1));
lean_inc_ref(v_dpost_2926_);
lean_inc_ref(v_dpre_2925_);
lean_inc_ref(v_post_2924_);
lean_inc_ref(v_pre_2923_);
v___x_2930_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2930_, 0, v_pre_2923_);
lean_ctor_set(v___x_2930_, 1, v_post_2924_);
lean_ctor_set(v___x_2930_, 2, v_dpre_2925_);
lean_ctor_set(v___x_2930_, 3, v_dpost_2926_);
lean_ctor_set(v___x_2930_, 4, v___x_2927_);
lean_ctor_set_uint8(v___x_2930_, sizeof(void*)*5, v___x_2928_);
lean_inc_ref(v_e_2896_);
v_r_2931_ = l_Lean_Meta_Simp_rewrite_x3f(v_e_2896_, v_post_2920_, v_erased_2921_, v___x_2929_, v___x_2928_, v___x_2930_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
lean_dec_ref(v___x_2930_);
if (lean_obj_tag(v_r_2931_) == 0)
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_3000_; 
v_a_2932_ = lean_ctor_get(v_r_2931_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v_r_2931_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2934_ = v_r_2931_;
v_isShared_2935_ = v_isSharedCheck_3000_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v_r_2931_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_3000_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2937_; 
lean_inc(v_a_2932_);
if (v_isShared_2935_ == 0)
{
lean_ctor_set_tag(v___x_2934_, 1);
v___x_2937_ = v___x_2934_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2932_);
v___x_2937_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
lean_object* v___x_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2997_; 
v___x_2938_ = l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0(v_a_2899_, v_cache_2922_, v___x_2937_);
lean_dec_ref(v___x_2937_);
v_isSharedCheck_2997_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_2997_ == 0)
{
lean_object* v_unused_2998_; 
v_unused_2998_ = lean_ctor_get(v___x_2938_, 0);
lean_dec(v_unused_2998_);
v___x_2940_ = v___x_2938_;
v_isShared_2941_ = v_isSharedCheck_2997_;
goto v_resetjp_2939_;
}
else
{
lean_dec(v___x_2938_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2997_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___y_2943_; lean_object* v_expr_2944_; 
if (lean_obj_tag(v_a_2932_) == 0)
{
lean_object* v___x_2993_; lean_object* v___x_2994_; 
v___x_2993_ = lean_box(0);
lean_inc_ref_n(v_e_2896_, 2);
v___x_2994_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2994_, 0, v_e_2896_);
lean_ctor_set(v___x_2994_, 1, v___x_2993_);
lean_ctor_set_uint8(v___x_2994_, sizeof(void*)*2, v___x_2915_);
v___y_2943_ = v___x_2994_;
v_expr_2944_ = v_e_2896_;
goto v___jp_2942_;
}
else
{
lean_object* v_val_2995_; lean_object* v_expr_2996_; 
v_val_2995_ = lean_ctor_get(v_a_2932_, 0);
lean_inc(v_val_2995_);
lean_dec_ref(v_a_2932_);
v_expr_2996_ = lean_ctor_get(v_val_2995_, 0);
lean_inc_ref(v_expr_2996_);
v___y_2943_ = v_val_2995_;
v_expr_2944_ = v_expr_2996_;
goto v___jp_2942_;
}
v___jp_2942_:
{
lean_object* v___x_2945_; 
v___x_2945_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure(v_expr_2944_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___x_2947_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
lean_dec_ref(v___x_2945_);
v___x_2947_ = l_Lean_Meta_Simp_Result_mkEqTrans(v___y_2943_, v_a_2946_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2976_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2950_ = v___x_2947_;
v_isShared_2951_ = v_isSharedCheck_2976_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2947_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2976_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v_expr_2952_; uint8_t v___x_2953_; 
v_expr_2952_ = lean_ctor_get(v_a_2948_, 0);
v___x_2953_ = lean_expr_eqv(v_expr_2952_, v_e_2896_);
if (v___x_2953_ == 0)
{
lean_object* v___x_2955_; 
lean_dec_ref(v_e_2896_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set_tag(v___x_2940_, 1);
lean_ctor_set(v___x_2940_, 0, v_a_2948_);
v___x_2955_ = v___x_2940_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2948_);
v___x_2955_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
lean_object* v___x_2957_; 
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 0, v___x_2955_);
v___x_2957_ = v___x_2950_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v___x_2955_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
else
{
lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2973_; 
v_isSharedCheck_2973_ = !lean_is_exclusive(v_a_2948_);
if (v_isSharedCheck_2973_ == 0)
{
lean_object* v_unused_2974_; lean_object* v_unused_2975_; 
v_unused_2974_ = lean_ctor_get(v_a_2948_, 1);
lean_dec(v_unused_2974_);
v_unused_2975_ = lean_ctor_get(v_a_2948_, 0);
lean_dec(v_unused_2975_);
v___x_2961_ = v_a_2948_;
v_isShared_2962_ = v_isSharedCheck_2973_;
goto v_resetjp_2960_;
}
else
{
lean_dec(v_a_2948_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2973_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2963_; lean_object* v___x_2965_; 
v___x_2963_ = lean_box(0);
if (v_isShared_2962_ == 0)
{
lean_ctor_set(v___x_2961_, 1, v___x_2963_);
lean_ctor_set(v___x_2961_, 0, v_e_2896_);
v___x_2965_ = v___x_2961_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_e_2896_);
lean_ctor_set(v_reuseFailAlloc_2972_, 1, v___x_2963_);
v___x_2965_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
lean_object* v___x_2967_; 
lean_ctor_set_uint8(v___x_2965_, sizeof(void*)*2, v___x_2953_);
if (v_isShared_2941_ == 0)
{
lean_ctor_set(v___x_2940_, 0, v___x_2965_);
v___x_2967_ = v___x_2940_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2971_; 
v_reuseFailAlloc_2971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2971_, 0, v___x_2965_);
v___x_2967_ = v_reuseFailAlloc_2971_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
lean_object* v___x_2969_; 
if (v_isShared_2951_ == 0)
{
lean_ctor_set(v___x_2950_, 0, v___x_2967_);
v___x_2969_ = v___x_2950_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v___x_2967_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2984_; 
lean_del_object(v___x_2940_);
lean_dec_ref(v_e_2896_);
v_a_2977_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2979_ = v___x_2947_;
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2947_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2982_; 
if (v_isShared_2980_ == 0)
{
v___x_2982_ = v___x_2979_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_a_2977_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
}
else
{
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2992_; 
lean_dec_ref(v___y_2943_);
lean_del_object(v___x_2940_);
lean_dec_ref(v_e_2896_);
v_a_2985_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2987_ = v___x_2945_;
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___x_2945_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2990_; 
if (v_isShared_2988_ == 0)
{
v___x_2990_ = v___x_2987_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_a_2985_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
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
lean_object* v_a_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_dec_ref(v_e_2896_);
v_a_3001_ = lean_ctor_get(v_r_2931_, 0);
lean_inc(v_a_3001_);
lean_dec_ref(v_r_2931_);
v___x_3002_ = lean_box(0);
v___x_3003_ = l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0(v_a_2899_, v_cache_2922_, v___x_3002_);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3010_ == 0)
{
lean_object* v_unused_3011_; 
v_unused_3011_ = lean_ctor_get(v___x_3003_, 0);
lean_dec(v_unused_3011_);
v___x_3005_ = v___x_3003_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_dec(v___x_3003_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
lean_ctor_set_tag(v___x_3005_, 1);
lean_ctor_set(v___x_3005_, 0, v_a_3001_);
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3001_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___boxed(lean_object* v_up_3015_, lean_object* v_e_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l_Lean_Elab_Tactic_NormCast_upwardAndElim(v_up_3015_, v_e_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_);
lean_dec(v_a_3023_);
lean_dec_ref(v_a_3022_);
lean_dec(v_a_3021_);
lean_dec_ref(v_a_3020_);
lean_dec(v_a_3019_);
lean_dec_ref(v_a_3018_);
lean_dec(v_a_3017_);
lean_dec_ref(v_up_3015_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_numeralToCoe(lean_object* v_e_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_e_3030_);
if (lean_obj_tag(v___x_3036_) == 1)
{
lean_object* v_val_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3112_; 
v_val_3037_ = lean_ctor_get(v___x_3036_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3039_ = v___x_3036_;
v_isShared_3040_ = v_isSharedCheck_3112_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_val_3037_);
lean_dec(v___x_3036_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3112_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v_fst_3041_; lean_object* v_snd_3042_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___x_3090_; 
v_fst_3041_ = lean_ctor_get(v_val_3037_, 0);
lean_inc_n(v_fst_3041_, 2);
v_snd_3042_ = lean_ctor_get(v_val_3037_, 1);
lean_inc(v_snd_3042_);
lean_dec(v_val_3037_);
lean_inc(v_a_3034_);
lean_inc_ref(v_a_3033_);
lean_inc(v_a_3032_);
lean_inc_ref(v_a_3031_);
v___x_3090_ = lean_whnf(v_fst_3041_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3091_; lean_object* v___x_3092_; uint8_t v___x_3093_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_a_3091_);
lean_dec_ref(v___x_3090_);
v___x_3092_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__5));
v___x_3093_ = l_Lean_Expr_isConstOf(v_a_3091_, v___x_3092_);
lean_dec(v_a_3091_);
if (v___x_3093_ == 0)
{
v___y_3044_ = v_a_3031_;
v___y_3045_ = v_a_3032_;
v___y_3046_ = v_a_3033_;
v___y_3047_ = v_a_3034_;
goto v___jp_3043_;
}
else
{
lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
lean_dec(v_snd_3042_);
lean_dec(v_fst_3041_);
lean_del_object(v___x_3039_);
lean_dec_ref(v_e_3030_);
v___x_3094_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_3095_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_3094_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_);
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v___x_3095_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3095_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3101_; 
if (v_isShared_3099_ == 0)
{
v___x_3101_ = v___x_3098_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_a_3096_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_dec(v_snd_3042_);
lean_dec(v_fst_3041_);
lean_del_object(v___x_3039_);
lean_dec_ref(v_e_3030_);
v_a_3104_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3090_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3090_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
v___jp_3043_:
{
lean_object* v___x_3048_; lean_object* v___x_3050_; 
v___x_3048_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_numeralToCoe___closed__1));
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 0, v_fst_3041_);
v___x_3050_ = v___x_3039_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3089_; 
v_reuseFailAlloc_3089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_fst_3041_);
v___x_3050_ = v_reuseFailAlloc_3089_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3051_ = lean_box(0);
v___x_3052_ = l_Lean_mkNatLit(v_snd_3042_);
v___x_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3052_);
v___x_3054_ = lean_unsigned_to_nat(3u);
v___x_3055_ = lean_mk_empty_array_with_capacity(v___x_3054_);
v___x_3056_ = lean_array_push(v___x_3055_, v___x_3050_);
v___x_3057_ = lean_array_push(v___x_3056_, v___x_3051_);
v___x_3058_ = lean_array_push(v___x_3057_, v___x_3053_);
v___x_3059_ = l_Lean_Meta_mkAppOptM(v___x_3048_, v___x_3058_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_a_3060_; lean_object* v___x_3061_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_a_3060_);
lean_dec_ref(v___x_3059_);
v___x_3061_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_e_3030_, v_a_3060_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3072_; 
v_a_3062_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3064_ = v___x_3061_;
v_isShared_3065_ = v_isSharedCheck_3072_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3061_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3072_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
if (lean_obj_tag(v_a_3062_) == 1)
{
lean_object* v_val_3066_; lean_object* v___x_3068_; 
v_val_3066_ = lean_ctor_get(v_a_3062_, 0);
lean_inc(v_val_3066_);
lean_dec_ref(v_a_3062_);
if (v_isShared_3065_ == 0)
{
lean_ctor_set(v___x_3064_, 0, v_val_3066_);
v___x_3068_ = v___x_3064_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_val_3066_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
else
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
lean_del_object(v___x_3064_);
lean_dec(v_a_3062_);
v___x_3070_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_3071_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_3070_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
return v___x_3071_;
}
}
}
else
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3080_; 
v_a_3073_ = lean_ctor_get(v___x_3061_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3061_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3075_ = v___x_3061_;
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3061_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3078_; 
if (v_isShared_3076_ == 0)
{
v___x_3078_ = v___x_3075_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3073_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_dec_ref(v_e_3030_);
v_a_3081_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_3059_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_3059_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
lean_dec(v___x_3036_);
lean_dec_ref(v_e_3030_);
v___x_3113_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_3114_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_3113_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_);
return v___x_3114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_numeralToCoe___boxed(lean_object* v_e_3115_, lean_object* v_a_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_){
_start:
{
lean_object* v_res_3121_; 
v_res_3121_ = l_Lean_Elab_Tactic_NormCast_numeralToCoe(v_e_3115_, v_a_3116_, v_a_3117_, v_a_3118_, v_a_3119_);
lean_dec(v_a_3119_);
lean_dec_ref(v_a_3118_);
lean_dec(v_a_3117_);
lean_dec_ref(v_a_3116_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(lean_object* v_e_3130_, lean_object* v_a_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_){
_start:
{
lean_object* v___x_3136_; uint8_t v___x_3137_; uint8_t v___x_3138_; lean_object* v___x_3139_; 
v___x_3136_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_));
v___x_3137_ = 0;
v___x_3138_ = 1;
v___x_3139_ = l_Lean_Meta_evalExpr_x27___redArg(v___x_3136_, v_e_3130_, v___x_3137_, v___x_3138_, v_a_3131_, v_a_3132_, v_a_3133_, v_a_3134_);
return v___x_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3____boxed(lean_object* v_e_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(v_e_3140_, v_a_3141_, v_a_3142_, v_a_3143_, v_a_3144_);
lean_dec(v_a_3144_);
lean_dec_ref(v_a_3143_);
lean_dec(v_a_3142_);
lean_dec_ref(v_a_3141_);
return v_res_3146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(lean_object* v_e_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_){
_start:
{
lean_object* v___x_3155_; 
v___x_3155_ = l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(v_e_3147_, v_a_3150_, v_a_3151_, v_a_3152_, v_a_3153_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3____boxed(lean_object* v_e_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l_Lean_Elab_Tactic_NormCast_evalUnsafe_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(v_e_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_);
lean_dec(v_a_3162_);
lean_dec_ref(v_a_3161_);
lean_dec(v_a_3160_);
lean_dec_ref(v_a_3159_);
lean_dec(v_a_3158_);
lean_dec_ref(v_a_3157_);
return v_res_3164_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__0(void){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3165_ = lean_box(1);
v___x_3166_ = l_Lean_MessageData_ofFormat(v___x_3165_);
return v___x_3166_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__3(void){
_start:
{
lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3170_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__2));
v___x_3171_ = l_Lean_MessageData_ofFormat(v___x_3170_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8(lean_object* v_x_3172_, lean_object* v_x_3173_){
_start:
{
if (lean_obj_tag(v_x_3173_) == 0)
{
return v_x_3172_;
}
else
{
lean_object* v_head_3174_; lean_object* v_tail_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3197_; 
v_head_3174_ = lean_ctor_get(v_x_3173_, 0);
v_tail_3175_ = lean_ctor_get(v_x_3173_, 1);
v_isSharedCheck_3197_ = !lean_is_exclusive(v_x_3173_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3177_ = v_x_3173_;
v_isShared_3178_ = v_isSharedCheck_3197_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_tail_3175_);
lean_inc(v_head_3174_);
lean_dec(v_x_3173_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3197_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v_before_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3195_; 
v_before_3179_ = lean_ctor_get(v_head_3174_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v_head_3174_);
if (v_isSharedCheck_3195_ == 0)
{
lean_object* v_unused_3196_; 
v_unused_3196_ = lean_ctor_get(v_head_3174_, 1);
lean_dec(v_unused_3196_);
v___x_3181_ = v_head_3174_;
v_isShared_3182_ = v_isSharedCheck_3195_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_before_3179_);
lean_dec(v_head_3174_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3195_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3183_; lean_object* v___x_3185_; 
v___x_3183_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__0);
if (v_isShared_3182_ == 0)
{
lean_ctor_set_tag(v___x_3181_, 7);
lean_ctor_set(v___x_3181_, 1, v___x_3183_);
lean_ctor_set(v___x_3181_, 0, v_x_3172_);
v___x_3185_ = v___x_3181_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_x_3172_);
lean_ctor_set(v_reuseFailAlloc_3194_, 1, v___x_3183_);
v___x_3185_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
lean_object* v___x_3186_; lean_object* v___x_3188_; 
v___x_3186_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__3);
if (v_isShared_3178_ == 0)
{
lean_ctor_set_tag(v___x_3177_, 7);
lean_ctor_set(v___x_3177_, 1, v___x_3186_);
lean_ctor_set(v___x_3177_, 0, v___x_3185_);
v___x_3188_ = v___x_3177_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3185_);
lean_ctor_set(v_reuseFailAlloc_3193_, 1, v___x_3186_);
v___x_3188_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3189_ = l_Lean_MessageData_ofSyntax(v_before_3179_);
v___x_3190_ = l_Lean_indentD(v___x_3189_);
v___x_3191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3188_);
lean_ctor_set(v___x_3191_, 1, v___x_3190_);
v_x_3172_ = v___x_3191_;
v_x_3173_ = v_tail_3175_;
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
lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3201_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__1));
v___x_3202_ = l_Lean_MessageData_ofFormat(v___x_3201_);
return v___x_3202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg(lean_object* v_msgData_3203_, lean_object* v_macroStack_3204_, lean_object* v___y_3205_){
_start:
{
lean_object* v_options_3207_; lean_object* v___x_3208_; uint8_t v___x_3209_; 
v_options_3207_ = lean_ctor_get(v___y_3205_, 2);
v___x_3208_ = l_Lean_Elab_pp_macroStack;
v___x_3209_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_3207_, v___x_3208_);
if (v___x_3209_ == 0)
{
lean_object* v___x_3210_; 
lean_dec(v_macroStack_3204_);
v___x_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3210_, 0, v_msgData_3203_);
return v___x_3210_;
}
else
{
if (lean_obj_tag(v_macroStack_3204_) == 0)
{
lean_object* v___x_3211_; 
v___x_3211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3211_, 0, v_msgData_3203_);
return v___x_3211_;
}
else
{
lean_object* v_head_3212_; lean_object* v_after_3213_; lean_object* v___x_3215_; uint8_t v_isShared_3216_; uint8_t v_isSharedCheck_3228_; 
v_head_3212_ = lean_ctor_get(v_macroStack_3204_, 0);
lean_inc(v_head_3212_);
v_after_3213_ = lean_ctor_get(v_head_3212_, 1);
v_isSharedCheck_3228_ = !lean_is_exclusive(v_head_3212_);
if (v_isSharedCheck_3228_ == 0)
{
lean_object* v_unused_3229_; 
v_unused_3229_ = lean_ctor_get(v_head_3212_, 0);
lean_dec(v_unused_3229_);
v___x_3215_ = v_head_3212_;
v_isShared_3216_ = v_isSharedCheck_3228_;
goto v_resetjp_3214_;
}
else
{
lean_inc(v_after_3213_);
lean_dec(v_head_3212_);
v___x_3215_ = lean_box(0);
v_isShared_3216_ = v_isSharedCheck_3228_;
goto v_resetjp_3214_;
}
v_resetjp_3214_:
{
lean_object* v___x_3217_; lean_object* v___x_3219_; 
v___x_3217_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__0);
if (v_isShared_3216_ == 0)
{
lean_ctor_set_tag(v___x_3215_, 7);
lean_ctor_set(v___x_3215_, 1, v___x_3217_);
lean_ctor_set(v___x_3215_, 0, v_msgData_3203_);
v___x_3219_ = v___x_3215_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3227_; 
v_reuseFailAlloc_3227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3227_, 0, v_msgData_3203_);
lean_ctor_set(v_reuseFailAlloc_3227_, 1, v___x_3217_);
v___x_3219_ = v_reuseFailAlloc_3227_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v_msgData_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3220_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__2);
v___x_3221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3219_);
lean_ctor_set(v___x_3221_, 1, v___x_3220_);
v___x_3222_ = l_Lean_MessageData_ofSyntax(v_after_3213_);
v___x_3223_ = l_Lean_indentD(v___x_3222_);
v_msgData_3224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_3224_, 0, v___x_3221_);
lean_ctor_set(v_msgData_3224_, 1, v___x_3223_);
v___x_3225_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8(v_msgData_3224_, v_macroStack_3204_);
v___x_3226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3225_);
return v___x_3226_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___boxed(lean_object* v_msgData_3230_, lean_object* v_macroStack_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg(v_msgData_3230_, v_macroStack_3231_, v___y_3232_);
lean_dec_ref(v___y_3232_);
return v_res_3234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg(lean_object* v_msg_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_){
_start:
{
lean_object* v_ref_3243_; lean_object* v___x_3244_; lean_object* v_a_3245_; lean_object* v_macroStack_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3257_; 
v_ref_3243_ = lean_ctor_get(v___y_3240_, 5);
v___x_3244_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__5(v_msg_3235_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
lean_inc(v_a_3245_);
lean_dec_ref(v___x_3244_);
v_macroStack_3246_ = lean_ctor_get(v___y_3236_, 1);
v___x_3247_ = l_Lean_Elab_getBetterRef(v_ref_3243_, v_macroStack_3246_);
lean_inc(v_macroStack_3246_);
v___x_3248_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg(v_a_3245_, v_macroStack_3246_, v___y_3240_);
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3251_ = v___x_3248_;
v_isShared_3252_ = v_isSharedCheck_3257_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___x_3248_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3257_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3253_; lean_object* v___x_3255_; 
v___x_3253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3253_, 0, v___x_3247_);
lean_ctor_set(v___x_3253_, 1, v_a_3249_);
if (v_isShared_3252_ == 0)
{
lean_ctor_set_tag(v___x_3251_, 1);
lean_ctor_set(v___x_3251_, 0, v___x_3253_);
v___x_3255_ = v___x_3251_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3253_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg___boxed(lean_object* v_msg_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v_res_3266_; 
v_res_3266_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg(v_msg_3258_, v___y_3259_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec(v___y_3262_);
lean_dec_ref(v___y_3261_);
lean_dec(v___y_3260_);
lean_dec_ref(v___y_3259_);
return v_res_3266_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg(lean_object* v_cls_3269_, lean_object* v_msg_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
lean_object* v_ref_3276_; lean_object* v___x_3277_; lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3323_; 
v_ref_3276_ = lean_ctor_get(v___y_3273_, 5);
v___x_3277_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__5(v_msg_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3280_ = v___x_3277_;
v_isShared_3281_ = v_isSharedCheck_3323_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3277_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3323_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
lean_object* v___x_3282_; lean_object* v_traceState_3283_; lean_object* v_env_3284_; lean_object* v_nextMacroScope_3285_; lean_object* v_ngen_3286_; lean_object* v_auxDeclNGen_3287_; lean_object* v_cache_3288_; lean_object* v_messages_3289_; lean_object* v_infoState_3290_; lean_object* v_snapshotTasks_3291_; lean_object* v_newDecls_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3322_; 
v___x_3282_ = lean_st_ref_take(v___y_3274_);
v_traceState_3283_ = lean_ctor_get(v___x_3282_, 4);
v_env_3284_ = lean_ctor_get(v___x_3282_, 0);
v_nextMacroScope_3285_ = lean_ctor_get(v___x_3282_, 1);
v_ngen_3286_ = lean_ctor_get(v___x_3282_, 2);
v_auxDeclNGen_3287_ = lean_ctor_get(v___x_3282_, 3);
v_cache_3288_ = lean_ctor_get(v___x_3282_, 5);
v_messages_3289_ = lean_ctor_get(v___x_3282_, 6);
v_infoState_3290_ = lean_ctor_get(v___x_3282_, 7);
v_snapshotTasks_3291_ = lean_ctor_get(v___x_3282_, 8);
v_newDecls_3292_ = lean_ctor_get(v___x_3282_, 9);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3282_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3294_ = v___x_3282_;
v_isShared_3295_ = v_isSharedCheck_3322_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_newDecls_3292_);
lean_inc(v_snapshotTasks_3291_);
lean_inc(v_infoState_3290_);
lean_inc(v_messages_3289_);
lean_inc(v_cache_3288_);
lean_inc(v_traceState_3283_);
lean_inc(v_auxDeclNGen_3287_);
lean_inc(v_ngen_3286_);
lean_inc(v_nextMacroScope_3285_);
lean_inc(v_env_3284_);
lean_dec(v___x_3282_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3322_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
uint64_t v_tid_3296_; lean_object* v_traces_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3321_; 
v_tid_3296_ = lean_ctor_get_uint64(v_traceState_3283_, sizeof(void*)*1);
v_traces_3297_ = lean_ctor_get(v_traceState_3283_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v_traceState_3283_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3299_ = v_traceState_3283_;
v_isShared_3300_ = v_isSharedCheck_3321_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_traces_3297_);
lean_dec(v_traceState_3283_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3321_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3301_; double v___x_3302_; uint8_t v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3311_; 
v___x_3301_ = lean_box(0);
v___x_3302_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2);
v___x_3303_ = 0;
v___x_3304_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_3305_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3305_, 0, v_cls_3269_);
lean_ctor_set(v___x_3305_, 1, v___x_3301_);
lean_ctor_set(v___x_3305_, 2, v___x_3304_);
lean_ctor_set_float(v___x_3305_, sizeof(void*)*3, v___x_3302_);
lean_ctor_set_float(v___x_3305_, sizeof(void*)*3 + 8, v___x_3302_);
lean_ctor_set_uint8(v___x_3305_, sizeof(void*)*3 + 16, v___x_3303_);
v___x_3306_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_3307_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3305_);
lean_ctor_set(v___x_3307_, 1, v_a_3278_);
lean_ctor_set(v___x_3307_, 2, v___x_3306_);
lean_inc(v_ref_3276_);
v___x_3308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3308_, 0, v_ref_3276_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
v___x_3309_ = l_Lean_PersistentArray_push___redArg(v_traces_3297_, v___x_3308_);
if (v_isShared_3300_ == 0)
{
lean_ctor_set(v___x_3299_, 0, v___x_3309_);
v___x_3311_ = v___x_3299_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___x_3309_);
lean_ctor_set_uint64(v_reuseFailAlloc_3320_, sizeof(void*)*1, v_tid_3296_);
v___x_3311_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
lean_object* v___x_3313_; 
if (v_isShared_3295_ == 0)
{
lean_ctor_set(v___x_3294_, 4, v___x_3311_);
v___x_3313_ = v___x_3294_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_env_3284_);
lean_ctor_set(v_reuseFailAlloc_3319_, 1, v_nextMacroScope_3285_);
lean_ctor_set(v_reuseFailAlloc_3319_, 2, v_ngen_3286_);
lean_ctor_set(v_reuseFailAlloc_3319_, 3, v_auxDeclNGen_3287_);
lean_ctor_set(v_reuseFailAlloc_3319_, 4, v___x_3311_);
lean_ctor_set(v_reuseFailAlloc_3319_, 5, v_cache_3288_);
lean_ctor_set(v_reuseFailAlloc_3319_, 6, v_messages_3289_);
lean_ctor_set(v_reuseFailAlloc_3319_, 7, v_infoState_3290_);
lean_ctor_set(v_reuseFailAlloc_3319_, 8, v_snapshotTasks_3291_);
lean_ctor_set(v_reuseFailAlloc_3319_, 9, v_newDecls_3292_);
v___x_3313_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3317_; 
v___x_3314_ = lean_st_ref_set(v___y_3274_, v___x_3313_);
v___x_3315_ = lean_box(0);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 0, v___x_3315_);
v___x_3317_ = v___x_3280_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3315_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_cls_3324_, lean_object* v_msg_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg(v_cls_3324_, v_msg_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
return v_res_3331_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_keys_3332_, lean_object* v_i_3333_, lean_object* v_k_3334_){
_start:
{
lean_object* v___x_3335_; uint8_t v___x_3336_; 
v___x_3335_ = lean_array_get_size(v_keys_3332_);
v___x_3336_ = lean_nat_dec_lt(v_i_3333_, v___x_3335_);
if (v___x_3336_ == 0)
{
lean_dec(v_i_3333_);
return v___x_3336_;
}
else
{
lean_object* v_k_x27_3337_; uint8_t v___x_3338_; 
v_k_x27_3337_ = lean_array_fget_borrowed(v_keys_3332_, v_i_3333_);
v___x_3338_ = l_Lean_instBEqExtraModUse_beq(v_k_3334_, v_k_x27_3337_);
if (v___x_3338_ == 0)
{
lean_object* v___x_3339_; lean_object* v___x_3340_; 
v___x_3339_ = lean_unsigned_to_nat(1u);
v___x_3340_ = lean_nat_add(v_i_3333_, v___x_3339_);
lean_dec(v_i_3333_);
v_i_3333_ = v___x_3340_;
goto _start;
}
else
{
lean_dec(v_i_3333_);
return v___x_3338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_keys_3342_, lean_object* v_i_3343_, lean_object* v_k_3344_){
_start:
{
uint8_t v_res_3345_; lean_object* v_r_3346_; 
v_res_3345_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_3342_, v_i_3343_, v_k_3344_);
lean_dec_ref(v_k_3344_);
lean_dec_ref(v_keys_3342_);
v_r_3346_ = lean_box(v_res_3345_);
return v_r_3346_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_3347_; size_t v___x_3348_; size_t v___x_3349_; 
v___x_3347_ = ((size_t)5ULL);
v___x_3348_ = ((size_t)1ULL);
v___x_3349_ = lean_usize_shift_left(v___x_3348_, v___x_3347_);
return v___x_3349_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_3350_; size_t v___x_3351_; size_t v___x_3352_; 
v___x_3350_ = ((size_t)1ULL);
v___x_3351_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_3352_ = lean_usize_sub(v___x_3351_, v___x_3350_);
return v___x_3352_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_3353_, size_t v_x_3354_, lean_object* v_x_3355_){
_start:
{
if (lean_obj_tag(v_x_3353_) == 0)
{
lean_object* v_es_3356_; lean_object* v___x_3357_; size_t v___x_3358_; size_t v___x_3359_; size_t v___x_3360_; lean_object* v_j_3361_; lean_object* v___x_3362_; 
v_es_3356_ = lean_ctor_get(v_x_3353_, 0);
v___x_3357_ = lean_box(2);
v___x_3358_ = ((size_t)5ULL);
v___x_3359_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_3360_ = lean_usize_land(v_x_3354_, v___x_3359_);
v_j_3361_ = lean_usize_to_nat(v___x_3360_);
v___x_3362_ = lean_array_get_borrowed(v___x_3357_, v_es_3356_, v_j_3361_);
lean_dec(v_j_3361_);
switch(lean_obj_tag(v___x_3362_))
{
case 0:
{
lean_object* v_key_3363_; uint8_t v___x_3364_; 
v_key_3363_ = lean_ctor_get(v___x_3362_, 0);
v___x_3364_ = l_Lean_instBEqExtraModUse_beq(v_x_3355_, v_key_3363_);
return v___x_3364_;
}
case 1:
{
lean_object* v_node_3365_; size_t v___x_3366_; 
v_node_3365_ = lean_ctor_get(v___x_3362_, 0);
v___x_3366_ = lean_usize_shift_right(v_x_3354_, v___x_3358_);
v_x_3353_ = v_node_3365_;
v_x_3354_ = v___x_3366_;
goto _start;
}
default: 
{
uint8_t v___x_3368_; 
v___x_3368_ = 0;
return v___x_3368_;
}
}
}
else
{
lean_object* v_ks_3369_; lean_object* v___x_3370_; uint8_t v___x_3371_; 
v_ks_3369_ = lean_ctor_get(v_x_3353_, 0);
v___x_3370_ = lean_unsigned_to_nat(0u);
v___x_3371_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ks_3369_, v___x_3370_, v_x_3355_);
return v___x_3371_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_3372_, lean_object* v_x_3373_, lean_object* v_x_3374_){
_start:
{
size_t v_x_12119__boxed_3375_; uint8_t v_res_3376_; lean_object* v_r_3377_; 
v_x_12119__boxed_3375_ = lean_unbox_usize(v_x_3373_);
lean_dec(v_x_3373_);
v_res_3376_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg(v_x_3372_, v_x_12119__boxed_3375_, v_x_3374_);
lean_dec_ref(v_x_3374_);
lean_dec_ref(v_x_3372_);
v_r_3377_ = lean_box(v_res_3376_);
return v_r_3377_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3378_, lean_object* v_x_3379_){
_start:
{
uint64_t v___x_3380_; size_t v___x_3381_; uint8_t v___x_3382_; 
v___x_3380_ = l_Lean_instHashableExtraModUse_hash(v_x_3379_);
v___x_3381_ = lean_uint64_to_usize(v___x_3380_);
v___x_3382_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg(v_x_3378_, v___x_3381_, v_x_3379_);
return v___x_3382_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3383_, lean_object* v_x_3384_){
_start:
{
uint8_t v_res_3385_; lean_object* v_r_3386_; 
v_res_3385_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___redArg(v_x_3383_, v_x_3384_);
lean_dec_ref(v_x_3384_);
lean_dec_ref(v_x_3383_);
v_r_3386_ = lean_box(v_res_3385_);
return v_r_3386_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; lean_object* v___x_3391_; 
v___x_3389_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__1));
v___x_3390_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__0));
v___x_3391_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_3390_, v___x_3389_);
return v___x_3391_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3392_; 
v___x_3392_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3392_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3393_; lean_object* v___x_3394_; 
v___x_3393_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__3);
v___x_3394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3393_);
return v___x_3394_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3395_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4);
v___x_3396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3395_);
lean_ctor_set(v___x_3396_, 1, v___x_3395_);
return v___x_3396_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3397_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4);
v___x_3398_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3398_, 0, v___x_3397_);
lean_ctor_set(v___x_3398_, 1, v___x_3397_);
lean_ctor_set(v___x_3398_, 2, v___x_3397_);
lean_ctor_set(v___x_3398_, 3, v___x_3397_);
lean_ctor_set(v___x_3398_, 4, v___x_3397_);
lean_ctor_set(v___x_3398_, 5, v___x_3397_);
return v___x_3398_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v___x_3403_; lean_object* v___x_3404_; 
v___x_3403_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__9));
v___x_3404_ = l_Lean_stringToMessageData(v___x_3403_);
return v___x_3404_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3406_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__11));
v___x_3407_ = l_Lean_stringToMessageData(v___x_3406_);
return v___x_3407_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__13(void){
_start:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; 
v___x_3408_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_3409_ = l_Lean_stringToMessageData(v___x_3408_);
return v___x_3409_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__14(void){
_start:
{
lean_object* v_cls_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v_cls_3410_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__8));
v___x_3411_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__2));
v___x_3412_ = l_Lean_Name_append(v___x_3411_, v_cls_3410_);
return v___x_3412_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3414_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__15));
v___x_3415_ = l_Lean_stringToMessageData(v___x_3414_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0(lean_object* v_mod_3420_, uint8_t v_isMeta_3421_, lean_object* v_hint_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_){
_start:
{
lean_object* v___x_3430_; lean_object* v_env_3431_; uint8_t v_isExporting_3432_; lean_object* v___x_3433_; lean_object* v_env_3434_; lean_object* v___x_3435_; lean_object* v_entry_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___y_3441_; lean_object* v___y_3442_; lean_object* v___x_3483_; uint8_t v___x_3484_; 
v___x_3430_ = lean_st_ref_get(v___y_3428_);
v_env_3431_ = lean_ctor_get(v___x_3430_, 0);
lean_inc_ref(v_env_3431_);
lean_dec(v___x_3430_);
v_isExporting_3432_ = lean_ctor_get_uint8(v_env_3431_, sizeof(void*)*8);
lean_dec_ref(v_env_3431_);
v___x_3433_ = lean_st_ref_get(v___y_3428_);
v_env_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc_ref(v_env_3434_);
lean_dec(v___x_3433_);
v___x_3435_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__2);
lean_inc(v_mod_3420_);
v_entry_3436_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3436_, 0, v_mod_3420_);
lean_ctor_set_uint8(v_entry_3436_, sizeof(void*)*1, v_isExporting_3432_);
lean_ctor_set_uint8(v_entry_3436_, sizeof(void*)*1 + 1, v_isMeta_3421_);
v___x_3437_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3438_ = lean_box(1);
v___x_3439_ = lean_box(0);
v___x_3483_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3435_, v___x_3437_, v_env_3434_, v___x_3438_, v___x_3439_);
v___x_3484_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___redArg(v___x_3483_, v_entry_3436_);
lean_dec(v___x_3483_);
if (v___x_3484_ == 0)
{
lean_object* v_options_3485_; uint8_t v_hasTrace_3486_; 
v_options_3485_ = lean_ctor_get(v___y_3427_, 2);
v_hasTrace_3486_ = lean_ctor_get_uint8(v_options_3485_, sizeof(void*)*1);
if (v_hasTrace_3486_ == 0)
{
lean_dec(v_hint_3422_);
lean_dec(v_mod_3420_);
v___y_3441_ = v___y_3426_;
v___y_3442_ = v___y_3428_;
goto v___jp_3440_;
}
else
{
lean_object* v_inheritedTraceOptions_3487_; lean_object* v_cls_3488_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___x_3508_; uint8_t v___x_3509_; 
v_inheritedTraceOptions_3487_ = lean_ctor_get(v___y_3427_, 13);
v_cls_3488_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__8));
v___x_3508_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__14);
v___x_3509_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3487_, v_options_3485_, v___x_3508_);
if (v___x_3509_ == 0)
{
lean_dec(v_hint_3422_);
lean_dec(v_mod_3420_);
v___y_3441_ = v___y_3426_;
v___y_3442_ = v___y_3428_;
goto v___jp_3440_;
}
else
{
lean_object* v___x_3510_; lean_object* v___y_3512_; 
v___x_3510_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__16);
if (v_isExporting_3432_ == 0)
{
lean_object* v___x_3519_; 
v___x_3519_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__19));
v___y_3512_ = v___x_3519_;
goto v___jp_3511_;
}
else
{
lean_object* v___x_3520_; 
v___x_3520_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__20));
v___y_3512_ = v___x_3520_;
goto v___jp_3511_;
}
v___jp_3511_:
{
lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; 
lean_inc_ref(v___y_3512_);
v___x_3513_ = l_Lean_stringToMessageData(v___y_3512_);
v___x_3514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3514_, 0, v___x_3510_);
lean_ctor_set(v___x_3514_, 1, v___x_3513_);
v___x_3515_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1);
v___x_3516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3514_);
lean_ctor_set(v___x_3516_, 1, v___x_3515_);
if (v_isMeta_3421_ == 0)
{
lean_object* v___x_3517_; 
v___x_3517_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__17));
v___y_3495_ = v___x_3516_;
v___y_3496_ = v___x_3517_;
goto v___jp_3494_;
}
else
{
lean_object* v___x_3518_; 
v___x_3518_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__18));
v___y_3495_ = v___x_3516_;
v___y_3496_ = v___x_3518_;
goto v___jp_3494_;
}
}
}
v___jp_3489_:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3492_, 0, v___y_3490_);
lean_ctor_set(v___x_3492_, 1, v___y_3491_);
v___x_3493_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg(v_cls_3488_, v___x_3492_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_dec_ref(v___x_3493_);
v___y_3441_ = v___y_3426_;
v___y_3442_ = v___y_3428_;
goto v___jp_3440_;
}
else
{
lean_dec_ref(v_entry_3436_);
return v___x_3493_;
}
}
v___jp_3494_:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; uint8_t v___x_3503_; 
lean_inc_ref(v___y_3496_);
v___x_3497_ = l_Lean_stringToMessageData(v___y_3496_);
v___x_3498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3498_, 0, v___y_3495_);
lean_ctor_set(v___x_3498_, 1, v___x_3497_);
v___x_3499_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__10);
v___x_3500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3500_, 0, v___x_3498_);
lean_ctor_set(v___x_3500_, 1, v___x_3499_);
v___x_3501_ = l_Lean_MessageData_ofName(v_mod_3420_);
v___x_3502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3500_);
lean_ctor_set(v___x_3502_, 1, v___x_3501_);
v___x_3503_ = l_Lean_Name_isAnonymous(v_hint_3422_);
if (v___x_3503_ == 0)
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3504_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__12);
v___x_3505_ = l_Lean_MessageData_ofName(v_hint_3422_);
v___x_3506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3506_, 0, v___x_3504_);
lean_ctor_set(v___x_3506_, 1, v___x_3505_);
v___y_3490_ = v___x_3502_;
v___y_3491_ = v___x_3506_;
goto v___jp_3489_;
}
else
{
lean_object* v___x_3507_; 
lean_dec(v_hint_3422_);
v___x_3507_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__13);
v___y_3490_ = v___x_3502_;
v___y_3491_ = v___x_3507_;
goto v___jp_3489_;
}
}
}
}
else
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
lean_dec_ref(v_entry_3436_);
lean_dec(v_hint_3422_);
lean_dec(v_mod_3420_);
v___x_3521_ = lean_box(0);
v___x_3522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3521_);
return v___x_3522_;
}
v___jp_3440_:
{
lean_object* v___x_3443_; lean_object* v_toEnvExtension_3444_; lean_object* v_env_3445_; lean_object* v_nextMacroScope_3446_; lean_object* v_ngen_3447_; lean_object* v_auxDeclNGen_3448_; lean_object* v_traceState_3449_; lean_object* v_messages_3450_; lean_object* v_infoState_3451_; lean_object* v_snapshotTasks_3452_; lean_object* v_newDecls_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3481_; 
v___x_3443_ = lean_st_ref_take(v___y_3442_);
v_toEnvExtension_3444_ = lean_ctor_get(v___x_3437_, 0);
v_env_3445_ = lean_ctor_get(v___x_3443_, 0);
v_nextMacroScope_3446_ = lean_ctor_get(v___x_3443_, 1);
v_ngen_3447_ = lean_ctor_get(v___x_3443_, 2);
v_auxDeclNGen_3448_ = lean_ctor_get(v___x_3443_, 3);
v_traceState_3449_ = lean_ctor_get(v___x_3443_, 4);
v_messages_3450_ = lean_ctor_get(v___x_3443_, 6);
v_infoState_3451_ = lean_ctor_get(v___x_3443_, 7);
v_snapshotTasks_3452_ = lean_ctor_get(v___x_3443_, 8);
v_newDecls_3453_ = lean_ctor_get(v___x_3443_, 9);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3481_ == 0)
{
lean_object* v_unused_3482_; 
v_unused_3482_ = lean_ctor_get(v___x_3443_, 5);
lean_dec(v_unused_3482_);
v___x_3455_ = v___x_3443_;
v_isShared_3456_ = v_isSharedCheck_3481_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_newDecls_3453_);
lean_inc(v_snapshotTasks_3452_);
lean_inc(v_infoState_3451_);
lean_inc(v_messages_3450_);
lean_inc(v_traceState_3449_);
lean_inc(v_auxDeclNGen_3448_);
lean_inc(v_ngen_3447_);
lean_inc(v_nextMacroScope_3446_);
lean_inc(v_env_3445_);
lean_dec(v___x_3443_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3481_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v_asyncMode_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3461_; 
v_asyncMode_3457_ = lean_ctor_get(v_toEnvExtension_3444_, 2);
v___x_3458_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3437_, v_env_3445_, v_entry_3436_, v_asyncMode_3457_, v___x_3439_);
v___x_3459_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__5);
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 5, v___x_3459_);
lean_ctor_set(v___x_3455_, 0, v___x_3458_);
v___x_3461_ = v___x_3455_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v___x_3458_);
lean_ctor_set(v_reuseFailAlloc_3480_, 1, v_nextMacroScope_3446_);
lean_ctor_set(v_reuseFailAlloc_3480_, 2, v_ngen_3447_);
lean_ctor_set(v_reuseFailAlloc_3480_, 3, v_auxDeclNGen_3448_);
lean_ctor_set(v_reuseFailAlloc_3480_, 4, v_traceState_3449_);
lean_ctor_set(v_reuseFailAlloc_3480_, 5, v___x_3459_);
lean_ctor_set(v_reuseFailAlloc_3480_, 6, v_messages_3450_);
lean_ctor_set(v_reuseFailAlloc_3480_, 7, v_infoState_3451_);
lean_ctor_set(v_reuseFailAlloc_3480_, 8, v_snapshotTasks_3452_);
lean_ctor_set(v_reuseFailAlloc_3480_, 9, v_newDecls_3453_);
v___x_3461_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v_mctx_3464_; lean_object* v_zetaDeltaFVarIds_3465_; lean_object* v_postponed_3466_; lean_object* v_diag_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3478_; 
v___x_3462_ = lean_st_ref_set(v___y_3442_, v___x_3461_);
v___x_3463_ = lean_st_ref_take(v___y_3441_);
v_mctx_3464_ = lean_ctor_get(v___x_3463_, 0);
v_zetaDeltaFVarIds_3465_ = lean_ctor_get(v___x_3463_, 2);
v_postponed_3466_ = lean_ctor_get(v___x_3463_, 3);
v_diag_3467_ = lean_ctor_get(v___x_3463_, 4);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3478_ == 0)
{
lean_object* v_unused_3479_; 
v_unused_3479_ = lean_ctor_get(v___x_3463_, 1);
lean_dec(v_unused_3479_);
v___x_3469_ = v___x_3463_;
v_isShared_3470_ = v_isSharedCheck_3478_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_diag_3467_);
lean_inc(v_postponed_3466_);
lean_inc(v_zetaDeltaFVarIds_3465_);
lean_inc(v_mctx_3464_);
lean_dec(v___x_3463_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3478_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3471_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__6);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 1, v___x_3471_);
v___x_3473_ = v___x_3469_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_mctx_3464_);
lean_ctor_set(v_reuseFailAlloc_3477_, 1, v___x_3471_);
lean_ctor_set(v_reuseFailAlloc_3477_, 2, v_zetaDeltaFVarIds_3465_);
lean_ctor_set(v_reuseFailAlloc_3477_, 3, v_postponed_3466_);
lean_ctor_set(v_reuseFailAlloc_3477_, 4, v_diag_3467_);
v___x_3473_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; 
v___x_3474_ = lean_st_ref_set(v___y_3441_, v___x_3473_);
v___x_3475_ = lean_box(0);
v___x_3476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3475_);
return v___x_3476_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___boxed(lean_object* v_mod_3523_, lean_object* v_isMeta_3524_, lean_object* v_hint_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
uint8_t v_isMeta_boxed_3533_; lean_object* v_res_3534_; 
v_isMeta_boxed_3533_ = lean_unbox(v_isMeta_3524_);
v_res_3534_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0(v_mod_3523_, v_isMeta_boxed_3533_, v_hint_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_);
lean_dec(v___y_3531_);
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec_ref(v___y_3528_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
return v_res_3534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__1(lean_object* v___x_3535_, lean_object* v_declName_3536_, lean_object* v_as_3537_, size_t v_sz_3538_, size_t v_i_3539_, lean_object* v_b_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
uint8_t v___x_3548_; 
v___x_3548_ = lean_usize_dec_lt(v_i_3539_, v_sz_3538_);
if (v___x_3548_ == 0)
{
lean_object* v___x_3549_; 
lean_dec(v_declName_3536_);
v___x_3549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3549_, 0, v_b_3540_);
return v___x_3549_;
}
else
{
lean_object* v___x_3550_; lean_object* v_modules_3551_; lean_object* v___x_3552_; lean_object* v_a_3553_; lean_object* v___x_3554_; lean_object* v_toImport_3555_; lean_object* v_module_3556_; uint8_t v___x_3557_; lean_object* v___x_3558_; 
v___x_3550_ = l_Lean_Environment_header(v___x_3535_);
v_modules_3551_ = lean_ctor_get(v___x_3550_, 3);
lean_inc_ref(v_modules_3551_);
lean_dec_ref(v___x_3550_);
v___x_3552_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3553_ = lean_array_uget_borrowed(v_as_3537_, v_i_3539_);
v___x_3554_ = lean_array_get(v___x_3552_, v_modules_3551_, v_a_3553_);
lean_dec_ref(v_modules_3551_);
v_toImport_3555_ = lean_ctor_get(v___x_3554_, 0);
lean_inc_ref(v_toImport_3555_);
lean_dec(v___x_3554_);
v_module_3556_ = lean_ctor_get(v_toImport_3555_, 0);
lean_inc(v_module_3556_);
lean_dec_ref(v_toImport_3555_);
v___x_3557_ = 0;
lean_inc(v_declName_3536_);
v___x_3558_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0(v_module_3556_, v___x_3557_, v_declName_3536_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v___x_3559_; size_t v___x_3560_; size_t v___x_3561_; 
lean_dec_ref(v___x_3558_);
v___x_3559_ = lean_box(0);
v___x_3560_ = ((size_t)1ULL);
v___x_3561_ = lean_usize_add(v_i_3539_, v___x_3560_);
v_i_3539_ = v___x_3561_;
v_b_3540_ = v___x_3559_;
goto _start;
}
else
{
lean_dec(v_declName_3536_);
return v___x_3558_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__1___boxed(lean_object* v___x_3563_, lean_object* v_declName_3564_, lean_object* v_as_3565_, lean_object* v_sz_3566_, lean_object* v_i_3567_, lean_object* v_b_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
size_t v_sz_boxed_3576_; size_t v_i_boxed_3577_; lean_object* v_res_3578_; 
v_sz_boxed_3576_ = lean_unbox_usize(v_sz_3566_);
lean_dec(v_sz_3566_);
v_i_boxed_3577_ = lean_unbox_usize(v_i_3567_);
lean_dec(v_i_3567_);
v_res_3578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__1(v___x_3563_, v_declName_3564_, v_as_3565_, v_sz_boxed_3576_, v_i_boxed_3577_, v_b_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
lean_dec(v___y_3570_);
lean_dec_ref(v___y_3569_);
lean_dec_ref(v_as_3565_);
lean_dec_ref(v___x_3563_);
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__5___redArg(lean_object* v_a_3579_, lean_object* v_x_3580_){
_start:
{
if (lean_obj_tag(v_x_3580_) == 0)
{
lean_object* v___x_3581_; 
v___x_3581_ = lean_box(0);
return v___x_3581_;
}
else
{
lean_object* v_key_3582_; lean_object* v_value_3583_; lean_object* v_tail_3584_; uint8_t v___x_3585_; 
v_key_3582_ = lean_ctor_get(v_x_3580_, 0);
v_value_3583_ = lean_ctor_get(v_x_3580_, 1);
v_tail_3584_ = lean_ctor_get(v_x_3580_, 2);
v___x_3585_ = lean_name_eq(v_key_3582_, v_a_3579_);
if (v___x_3585_ == 0)
{
v_x_3580_ = v_tail_3584_;
goto _start;
}
else
{
lean_object* v___x_3587_; 
lean_inc(v_value_3583_);
v___x_3587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3587_, 0, v_value_3583_);
return v___x_3587_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_3588_, lean_object* v_x_3589_){
_start:
{
lean_object* v_res_3590_; 
v_res_3590_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__5___redArg(v_a_3588_, v_x_3589_);
lean_dec(v_x_3589_);
lean_dec(v_a_3588_);
return v_res_3590_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3591_; uint64_t v___x_3592_; 
v___x_3591_ = lean_unsigned_to_nat(1723u);
v___x_3592_ = lean_uint64_of_nat(v___x_3591_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg(lean_object* v_m_3593_, lean_object* v_a_3594_){
_start:
{
lean_object* v_buckets_3595_; lean_object* v___x_3596_; uint64_t v___y_3598_; 
v_buckets_3595_ = lean_ctor_get(v_m_3593_, 1);
v___x_3596_ = lean_array_get_size(v_buckets_3595_);
if (lean_obj_tag(v_a_3594_) == 0)
{
uint64_t v___x_3612_; 
v___x_3612_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg___closed__0);
v___y_3598_ = v___x_3612_;
goto v___jp_3597_;
}
else
{
uint64_t v_hash_3613_; 
v_hash_3613_ = lean_ctor_get_uint64(v_a_3594_, sizeof(void*)*2);
v___y_3598_ = v_hash_3613_;
goto v___jp_3597_;
}
v___jp_3597_:
{
uint64_t v___x_3599_; uint64_t v___x_3600_; uint64_t v_fold_3601_; uint64_t v___x_3602_; uint64_t v___x_3603_; uint64_t v___x_3604_; size_t v___x_3605_; size_t v___x_3606_; size_t v___x_3607_; size_t v___x_3608_; size_t v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; 
v___x_3599_ = 32ULL;
v___x_3600_ = lean_uint64_shift_right(v___y_3598_, v___x_3599_);
v_fold_3601_ = lean_uint64_xor(v___y_3598_, v___x_3600_);
v___x_3602_ = 16ULL;
v___x_3603_ = lean_uint64_shift_right(v_fold_3601_, v___x_3602_);
v___x_3604_ = lean_uint64_xor(v_fold_3601_, v___x_3603_);
v___x_3605_ = lean_uint64_to_usize(v___x_3604_);
v___x_3606_ = lean_usize_of_nat(v___x_3596_);
v___x_3607_ = ((size_t)1ULL);
v___x_3608_ = lean_usize_sub(v___x_3606_, v___x_3607_);
v___x_3609_ = lean_usize_land(v___x_3605_, v___x_3608_);
v___x_3610_ = lean_array_uget_borrowed(v_buckets_3595_, v___x_3609_);
v___x_3611_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__5___redArg(v_a_3594_, v___x_3610_);
return v___x_3611_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg___boxed(lean_object* v_m_3614_, lean_object* v_a_3615_){
_start:
{
lean_object* v_res_3616_; 
v_res_3616_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg(v_m_3614_, v_a_3615_);
lean_dec(v_a_3615_);
lean_dec_ref(v_m_3614_);
return v_res_3616_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___x_3619_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__1));
v___x_3620_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__0));
v___x_3621_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_3620_, v___x_3619_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0(lean_object* v_declName_3624_, uint8_t v_isMeta_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
lean_object* v___x_3633_; lean_object* v_env_3637_; lean_object* v___y_3639_; lean_object* v___x_3652_; 
v___x_3633_ = lean_st_ref_get(v___y_3631_);
v_env_3637_ = lean_ctor_get(v___x_3633_, 0);
lean_inc_ref(v_env_3637_);
lean_dec(v___x_3633_);
v___x_3652_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3637_, v_declName_3624_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_dec_ref(v_env_3637_);
lean_dec(v_declName_3624_);
goto v___jp_3634_;
}
else
{
lean_object* v_val_3653_; lean_object* v___x_3654_; lean_object* v_modules_3655_; lean_object* v___x_3656_; uint8_t v___x_3657_; 
v_val_3653_ = lean_ctor_get(v___x_3652_, 0);
lean_inc(v_val_3653_);
lean_dec_ref(v___x_3652_);
v___x_3654_ = l_Lean_Environment_header(v_env_3637_);
v_modules_3655_ = lean_ctor_get(v___x_3654_, 3);
lean_inc_ref(v_modules_3655_);
lean_dec_ref(v___x_3654_);
v___x_3656_ = lean_array_get_size(v_modules_3655_);
v___x_3657_ = lean_nat_dec_lt(v_val_3653_, v___x_3656_);
if (v___x_3657_ == 0)
{
lean_dec_ref(v_modules_3655_);
lean_dec(v_val_3653_);
lean_dec_ref(v_env_3637_);
lean_dec(v_declName_3624_);
goto v___jp_3634_;
}
else
{
lean_object* v___x_3658_; lean_object* v_env_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; uint8_t v___y_3663_; 
v___x_3658_ = lean_st_ref_get(v___y_3631_);
v_env_3659_ = lean_ctor_get(v___x_3658_, 0);
lean_inc_ref(v_env_3659_);
lean_dec(v___x_3658_);
v___x_3660_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__2);
v___x_3661_ = lean_array_fget(v_modules_3655_, v_val_3653_);
lean_dec(v_val_3653_);
lean_dec_ref(v_modules_3655_);
if (v_isMeta_3625_ == 0)
{
lean_dec_ref(v_env_3659_);
v___y_3663_ = v_isMeta_3625_;
goto v___jp_3662_;
}
else
{
uint8_t v___x_3674_; 
lean_inc(v_declName_3624_);
v___x_3674_ = l_Lean_isMarkedMeta(v_env_3659_, v_declName_3624_);
if (v___x_3674_ == 0)
{
v___y_3663_ = v_isMeta_3625_;
goto v___jp_3662_;
}
else
{
uint8_t v___x_3675_; 
v___x_3675_ = 0;
v___y_3663_ = v___x_3675_;
goto v___jp_3662_;
}
}
v___jp_3662_:
{
lean_object* v_toImport_3664_; lean_object* v_module_3665_; lean_object* v___x_3666_; 
v_toImport_3664_ = lean_ctor_get(v___x_3661_, 0);
lean_inc_ref(v_toImport_3664_);
lean_dec(v___x_3661_);
v_module_3665_ = lean_ctor_get(v_toImport_3664_, 0);
lean_inc(v_module_3665_);
lean_dec_ref(v_toImport_3664_);
lean_inc(v_declName_3624_);
v___x_3666_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0(v_module_3665_, v___y_3663_, v_declName_3624_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
lean_dec_ref(v___x_3666_);
v___x_3667_ = l_Lean_indirectModUseExt;
v___x_3668_ = lean_box(1);
v___x_3669_ = lean_box(0);
lean_inc_ref(v_env_3637_);
v___x_3670_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3660_, v___x_3667_, v_env_3637_, v___x_3668_, v___x_3669_);
v___x_3671_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg(v___x_3670_, v_declName_3624_);
lean_dec(v___x_3670_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v___x_3672_; 
v___x_3672_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__3));
v___y_3639_ = v___x_3672_;
goto v___jp_3638_;
}
else
{
lean_object* v_val_3673_; 
v_val_3673_ = lean_ctor_get(v___x_3671_, 0);
lean_inc(v_val_3673_);
lean_dec_ref(v___x_3671_);
v___y_3639_ = v_val_3673_;
goto v___jp_3638_;
}
}
else
{
lean_dec_ref(v_env_3637_);
lean_dec(v_declName_3624_);
return v___x_3666_;
}
}
}
}
v___jp_3634_:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = lean_box(0);
v___x_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3635_);
return v___x_3636_;
}
v___jp_3638_:
{
lean_object* v___x_3640_; size_t v_sz_3641_; size_t v___x_3642_; lean_object* v___x_3643_; 
v___x_3640_ = lean_box(0);
v_sz_3641_ = lean_array_size(v___y_3639_);
v___x_3642_ = ((size_t)0ULL);
v___x_3643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__1(v_env_3637_, v_declName_3624_, v___y_3639_, v_sz_3641_, v___x_3642_, v___x_3640_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_);
lean_dec_ref(v___y_3639_);
lean_dec_ref(v_env_3637_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3650_; 
v_isSharedCheck_3650_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3650_ == 0)
{
lean_object* v_unused_3651_; 
v_unused_3651_ = lean_ctor_get(v___x_3643_, 0);
lean_dec(v_unused_3651_);
v___x_3645_ = v___x_3643_;
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
else
{
lean_dec(v___x_3643_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3650_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3648_; 
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 0, v___x_3640_);
v___x_3648_ = v___x_3645_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3649_; 
v_reuseFailAlloc_3649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3649_, 0, v___x_3640_);
v___x_3648_ = v_reuseFailAlloc_3649_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
return v___x_3648_;
}
}
}
else
{
return v___x_3643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___boxed(lean_object* v_declName_3676_, lean_object* v_isMeta_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_, lean_object* v___y_3682_, lean_object* v___y_3683_, lean_object* v___y_3684_){
_start:
{
uint8_t v_isMeta_boxed_3685_; lean_object* v_res_3686_; 
v_isMeta_boxed_3685_ = lean_unbox(v_isMeta_3677_);
v_res_3686_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0(v_declName_3676_, v_isMeta_boxed_3685_, v___y_3678_, v___y_3679_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_);
lean_dec(v___y_3683_);
lean_dec_ref(v___y_3682_);
lean_dec(v___y_3681_);
lean_dec_ref(v___y_3680_);
lean_dec(v___y_3679_);
lean_dec_ref(v___y_3678_);
return v_res_3686_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__1(void){
_start:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3688_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__0));
v___x_3689_ = l_Lean_stringToMessageData(v___x_3688_);
return v___x_3689_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__3(void){
_start:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3691_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__2));
v___x_3692_ = l_Lean_stringToMessageData(v___x_3691_);
return v___x_3692_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__5(void){
_start:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; 
v___x_3694_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__4));
v___x_3695_ = l_Lean_stringToMessageData(v___x_3694_);
return v___x_3695_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__7(void){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3697_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__6));
v___x_3698_ = l_Lean_stringToMessageData(v___x_3697_);
return v___x_3698_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__8(void){
_start:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; 
v___x_3699_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_));
v___x_3700_ = l_Lean_MessageData_ofName(v___x_3699_);
return v___x_3700_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__9(void){
_start:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; 
v___x_3701_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__8, &l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__8);
v___x_3702_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__7, &l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__7);
v___x_3703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3702_);
lean_ctor_set(v___x_3703_, 1, v___x_3701_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg(lean_object* v_optConfig_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_){
_start:
{
lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; uint8_t v___y_3730_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v___y_3747_; uint8_t v_recover_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; uint8_t v___x_3757_; uint8_t v___x_3758_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v___y_3765_; 
v_recover_3752_ = lean_ctor_get_uint8(v_a_3712_, sizeof(void*)*1);
lean_inc(v_optConfig_3711_);
v___x_3753_ = l_Lean_Parser_Tactic_getConfigItems(v_optConfig_3711_);
v___x_3754_ = l_Lean_Elab_Tactic_mkConfigItemViews(v___x_3753_);
v___x_3755_ = lean_array_get_size(v___x_3754_);
v___x_3756_ = lean_unsigned_to_nat(0u);
v___x_3757_ = lean_nat_dec_eq(v___x_3755_, v___x_3756_);
v___x_3758_ = 1;
if (v___x_3757_ == 0)
{
lean_object* v___x_3810_; lean_object* v_fileName_3811_; lean_object* v_fileMap_3812_; lean_object* v_options_3813_; lean_object* v_currRecDepth_3814_; lean_object* v_maxRecDepth_3815_; lean_object* v_ref_3816_; lean_object* v_currNamespace_3817_; lean_object* v_openDecls_3818_; lean_object* v_initHeartbeats_3819_; lean_object* v_maxHeartbeats_3820_; lean_object* v_quotContext_3821_; lean_object* v_currMacroScope_3822_; uint8_t v_diag_3823_; lean_object* v_cancelTk_x3f_3824_; uint8_t v_suppressElabErrors_3825_; lean_object* v_inheritedTraceOptions_3826_; lean_object* v_env_3827_; lean_object* v_ref_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; uint8_t v___x_3831_; 
v___x_3810_ = lean_st_ref_get(v_a_3718_);
v_fileName_3811_ = lean_ctor_get(v_a_3717_, 0);
v_fileMap_3812_ = lean_ctor_get(v_a_3717_, 1);
v_options_3813_ = lean_ctor_get(v_a_3717_, 2);
v_currRecDepth_3814_ = lean_ctor_get(v_a_3717_, 3);
v_maxRecDepth_3815_ = lean_ctor_get(v_a_3717_, 4);
v_ref_3816_ = lean_ctor_get(v_a_3717_, 5);
v_currNamespace_3817_ = lean_ctor_get(v_a_3717_, 6);
v_openDecls_3818_ = lean_ctor_get(v_a_3717_, 7);
v_initHeartbeats_3819_ = lean_ctor_get(v_a_3717_, 8);
v_maxHeartbeats_3820_ = lean_ctor_get(v_a_3717_, 9);
v_quotContext_3821_ = lean_ctor_get(v_a_3717_, 10);
v_currMacroScope_3822_ = lean_ctor_get(v_a_3717_, 11);
v_diag_3823_ = lean_ctor_get_uint8(v_a_3717_, sizeof(void*)*14);
v_cancelTk_x3f_3824_ = lean_ctor_get(v_a_3717_, 12);
v_suppressElabErrors_3825_ = lean_ctor_get_uint8(v_a_3717_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3826_ = lean_ctor_get(v_a_3717_, 13);
v_env_3827_ = lean_ctor_get(v___x_3810_, 0);
lean_inc_ref(v_env_3827_);
lean_dec(v___x_3810_);
v_ref_3828_ = l_Lean_replaceRef(v_optConfig_3711_, v_ref_3816_);
lean_dec(v_optConfig_3711_);
lean_inc_ref(v_inheritedTraceOptions_3826_);
lean_inc(v_cancelTk_x3f_3824_);
lean_inc(v_currMacroScope_3822_);
lean_inc(v_quotContext_3821_);
lean_inc(v_maxHeartbeats_3820_);
lean_inc(v_initHeartbeats_3819_);
lean_inc(v_openDecls_3818_);
lean_inc(v_currNamespace_3817_);
lean_inc(v_maxRecDepth_3815_);
lean_inc(v_currRecDepth_3814_);
lean_inc_ref(v_options_3813_);
lean_inc_ref(v_fileMap_3812_);
lean_inc_ref(v_fileName_3811_);
v___x_3829_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3829_, 0, v_fileName_3811_);
lean_ctor_set(v___x_3829_, 1, v_fileMap_3812_);
lean_ctor_set(v___x_3829_, 2, v_options_3813_);
lean_ctor_set(v___x_3829_, 3, v_currRecDepth_3814_);
lean_ctor_set(v___x_3829_, 4, v_maxRecDepth_3815_);
lean_ctor_set(v___x_3829_, 5, v_ref_3828_);
lean_ctor_set(v___x_3829_, 6, v_currNamespace_3817_);
lean_ctor_set(v___x_3829_, 7, v_openDecls_3818_);
lean_ctor_set(v___x_3829_, 8, v_initHeartbeats_3819_);
lean_ctor_set(v___x_3829_, 9, v_maxHeartbeats_3820_);
lean_ctor_set(v___x_3829_, 10, v_quotContext_3821_);
lean_ctor_set(v___x_3829_, 11, v_currMacroScope_3822_);
lean_ctor_set(v___x_3829_, 12, v_cancelTk_x3f_3824_);
lean_ctor_set(v___x_3829_, 13, v_inheritedTraceOptions_3826_);
lean_ctor_set_uint8(v___x_3829_, sizeof(void*)*14, v_diag_3823_);
lean_ctor_set_uint8(v___x_3829_, sizeof(void*)*14 + 1, v_suppressElabErrors_3825_);
v___x_3830_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_));
v___x_3831_ = l_Lean_Environment_contains(v_env_3827_, v___x_3830_, v___x_3758_);
if (v___x_3831_ == 0)
{
lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
lean_dec_ref(v___x_3754_);
v___x_3832_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__9, &l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__9);
v___x_3833_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg(v___x_3832_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v___x_3829_, v_a_3718_);
lean_dec_ref(v___x_3829_);
v_a_3834_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3836_ = v___x_3833_;
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3833_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
if (v_isShared_3837_ == 0)
{
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3834_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
else
{
v___y_3760_ = v_a_3713_;
v___y_3761_ = v_a_3714_;
v___y_3762_ = v_a_3715_;
v___y_3763_ = v_a_3716_;
v___y_3764_ = v___x_3829_;
v___y_3765_ = v_a_3718_;
goto v___jp_3759_;
}
}
else
{
lean_object* v___x_3842_; lean_object* v___x_3843_; 
lean_dec_ref(v___x_3754_);
lean_dec(v_optConfig_3711_);
v___x_3842_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__10));
v___x_3843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3842_);
return v___x_3843_;
}
v___jp_3720_:
{
if (v___y_3730_ == 0)
{
lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
lean_dec_ref(v___y_3729_);
v___x_3731_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__1, &l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__1);
v___x_3732_ = l_Lean_MessageData_ofExpr(v___y_3728_);
v___x_3733_ = l_Lean_indentD(v___x_3732_);
v___x_3734_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3734_, 0, v___x_3731_);
lean_ctor_set(v___x_3734_, 1, v___x_3733_);
v___x_3735_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__3, &l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__3);
v___x_3736_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3734_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
v___x_3737_ = l_Lean_Exception_toMessageData(v___y_3727_);
v___x_3738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3736_);
lean_ctor_set(v___x_3738_, 1, v___x_3737_);
v___x_3739_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg(v___x_3738_, v___y_3723_, v___y_3722_, v___y_3725_, v___y_3726_, v___y_3721_, v___y_3724_);
lean_dec_ref(v___y_3721_);
return v___x_3739_;
}
else
{
lean_dec_ref(v___y_3728_);
lean_dec_ref(v___y_3727_);
lean_dec_ref(v___y_3721_);
return v___y_3729_;
}
}
v___jp_3740_:
{
lean_object* v___x_3748_; 
lean_inc_ref(v___y_3741_);
v___x_3748_ = l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(v___y_3741_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_dec_ref(v___y_3746_);
lean_dec_ref(v___y_3741_);
return v___x_3748_;
}
else
{
lean_object* v_a_3749_; uint8_t v___x_3750_; 
v_a_3749_ = lean_ctor_get(v___x_3748_, 0);
lean_inc(v_a_3749_);
v___x_3750_ = l_Lean_Exception_isInterrupt(v_a_3749_);
if (v___x_3750_ == 0)
{
uint8_t v___x_3751_; 
lean_inc(v_a_3749_);
v___x_3751_ = l_Lean_Exception_isRuntime(v_a_3749_);
v___y_3721_ = v___y_3746_;
v___y_3722_ = v___y_3743_;
v___y_3723_ = v___y_3742_;
v___y_3724_ = v___y_3747_;
v___y_3725_ = v___y_3744_;
v___y_3726_ = v___y_3745_;
v___y_3727_ = v_a_3749_;
v___y_3728_ = v___y_3741_;
v___y_3729_ = v___x_3748_;
v___y_3730_ = v___x_3751_;
goto v___jp_3720_;
}
else
{
v___y_3721_ = v___y_3746_;
v___y_3722_ = v___y_3743_;
v___y_3723_ = v___y_3742_;
v___y_3724_ = v___y_3747_;
v___y_3725_ = v___y_3744_;
v___y_3726_ = v___y_3745_;
v___y_3727_ = v_a_3749_;
v___y_3728_ = v___y_3741_;
v___y_3729_ = v___x_3748_;
v___y_3730_ = v___x_3750_;
goto v___jp_3720_;
}
}
}
v___jp_3759_:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; 
v___x_3766_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_));
v___x_3767_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0(v___x_3766_, v___x_3758_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_object* v___x_3768_; 
lean_dec_ref(v___x_3767_);
v___x_3768_ = l_Lean_Elab_Tactic_elabConfig(v_recover_3752_, v___x_3766_, v___x_3754_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
if (lean_obj_tag(v___x_3768_) == 0)
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3793_; 
v_a_3769_ = lean_ctor_get(v___x_3768_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3771_ = v___x_3768_;
v_isShared_3772_ = v_isSharedCheck_3793_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3768_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3793_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
uint8_t v___x_3773_; 
v___x_3773_ = l_Lean_Expr_hasSyntheticSorry(v_a_3769_);
if (v___x_3773_ == 0)
{
uint8_t v___x_3774_; 
lean_del_object(v___x_3771_);
v___x_3774_ = l_Lean_Expr_hasSorry(v_a_3769_);
if (v___x_3774_ == 0)
{
v___y_3741_ = v_a_3769_;
v___y_3742_ = v___y_3760_;
v___y_3743_ = v___y_3761_;
v___y_3744_ = v___y_3762_;
v___y_3745_ = v___y_3763_;
v___y_3746_ = v___y_3764_;
v___y_3747_ = v___y_3765_;
goto v___jp_3740_;
}
else
{
lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
lean_dec(v_a_3769_);
v___x_3775_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__5, &l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__5);
v___x_3776_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg(v___x_3775_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
lean_dec_ref(v___y_3764_);
v_a_3777_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3776_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3776_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
else
{
lean_object* v___x_3785_; lean_object* v___x_3786_; uint8_t v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3791_; 
lean_dec(v_a_3769_);
lean_dec_ref(v___y_3764_);
v___x_3785_ = lean_unsigned_to_nat(100000u);
v___x_3786_ = lean_unsigned_to_nat(2u);
v___x_3787_ = 0;
v___x_3788_ = lean_box(0);
v___x_3789_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_3789_, 0, v___x_3785_);
lean_ctor_set(v___x_3789_, 1, v___x_3786_);
lean_ctor_set(v___x_3789_, 2, v___x_3788_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3, v___x_3757_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 1, v___x_3758_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 2, v___x_3757_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 3, v___x_3757_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 4, v___x_3757_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 5, v___x_3757_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 6, v___x_3787_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 7, v___x_3757_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 8, v___x_3757_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 9, v___x_3757_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 10, v___x_3757_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 11, v___x_3757_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 12, v___x_3758_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 13, v___x_3758_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 14, v___x_3757_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 15, v___x_3757_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 16, v___x_3757_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 17, v___x_3758_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 18, v___x_3758_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 19, v___x_3758_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 20, v___x_3758_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 21, v___x_3758_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 22, v___x_3758_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 23, v___x_3758_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 24, v___x_3758_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 25, v___x_3758_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 26, v___x_3757_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 27, v___x_3757_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*3 + 28, v___x_3757_);
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 0, v___x_3789_);
v___x_3791_ = v___x_3771_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v___x_3789_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
else
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
lean_dec_ref(v___y_3764_);
v_a_3794_ = lean_ctor_get(v___x_3768_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3796_ = v___x_3768_;
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3768_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3799_; 
if (v_isShared_3797_ == 0)
{
v___x_3799_ = v___x_3796_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3794_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
else
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3809_; 
lean_dec_ref(v___y_3764_);
lean_dec_ref(v___x_3754_);
v_a_3802_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3804_ = v___x_3767_;
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3767_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
if (v_isShared_3805_ == 0)
{
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___boxed(lean_object* v_optConfig_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_){
_start:
{
lean_object* v_res_3853_; 
v_res_3853_ = l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg(v_optConfig_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_);
lean_dec(v_a_3851_);
lean_dec_ref(v_a_3850_);
lean_dec(v_a_3849_);
lean_dec_ref(v_a_3848_);
lean_dec(v_a_3847_);
lean_dec_ref(v_a_3846_);
lean_dec_ref(v_a_3845_);
return v_res_3853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig(lean_object* v_optConfig_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_){
_start:
{
lean_object* v___x_3864_; 
v___x_3864_ = l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg(v_optConfig_3854_, v_a_3855_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___boxed(lean_object* v_optConfig_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_){
_start:
{
lean_object* v_res_3875_; 
v_res_3875_ = l_Lean_Elab_Tactic_NormCast_elabNormCastConfig(v_optConfig_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_);
lean_dec(v_a_3873_);
lean_dec_ref(v_a_3872_);
lean_dec(v_a_3871_);
lean_dec_ref(v_a_3870_);
lean_dec(v_a_3869_);
lean_dec_ref(v_a_3868_);
lean_dec(v_a_3867_);
lean_dec_ref(v_a_3866_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1(lean_object* v_00_u03b1_3876_, lean_object* v_msg_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_){
_start:
{
lean_object* v___x_3885_; 
v___x_3885_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg(v_msg_3877_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_);
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___boxed(lean_object* v_00_u03b1_3886_, lean_object* v_msg_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_){
_start:
{
lean_object* v_res_3895_; 
v_res_3895_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1(v_00_u03b1_3886_, v_msg_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_);
lean_dec(v___y_3893_);
lean_dec_ref(v___y_3892_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v___y_3888_);
return v_res_3895_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2(lean_object* v_00_u03b2_3896_, lean_object* v_m_3897_, lean_object* v_a_3898_){
_start:
{
lean_object* v___x_3899_; 
v___x_3899_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg(v_m_3897_, v_a_3898_);
return v___x_3899_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3900_, lean_object* v_m_3901_, lean_object* v_a_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2(v_00_u03b2_3900_, v_m_3901_, v_a_3902_);
lean_dec(v_a_3902_);
lean_dec_ref(v_m_3901_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4(lean_object* v_msgData_3904_, lean_object* v_macroStack_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_){
_start:
{
lean_object* v___x_3913_; 
v___x_3913_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg(v_msgData_3904_, v_macroStack_3905_, v___y_3910_);
return v___x_3913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___boxed(lean_object* v_msgData_3914_, lean_object* v_macroStack_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_){
_start:
{
lean_object* v_res_3923_; 
v_res_3923_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4(v_msgData_3914_, v_macroStack_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_, v___y_3921_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3920_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
lean_dec(v___y_3917_);
lean_dec_ref(v___y_3916_);
return v_res_3923_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3924_, lean_object* v_x_3925_, lean_object* v_x_3926_){
_start:
{
uint8_t v___x_3927_; 
v___x_3927_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___redArg(v_x_3925_, v_x_3926_);
return v___x_3927_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3928_, lean_object* v_x_3929_, lean_object* v_x_3930_){
_start:
{
uint8_t v_res_3931_; lean_object* v_r_3932_; 
v_res_3931_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1(v_00_u03b2_3928_, v_x_3929_, v_x_3930_);
lean_dec_ref(v_x_3930_);
lean_dec_ref(v_x_3929_);
v_r_3932_ = lean_box(v_res_3931_);
return v_r_3932_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2(lean_object* v_cls_3933_, lean_object* v_msg_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_){
_start:
{
lean_object* v___x_3942_; 
v___x_3942_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg(v_cls_3933_, v_msg_3934_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_3943_, lean_object* v_msg_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_){
_start:
{
lean_object* v_res_3952_; 
v_res_3952_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2(v_cls_3943_, v_msg_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
lean_dec(v___y_3948_);
lean_dec_ref(v___y_3947_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
return v_res_3952_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_3953_, lean_object* v_a_3954_, lean_object* v_x_3955_){
_start:
{
lean_object* v___x_3956_; 
v___x_3956_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__5___redArg(v_a_3954_, v_x_3955_);
return v___x_3956_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3957_, lean_object* v_a_3958_, lean_object* v_x_3959_){
_start:
{
lean_object* v_res_3960_; 
v_res_3960_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__5(v_00_u03b2_3957_, v_a_3958_, v_x_3959_);
lean_dec(v_x_3959_);
lean_dec(v_a_3958_);
return v_res_3960_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3961_, lean_object* v_x_3962_, size_t v_x_3963_, lean_object* v_x_3964_){
_start:
{
uint8_t v___x_3965_; 
v___x_3965_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg(v_x_3962_, v_x_3963_, v_x_3964_);
return v___x_3965_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_3966_, lean_object* v_x_3967_, lean_object* v_x_3968_, lean_object* v_x_3969_){
_start:
{
size_t v_x_13141__boxed_3970_; uint8_t v_res_3971_; lean_object* v_r_3972_; 
v_x_13141__boxed_3970_ = lean_unbox_usize(v_x_3968_);
lean_dec(v_x_3968_);
v_res_3971_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_3966_, v_x_3967_, v_x_13141__boxed_3970_, v_x_3969_);
lean_dec_ref(v_x_3969_);
lean_dec_ref(v_x_3967_);
v_r_3972_ = lean_box(v_res_3971_);
return v_r_3972_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_3973_, lean_object* v_keys_3974_, lean_object* v_vals_3975_, lean_object* v_heq_3976_, lean_object* v_i_3977_, lean_object* v_k_3978_){
_start:
{
uint8_t v___x_3979_; 
v___x_3979_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_3974_, v_i_3977_, v_k_3978_);
return v___x_3979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3980_, lean_object* v_keys_3981_, lean_object* v_vals_3982_, lean_object* v_heq_3983_, lean_object* v_i_3984_, lean_object* v_k_3985_){
_start:
{
uint8_t v_res_3986_; lean_object* v_r_3987_; 
v_res_3986_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_3980_, v_keys_3981_, v_vals_3982_, v_heq_3983_, v_i_3984_, v_k_3985_);
lean_dec_ref(v_k_3985_);
lean_dec_ref(v_vals_3982_);
lean_dec_ref(v_keys_3981_);
v_r_3987_ = lean_box(v_res_3986_);
return v_r_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(lean_object* v_e_3988_, lean_object* v___y_3989_){
_start:
{
uint8_t v___x_3991_; 
v___x_3991_ = l_Lean_Expr_hasMVar(v_e_3988_);
if (v___x_3991_ == 0)
{
lean_object* v___x_3992_; 
v___x_3992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3992_, 0, v_e_3988_);
return v___x_3992_;
}
else
{
lean_object* v___x_3993_; lean_object* v_mctx_3994_; lean_object* v___x_3995_; lean_object* v_fst_3996_; lean_object* v_snd_3997_; lean_object* v___x_3998_; lean_object* v_cache_3999_; lean_object* v_zetaDeltaFVarIds_4000_; lean_object* v_postponed_4001_; lean_object* v_diag_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4011_; 
v___x_3993_ = lean_st_ref_get(v___y_3989_);
v_mctx_3994_ = lean_ctor_get(v___x_3993_, 0);
lean_inc_ref(v_mctx_3994_);
lean_dec(v___x_3993_);
v___x_3995_ = l_Lean_instantiateMVarsCore(v_mctx_3994_, v_e_3988_);
v_fst_3996_ = lean_ctor_get(v___x_3995_, 0);
lean_inc(v_fst_3996_);
v_snd_3997_ = lean_ctor_get(v___x_3995_, 1);
lean_inc(v_snd_3997_);
lean_dec_ref(v___x_3995_);
v___x_3998_ = lean_st_ref_take(v___y_3989_);
v_cache_3999_ = lean_ctor_get(v___x_3998_, 1);
v_zetaDeltaFVarIds_4000_ = lean_ctor_get(v___x_3998_, 2);
v_postponed_4001_ = lean_ctor_get(v___x_3998_, 3);
v_diag_4002_ = lean_ctor_get(v___x_3998_, 4);
v_isSharedCheck_4011_ = !lean_is_exclusive(v___x_3998_);
if (v_isSharedCheck_4011_ == 0)
{
lean_object* v_unused_4012_; 
v_unused_4012_ = lean_ctor_get(v___x_3998_, 0);
lean_dec(v_unused_4012_);
v___x_4004_ = v___x_3998_;
v_isShared_4005_ = v_isSharedCheck_4011_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_diag_4002_);
lean_inc(v_postponed_4001_);
lean_inc(v_zetaDeltaFVarIds_4000_);
lean_inc(v_cache_3999_);
lean_dec(v___x_3998_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4011_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
lean_ctor_set(v___x_4004_, 0, v_snd_3997_);
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_snd_3997_);
lean_ctor_set(v_reuseFailAlloc_4010_, 1, v_cache_3999_);
lean_ctor_set(v_reuseFailAlloc_4010_, 2, v_zetaDeltaFVarIds_4000_);
lean_ctor_set(v_reuseFailAlloc_4010_, 3, v_postponed_4001_);
lean_ctor_set(v_reuseFailAlloc_4010_, 4, v_diag_4002_);
v___x_4007_ = v_reuseFailAlloc_4010_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4008_ = lean_st_ref_set(v___y_3989_, v___x_4007_);
v___x_4009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4009_, 0, v_fst_3996_);
return v___x_4009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg___boxed(lean_object* v_e_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_){
_start:
{
lean_object* v_res_4016_; 
v_res_4016_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_e_4013_, v___y_4014_);
lean_dec(v___y_4014_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0(lean_object* v_e_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_){
_start:
{
lean_object* v___x_4023_; 
v___x_4023_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_e_4017_, v___y_4019_);
return v___x_4023_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___boxed(lean_object* v_e_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_){
_start:
{
lean_object* v_res_4030_; 
v_res_4030_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0(v_e_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
lean_dec(v___y_4026_);
lean_dec_ref(v___y_4025_);
return v_res_4030_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__0(lean_object* v_x_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_){
_start:
{
lean_object* v___x_4042_; lean_object* v___x_4043_; 
v___x_4042_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___lam__0___closed__0));
v___x_4043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4043_, 0, v___x_4042_);
return v___x_4043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__0___boxed(lean_object* v_x_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
lean_object* v_res_4053_; 
v_res_4053_ = l_Lean_Elab_Tactic_NormCast_derive___lam__0(v_x_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_, v___y_4051_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
lean_dec(v___y_4049_);
lean_dec_ref(v___y_4048_);
lean_dec(v___y_4047_);
lean_dec_ref(v___y_4046_);
lean_dec(v___y_4045_);
lean_dec_ref(v_x_4044_);
return v_res_4053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__1(lean_object* v_e_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4063_, 0, v_e_4054_);
v___x_4064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4064_, 0, v___x_4063_);
return v___x_4064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__1___boxed(lean_object* v_e_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_){
_start:
{
lean_object* v_res_4074_; 
v_res_4074_ = l_Lean_Elab_Tactic_NormCast_derive___lam__1(v_e_4065_, v___y_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_, v___y_4071_, v___y_4072_);
lean_dec(v___y_4072_);
lean_dec_ref(v___y_4071_);
lean_dec(v___y_4070_);
lean_dec_ref(v___y_4069_);
lean_dec(v___y_4068_);
lean_dec_ref(v___y_4067_);
lean_dec(v___y_4066_);
return v_res_4074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__2(lean_object* v___x_4075_, lean_object* v_x_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4085_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4075_);
v___x_4086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4085_);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__2___boxed(lean_object* v___x_4087_, lean_object* v_x_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
lean_object* v_res_4097_; 
v_res_4097_ = l_Lean_Elab_Tactic_NormCast_derive___lam__2(v___x_4087_, v_x_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
lean_dec(v___y_4093_);
lean_dec_ref(v___y_4092_);
lean_dec(v___y_4091_);
lean_dec_ref(v___y_4090_);
lean_dec(v___y_4089_);
lean_dec_ref(v_x_4088_);
return v_res_4097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__3(lean_object* v___x_4098_, lean_object* v_x_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_){
_start:
{
lean_object* v___x_4108_; 
v___x_4108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4098_);
return v___x_4108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__3___boxed(lean_object* v___x_4109_, lean_object* v_x_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v_res_4119_; 
v_res_4119_ = l_Lean_Elab_Tactic_NormCast_derive___lam__3(v___x_4109_, v_x_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
lean_dec(v___y_4115_);
lean_dec_ref(v___y_4114_);
lean_dec(v___y_4113_);
lean_dec_ref(v___y_4112_);
lean_dec(v___y_4111_);
lean_dec_ref(v_x_4110_);
return v_res_4119_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__0(void){
_start:
{
lean_object* v___x_4120_; lean_object* v___x_4121_; 
v___x_4120_ = l_Lean_bombEmoji;
v___x_4121_ = l_Lean_stringToMessageData(v___x_4120_);
return v___x_4121_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__1(void){
_start:
{
lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4122_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1);
v___x_4123_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__0, &l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__0_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__0);
v___x_4124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4123_);
lean_ctor_set(v___x_4124_, 1, v___x_4122_);
return v___x_4124_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__3(void){
_start:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4126_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__2));
v___x_4127_ = l_Lean_stringToMessageData(v___x_4126_);
return v___x_4127_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__5(void){
_start:
{
lean_object* v___x_4129_; lean_object* v___x_4130_; 
v___x_4129_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__4));
v___x_4130_ = l_Lean_stringToMessageData(v___x_4129_);
return v___x_4130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__4(lean_object* v_phase_4131_, lean_object* v_x_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
if (lean_obj_tag(v_x_4132_) == 0)
{
lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4147_; 
v_isSharedCheck_4147_ = !lean_is_exclusive(v_x_4132_);
if (v_isSharedCheck_4147_ == 0)
{
lean_object* v_unused_4148_; 
v_unused_4148_ = lean_ctor_get(v_x_4132_, 0);
lean_dec(v_unused_4148_);
v___x_4139_ = v_x_4132_;
v_isShared_4140_ = v_isSharedCheck_4147_;
goto v_resetjp_4138_;
}
else
{
lean_dec(v_x_4132_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4147_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4145_; 
v___x_4141_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__1, &l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__1);
v___x_4142_ = l_Lean_stringToMessageData(v_phase_4131_);
v___x_4143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4141_);
lean_ctor_set(v___x_4143_, 1, v___x_4142_);
if (v_isShared_4140_ == 0)
{
lean_ctor_set(v___x_4139_, 0, v___x_4143_);
v___x_4145_ = v___x_4139_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v___x_4143_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
else
{
lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4164_; 
v_a_4149_ = lean_ctor_get(v_x_4132_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v_x_4132_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4151_ = v_x_4132_;
v_isShared_4152_ = v_isSharedCheck_4164_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v_x_4132_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4164_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v_expr_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4162_; 
v_expr_4153_ = lean_ctor_get(v_a_4149_, 0);
lean_inc_ref(v_expr_4153_);
lean_dec(v_a_4149_);
v___x_4154_ = l_Lean_MessageData_ofExpr(v_expr_4153_);
v___x_4155_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__3, &l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__3_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__3);
v___x_4156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4154_);
lean_ctor_set(v___x_4156_, 1, v___x_4155_);
v___x_4157_ = l_Lean_stringToMessageData(v_phase_4131_);
v___x_4158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4156_);
lean_ctor_set(v___x_4158_, 1, v___x_4157_);
v___x_4159_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__5, &l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__5);
v___x_4160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4158_);
lean_ctor_set(v___x_4160_, 1, v___x_4159_);
if (v_isShared_4152_ == 0)
{
lean_ctor_set_tag(v___x_4151_, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4160_);
v___x_4162_ = v___x_4151_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v___x_4160_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
return v___x_4162_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__4___boxed(lean_object* v_phase_4165_, lean_object* v_x_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v_res_4172_; 
v_res_4172_ = l_Lean_Elab_Tactic_NormCast_derive___lam__4(v_phase_4165_, v_x_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
return v_res_4172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__5(lean_object* v___x_4173_, uint8_t v___x_4174_, lean_object* v_phase_4175_, lean_object* v_k_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_){
_start:
{
lean_object* v_options_4182_; uint8_t v_hasTrace_4183_; 
v_options_4182_ = lean_ctor_get(v___y_4179_, 2);
v_hasTrace_4183_ = lean_ctor_get_uint8(v_options_4182_, sizeof(void*)*1);
if (v_hasTrace_4183_ == 0)
{
lean_object* v___x_4184_; 
lean_dec_ref(v_phase_4175_);
lean_dec(v___x_4173_);
lean_inc(v___y_4180_);
lean_inc_ref(v___y_4179_);
lean_inc(v___y_4178_);
lean_inc_ref(v___y_4177_);
v___x_4184_ = lean_apply_5(v_k_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, lean_box(0));
return v___x_4184_;
}
else
{
lean_object* v_inheritedTraceOptions_4185_; lean_object* v___f_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; uint8_t v___x_4190_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v_a_4194_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v_a_4209_; 
v_inheritedTraceOptions_4185_ = lean_ctor_get(v___y_4179_, 13);
v___f_4186_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4186_, 0, v_phase_4175_);
v___x_4187_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_4188_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__2));
lean_inc(v___x_4173_);
v___x_4189_ = l_Lean_Name_append(v___x_4188_, v___x_4173_);
v___x_4190_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4185_, v_options_4182_, v___x_4189_);
lean_dec(v___x_4189_);
if (v___x_4190_ == 0)
{
lean_object* v___x_4259_; uint8_t v___x_4260_; 
v___x_4259_ = l_Lean_trace_profiler;
v___x_4260_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_4182_, v___x_4259_);
if (v___x_4260_ == 0)
{
lean_object* v___x_4261_; 
lean_dec_ref(v___f_4186_);
lean_dec(v___x_4173_);
lean_inc(v___y_4180_);
lean_inc_ref(v___y_4179_);
lean_inc(v___y_4178_);
lean_inc_ref(v___y_4177_);
v___x_4261_ = lean_apply_5(v_k_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, lean_box(0));
return v___x_4261_;
}
else
{
goto v___jp_4218_;
}
}
else
{
goto v___jp_4218_;
}
v___jp_4191_:
{
lean_object* v___x_4195_; double v___x_4196_; double v___x_4197_; double v___x_4198_; double v___x_4199_; double v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4195_ = lean_io_mono_nanos_now();
v___x_4196_ = lean_float_of_nat(v___y_4192_);
v___x_4197_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4);
v___x_4198_ = lean_float_div(v___x_4196_, v___x_4197_);
v___x_4199_ = lean_float_of_nat(v___x_4195_);
v___x_4200_ = lean_float_div(v___x_4199_, v___x_4197_);
v___x_4201_ = lean_box_float(v___x_4198_);
v___x_4202_ = lean_box_float(v___x_4200_);
v___x_4203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4201_);
lean_ctor_set(v___x_4203_, 1, v___x_4202_);
v___x_4204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4204_, 0, v_a_4194_);
lean_ctor_set(v___x_4204_, 1, v___x_4203_);
v___x_4205_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4173_, v___x_4174_, v___x_4187_, v_options_4182_, v___x_4190_, v___y_4193_, v___f_4186_, v___x_4204_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_);
return v___x_4205_;
}
v___jp_4206_:
{
lean_object* v___x_4210_; double v___x_4211_; double v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
v___x_4210_ = lean_io_get_num_heartbeats();
v___x_4211_ = lean_float_of_nat(v___y_4207_);
v___x_4212_ = lean_float_of_nat(v___x_4210_);
v___x_4213_ = lean_box_float(v___x_4211_);
v___x_4214_ = lean_box_float(v___x_4212_);
v___x_4215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4213_);
lean_ctor_set(v___x_4215_, 1, v___x_4214_);
v___x_4216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4216_, 0, v_a_4209_);
lean_ctor_set(v___x_4216_, 1, v___x_4215_);
v___x_4217_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4173_, v___x_4174_, v___x_4187_, v_options_4182_, v___x_4190_, v___y_4208_, v___f_4186_, v___x_4216_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_);
return v___x_4217_;
}
v___jp_4218_:
{
lean_object* v___x_4219_; lean_object* v_a_4220_; lean_object* v___x_4221_; uint8_t v___x_4222_; 
v___x_4219_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___y_4180_);
v_a_4220_ = lean_ctor_get(v___x_4219_, 0);
lean_inc(v_a_4220_);
lean_dec_ref(v___x_4219_);
v___x_4221_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4222_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_4182_, v___x_4221_);
if (v___x_4222_ == 0)
{
lean_object* v___x_4223_; lean_object* v___x_4224_; 
v___x_4223_ = lean_io_mono_nanos_now();
lean_inc(v___y_4180_);
lean_inc_ref(v___y_4179_);
lean_inc(v___y_4178_);
lean_inc_ref(v___y_4177_);
v___x_4224_ = lean_apply_5(v_k_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, lean_box(0));
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_object* v_a_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4232_; 
v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4232_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4232_ == 0)
{
v___x_4227_ = v___x_4224_;
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_a_4225_);
lean_dec(v___x_4224_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v___x_4230_; 
if (v_isShared_4228_ == 0)
{
lean_ctor_set_tag(v___x_4227_, 1);
v___x_4230_ = v___x_4227_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_a_4225_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
v___y_4192_ = v___x_4223_;
v___y_4193_ = v_a_4220_;
v_a_4194_ = v___x_4230_;
goto v___jp_4191_;
}
}
}
else
{
lean_object* v_a_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4240_; 
v_a_4233_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4235_ = v___x_4224_;
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_a_4233_);
lean_dec(v___x_4224_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4238_; 
if (v_isShared_4236_ == 0)
{
lean_ctor_set_tag(v___x_4235_, 0);
v___x_4238_ = v___x_4235_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_a_4233_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
v___y_4192_ = v___x_4223_;
v___y_4193_ = v_a_4220_;
v_a_4194_ = v___x_4238_;
goto v___jp_4191_;
}
}
}
}
else
{
lean_object* v___x_4241_; lean_object* v___x_4242_; 
v___x_4241_ = lean_io_get_num_heartbeats();
lean_inc(v___y_4180_);
lean_inc_ref(v___y_4179_);
lean_inc(v___y_4178_);
lean_inc_ref(v___y_4177_);
v___x_4242_ = lean_apply_5(v_k_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, lean_box(0));
if (lean_obj_tag(v___x_4242_) == 0)
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
v_a_4243_ = lean_ctor_get(v___x_4242_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4242_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4242_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4242_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
lean_ctor_set_tag(v___x_4245_, 1);
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4243_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
v___y_4207_ = v___x_4241_;
v___y_4208_ = v_a_4220_;
v_a_4209_ = v___x_4248_;
goto v___jp_4206_;
}
}
}
else
{
lean_object* v_a_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4258_; 
v_a_4251_ = lean_ctor_get(v___x_4242_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4242_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4253_ = v___x_4242_;
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_a_4251_);
lean_dec(v___x_4242_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v___x_4256_; 
if (v_isShared_4254_ == 0)
{
lean_ctor_set_tag(v___x_4253_, 0);
v___x_4256_ = v___x_4253_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_a_4251_);
v___x_4256_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
v___y_4207_ = v___x_4241_;
v___y_4208_ = v_a_4220_;
v_a_4209_ = v___x_4256_;
goto v___jp_4206_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__5___boxed(lean_object* v___x_4262_, lean_object* v___x_4263_, lean_object* v_phase_4264_, lean_object* v_k_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_){
_start:
{
uint8_t v___x_35176__boxed_4271_; lean_object* v_res_4272_; 
v___x_35176__boxed_4271_ = lean_unbox(v___x_4263_);
v_res_4272_ = l_Lean_Elab_Tactic_NormCast_derive___lam__5(v___x_4262_, v___x_35176__boxed_4271_, v_phase_4264_, v_k_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_);
lean_dec(v___y_4269_);
lean_dec_ref(v___y_4268_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
return v_res_4272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__6(lean_object* v___x_4273_, uint8_t v___x_4274_, lean_object* v_e_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_){
_start:
{
lean_object* v_a_4285_; lean_object* v___y_4289_; lean_object* v___x_4299_; 
lean_inc_ref(v_e_4275_);
v___x_4299_ = l_Lean_Elab_Tactic_NormCast_numeralToCoe(v_e_4275_, v___y_4279_, v___y_4280_, v___y_4281_, v___y_4282_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_dec_ref(v_e_4275_);
lean_dec(v___x_4273_);
v___y_4289_ = v___x_4299_;
goto v___jp_4288_;
}
else
{
lean_object* v_a_4300_; uint8_t v___y_4302_; uint8_t v___x_4304_; 
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
lean_inc(v_a_4300_);
v___x_4304_ = l_Lean_Exception_isInterrupt(v_a_4300_);
if (v___x_4304_ == 0)
{
uint8_t v___x_4305_; 
v___x_4305_ = l_Lean_Exception_isRuntime(v_a_4300_);
v___y_4302_ = v___x_4305_;
goto v___jp_4301_;
}
else
{
lean_dec(v_a_4300_);
v___y_4302_ = v___x_4304_;
goto v___jp_4301_;
}
v___jp_4301_:
{
if (v___y_4302_ == 0)
{
lean_object* v___x_4303_; 
lean_dec_ref(v___x_4299_);
v___x_4303_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4303_, 0, v_e_4275_);
lean_ctor_set(v___x_4303_, 1, v___x_4273_);
lean_ctor_set_uint8(v___x_4303_, sizeof(void*)*2, v___x_4274_);
v_a_4285_ = v___x_4303_;
goto v___jp_4284_;
}
else
{
lean_dec_ref(v_e_4275_);
lean_dec(v___x_4273_);
v___y_4289_ = v___x_4299_;
goto v___jp_4288_;
}
}
}
v___jp_4284_:
{
lean_object* v___x_4286_; lean_object* v___x_4287_; 
v___x_4286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4286_, 0, v_a_4285_);
v___x_4287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4286_);
return v___x_4287_;
}
v___jp_4288_:
{
if (lean_obj_tag(v___y_4289_) == 0)
{
lean_object* v_a_4290_; 
v_a_4290_ = lean_ctor_get(v___y_4289_, 0);
lean_inc(v_a_4290_);
lean_dec_ref(v___y_4289_);
v_a_4285_ = v_a_4290_;
goto v___jp_4284_;
}
else
{
lean_object* v_a_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4298_; 
v_a_4291_ = lean_ctor_get(v___y_4289_, 0);
v_isSharedCheck_4298_ = !lean_is_exclusive(v___y_4289_);
if (v_isSharedCheck_4298_ == 0)
{
v___x_4293_ = v___y_4289_;
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_a_4291_);
lean_dec(v___y_4289_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v___x_4296_; 
if (v_isShared_4294_ == 0)
{
v___x_4296_ = v___x_4293_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_a_4291_);
v___x_4296_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
return v___x_4296_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__6___boxed(lean_object* v___x_4306_, lean_object* v___x_4307_, lean_object* v_e_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_){
_start:
{
uint8_t v___x_35354__boxed_4317_; lean_object* v_res_4318_; 
v___x_35354__boxed_4317_ = lean_unbox(v___x_4307_);
v_res_4318_ = l_Lean_Elab_Tactic_NormCast_derive___lam__6(v___x_4306_, v___x_35354__boxed_4317_, v_e_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_, v___y_4315_);
lean_dec(v___y_4315_);
lean_dec_ref(v___y_4314_);
lean_dec(v___y_4313_);
lean_dec_ref(v___y_4312_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec(v___y_4309_);
return v_res_4318_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__0(void){
_start:
{
lean_object* v___x_4319_; 
v___x_4319_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4319_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1(void){
_start:
{
lean_object* v___x_4320_; lean_object* v___x_4321_; 
v___x_4320_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__0, &l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__0_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__0);
v___x_4321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4321_, 0, v___x_4320_);
return v___x_4321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__7(lean_object* v_config_4322_, lean_object* v___x_4323_, lean_object* v_a_4324_, lean_object* v___x_4325_, lean_object* v___f_4326_, lean_object* v___f_4327_, lean_object* v___f_4328_, lean_object* v___f_4329_, lean_object* v___f_4330_, uint8_t v___x_4331_, lean_object* v_a_4332_, lean_object* v___x_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_){
_start:
{
lean_object* v___x_4339_; 
v___x_4339_ = l_Lean_Meta_Simp_mkContext___redArg(v_config_4322_, v___x_4323_, v_a_4324_, v___y_4334_, v___y_4336_, v___y_4337_);
if (lean_obj_tag(v___x_4339_) == 0)
{
lean_object* v_a_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; size_t v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; 
v_a_4340_ = lean_ctor_get(v___x_4339_, 0);
lean_inc(v_a_4340_);
lean_dec_ref(v___x_4339_);
v___x_4341_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1, &l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1);
lean_inc_n(v___x_4325_, 2);
v___x_4342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4342_, 0, v___x_4341_);
lean_ctor_set(v___x_4342_, 1, v___x_4325_);
v___x_4343_ = lean_unsigned_to_nat(32u);
v___x_4344_ = lean_mk_empty_array_with_capacity(v___x_4343_);
v___x_4345_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8);
v___x_4346_ = ((size_t)5ULL);
v___x_4347_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4347_, 0, v___x_4345_);
lean_ctor_set(v___x_4347_, 1, v___x_4344_);
lean_ctor_set(v___x_4347_, 2, v___x_4325_);
lean_ctor_set(v___x_4347_, 3, v___x_4325_);
lean_ctor_set_usize(v___x_4347_, 4, v___x_4346_);
v___x_4348_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4348_, 0, v___x_4341_);
lean_ctor_set(v___x_4348_, 1, v___x_4341_);
lean_ctor_set(v___x_4348_, 2, v___x_4341_);
lean_ctor_set(v___x_4348_, 3, v___x_4347_);
v___x_4349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4349_, 0, v___x_4342_);
lean_ctor_set(v___x_4349_, 1, v___x_4348_);
v___x_4350_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4350_, 0, v___f_4326_);
lean_ctor_set(v___x_4350_, 1, v___f_4327_);
lean_ctor_set(v___x_4350_, 2, v___f_4328_);
lean_ctor_set(v___x_4350_, 3, v___f_4329_);
lean_ctor_set(v___x_4350_, 4, v___f_4330_);
lean_ctor_set_uint8(v___x_4350_, sizeof(void*)*5, v___x_4331_);
v___x_4351_ = l_Lean_Meta_Simp_main(v_a_4332_, v_a_4340_, v___x_4349_, v___x_4350_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_);
if (lean_obj_tag(v___x_4351_) == 0)
{
lean_object* v_a_4352_; lean_object* v_fst_4353_; lean_object* v___x_4354_; 
v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
lean_inc(v_a_4352_);
lean_dec_ref(v___x_4351_);
v_fst_4353_ = lean_ctor_get(v_a_4352_, 0);
lean_inc(v_fst_4353_);
lean_dec(v_a_4352_);
v___x_4354_ = l_Lean_Meta_Simp_Result_mkEqTrans(v___x_4333_, v_fst_4353_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_);
return v___x_4354_;
}
else
{
lean_object* v_a_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4362_; 
lean_dec_ref(v___x_4333_);
v_a_4355_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4362_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4362_ == 0)
{
v___x_4357_ = v___x_4351_;
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_a_4355_);
lean_dec(v___x_4351_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4360_; 
if (v_isShared_4358_ == 0)
{
v___x_4360_ = v___x_4357_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_a_4355_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
return v___x_4360_;
}
}
}
}
else
{
lean_object* v_a_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4370_; 
lean_dec_ref(v___x_4333_);
lean_dec_ref(v_a_4332_);
lean_dec_ref(v___f_4330_);
lean_dec_ref(v___f_4329_);
lean_dec_ref(v___f_4328_);
lean_dec_ref(v___f_4327_);
lean_dec_ref(v___f_4326_);
lean_dec(v___x_4325_);
v_a_4363_ = lean_ctor_get(v___x_4339_, 0);
v_isSharedCheck_4370_ = !lean_is_exclusive(v___x_4339_);
if (v_isSharedCheck_4370_ == 0)
{
v___x_4365_ = v___x_4339_;
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_a_4363_);
lean_dec(v___x_4339_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4368_; 
if (v_isShared_4366_ == 0)
{
v___x_4368_ = v___x_4365_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v_a_4363_);
v___x_4368_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
return v___x_4368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__7___boxed(lean_object** _args){
lean_object* v_config_4371_ = _args[0];
lean_object* v___x_4372_ = _args[1];
lean_object* v_a_4373_ = _args[2];
lean_object* v___x_4374_ = _args[3];
lean_object* v___f_4375_ = _args[4];
lean_object* v___f_4376_ = _args[5];
lean_object* v___f_4377_ = _args[6];
lean_object* v___f_4378_ = _args[7];
lean_object* v___f_4379_ = _args[8];
lean_object* v___x_4380_ = _args[9];
lean_object* v_a_4381_ = _args[10];
lean_object* v___x_4382_ = _args[11];
lean_object* v___y_4383_ = _args[12];
lean_object* v___y_4384_ = _args[13];
lean_object* v___y_4385_ = _args[14];
lean_object* v___y_4386_ = _args[15];
lean_object* v___y_4387_ = _args[16];
_start:
{
uint8_t v___x_35445__boxed_4388_; lean_object* v_res_4389_; 
v___x_35445__boxed_4388_ = lean_unbox(v___x_4380_);
v_res_4389_ = l_Lean_Elab_Tactic_NormCast_derive___lam__7(v_config_4371_, v___x_4372_, v_a_4373_, v___x_4374_, v___f_4375_, v___f_4376_, v___f_4377_, v___f_4378_, v___f_4379_, v___x_35445__boxed_4388_, v_a_4381_, v___x_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_);
lean_dec(v___y_4386_);
lean_dec_ref(v___y_4385_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4383_);
return v_res_4389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__12(lean_object* v_up_4390_, lean_object* v_config_4391_, lean_object* v___x_4392_, lean_object* v_a_4393_, lean_object* v_a_4394_, lean_object* v___x_4395_, lean_object* v___f_4396_, lean_object* v___f_4397_, lean_object* v___f_4398_, lean_object* v___f_4399_, uint8_t v___x_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_){
_start:
{
lean_object* v___x_4406_; 
v___x_4406_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_up_4390_, v___y_4404_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_object* v_a_4407_; lean_object* v___x_4408_; 
v_a_4407_ = lean_ctor_get(v___x_4406_, 0);
lean_inc(v_a_4407_);
lean_dec_ref(v___x_4406_);
v___x_4408_ = l_Lean_Meta_Simp_mkContext___redArg(v_config_4391_, v___x_4392_, v_a_4393_, v___y_4401_, v___y_4403_, v___y_4404_);
if (lean_obj_tag(v___x_4408_) == 0)
{
lean_object* v_a_4409_; lean_object* v_expr_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; size_t v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; 
v_a_4409_ = lean_ctor_get(v___x_4408_, 0);
lean_inc(v_a_4409_);
lean_dec_ref(v___x_4408_);
v_expr_4410_ = lean_ctor_get(v_a_4394_, 0);
v___x_4411_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_upwardAndElim___boxed), 10, 1);
lean_closure_set(v___x_4411_, 0, v_a_4407_);
v___x_4412_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1, &l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1);
lean_inc_n(v___x_4395_, 2);
v___x_4413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4413_, 0, v___x_4412_);
lean_ctor_set(v___x_4413_, 1, v___x_4395_);
v___x_4414_ = lean_unsigned_to_nat(32u);
v___x_4415_ = lean_mk_empty_array_with_capacity(v___x_4414_);
v___x_4416_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8);
v___x_4417_ = ((size_t)5ULL);
v___x_4418_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4418_, 0, v___x_4416_);
lean_ctor_set(v___x_4418_, 1, v___x_4415_);
lean_ctor_set(v___x_4418_, 2, v___x_4395_);
lean_ctor_set(v___x_4418_, 3, v___x_4395_);
lean_ctor_set_usize(v___x_4418_, 4, v___x_4417_);
v___x_4419_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4419_, 0, v___x_4412_);
lean_ctor_set(v___x_4419_, 1, v___x_4412_);
lean_ctor_set(v___x_4419_, 2, v___x_4412_);
lean_ctor_set(v___x_4419_, 3, v___x_4418_);
v___x_4420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4420_, 0, v___x_4413_);
lean_ctor_set(v___x_4420_, 1, v___x_4419_);
v___x_4421_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4421_, 0, v___f_4396_);
lean_ctor_set(v___x_4421_, 1, v___x_4411_);
lean_ctor_set(v___x_4421_, 2, v___f_4397_);
lean_ctor_set(v___x_4421_, 3, v___f_4398_);
lean_ctor_set(v___x_4421_, 4, v___f_4399_);
lean_ctor_set_uint8(v___x_4421_, sizeof(void*)*5, v___x_4400_);
lean_inc_ref(v_expr_4410_);
v___x_4422_ = l_Lean_Meta_Simp_main(v_expr_4410_, v_a_4409_, v___x_4420_, v___x_4421_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_);
if (lean_obj_tag(v___x_4422_) == 0)
{
lean_object* v_a_4423_; lean_object* v_fst_4424_; lean_object* v___x_4425_; 
v_a_4423_ = lean_ctor_get(v___x_4422_, 0);
lean_inc(v_a_4423_);
lean_dec_ref(v___x_4422_);
v_fst_4424_ = lean_ctor_get(v_a_4423_, 0);
lean_inc(v_fst_4424_);
lean_dec(v_a_4423_);
v___x_4425_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_4394_, v_fst_4424_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_);
return v___x_4425_;
}
else
{
lean_object* v_a_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4433_; 
lean_dec_ref(v_a_4394_);
v_a_4426_ = lean_ctor_get(v___x_4422_, 0);
v_isSharedCheck_4433_ = !lean_is_exclusive(v___x_4422_);
if (v_isSharedCheck_4433_ == 0)
{
v___x_4428_ = v___x_4422_;
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_a_4426_);
lean_dec(v___x_4422_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4431_; 
if (v_isShared_4429_ == 0)
{
v___x_4431_ = v___x_4428_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_a_4426_);
v___x_4431_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
return v___x_4431_;
}
}
}
}
else
{
lean_object* v_a_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4441_; 
lean_dec(v_a_4407_);
lean_dec_ref(v___f_4399_);
lean_dec_ref(v___f_4398_);
lean_dec_ref(v___f_4397_);
lean_dec_ref(v___f_4396_);
lean_dec(v___x_4395_);
lean_dec_ref(v_a_4394_);
v_a_4434_ = lean_ctor_get(v___x_4408_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4408_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4436_ = v___x_4408_;
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_a_4434_);
lean_dec(v___x_4408_);
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
else
{
lean_object* v_a_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4449_; 
lean_dec_ref(v___f_4399_);
lean_dec_ref(v___f_4398_);
lean_dec_ref(v___f_4397_);
lean_dec_ref(v___f_4396_);
lean_dec(v___x_4395_);
lean_dec_ref(v_a_4394_);
lean_dec_ref(v_a_4393_);
lean_dec_ref(v___x_4392_);
lean_dec_ref(v_config_4391_);
v_a_4442_ = lean_ctor_get(v___x_4406_, 0);
v_isSharedCheck_4449_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4449_ == 0)
{
v___x_4444_ = v___x_4406_;
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_a_4442_);
lean_dec(v___x_4406_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v___x_4447_; 
if (v_isShared_4445_ == 0)
{
v___x_4447_ = v___x_4444_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_a_4442_);
v___x_4447_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
return v___x_4447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__12___boxed(lean_object* v_up_4450_, lean_object* v_config_4451_, lean_object* v___x_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_, lean_object* v___x_4455_, lean_object* v___f_4456_, lean_object* v___f_4457_, lean_object* v___f_4458_, lean_object* v___f_4459_, lean_object* v___x_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_){
_start:
{
uint8_t v___x_35564__boxed_4466_; lean_object* v_res_4467_; 
v___x_35564__boxed_4466_ = lean_unbox(v___x_4460_);
v_res_4467_ = l_Lean_Elab_Tactic_NormCast_derive___lam__12(v_up_4450_, v_config_4451_, v___x_4452_, v_a_4453_, v_a_4454_, v___x_4455_, v___f_4456_, v___f_4457_, v___f_4458_, v___f_4459_, v___x_35564__boxed_4466_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_);
lean_dec(v___y_4464_);
lean_dec_ref(v___y_4463_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
lean_dec_ref(v_up_4450_);
return v_res_4467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__8(lean_object* v_squash_4468_, lean_object* v_config_4469_, lean_object* v_a_4470_, lean_object* v_a_4471_, lean_object* v___x_4472_, lean_object* v_a_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_){
_start:
{
lean_object* v___x_4479_; 
v___x_4479_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_squash_4468_, v___y_4477_);
if (lean_obj_tag(v___x_4479_) == 0)
{
lean_object* v_a_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; 
v_a_4480_ = lean_ctor_get(v___x_4479_, 0);
lean_inc(v_a_4480_);
lean_dec_ref(v___x_4479_);
v___x_4481_ = lean_unsigned_to_nat(1u);
v___x_4482_ = lean_mk_empty_array_with_capacity(v___x_4481_);
v___x_4483_ = lean_array_push(v___x_4482_, v_a_4480_);
v___x_4484_ = l_Lean_Meta_Simp_mkContext___redArg(v_config_4469_, v___x_4483_, v_a_4470_, v___y_4474_, v___y_4476_, v___y_4477_);
if (lean_obj_tag(v___x_4484_) == 0)
{
lean_object* v_a_4485_; lean_object* v_expr_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; size_t v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; 
v_a_4485_ = lean_ctor_get(v___x_4484_, 0);
lean_inc(v_a_4485_);
lean_dec_ref(v___x_4484_);
v_expr_4486_ = lean_ctor_get(v_a_4471_, 0);
v___x_4487_ = lean_box(0);
v___x_4488_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1, &l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1);
lean_inc_n(v___x_4472_, 2);
v___x_4489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4489_, 0, v___x_4488_);
lean_ctor_set(v___x_4489_, 1, v___x_4472_);
v___x_4490_ = lean_unsigned_to_nat(32u);
v___x_4491_ = lean_mk_empty_array_with_capacity(v___x_4490_);
v___x_4492_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8);
v___x_4493_ = ((size_t)5ULL);
v___x_4494_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4494_, 0, v___x_4492_);
lean_ctor_set(v___x_4494_, 1, v___x_4491_);
lean_ctor_set(v___x_4494_, 2, v___x_4472_);
lean_ctor_set(v___x_4494_, 3, v___x_4472_);
lean_ctor_set_usize(v___x_4494_, 4, v___x_4493_);
v___x_4495_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4495_, 0, v___x_4488_);
lean_ctor_set(v___x_4495_, 1, v___x_4488_);
lean_ctor_set(v___x_4495_, 2, v___x_4488_);
lean_ctor_set(v___x_4495_, 3, v___x_4494_);
v___x_4496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4496_, 0, v___x_4489_);
lean_ctor_set(v___x_4496_, 1, v___x_4495_);
lean_inc_ref(v_expr_4486_);
v___x_4497_ = l_Lean_Meta_simp(v_expr_4486_, v_a_4485_, v_a_4473_, v___x_4487_, v___x_4496_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
lean_dec_ref(v___x_4496_);
if (lean_obj_tag(v___x_4497_) == 0)
{
lean_object* v_a_4498_; lean_object* v_fst_4499_; lean_object* v___x_4500_; 
v_a_4498_ = lean_ctor_get(v___x_4497_, 0);
lean_inc(v_a_4498_);
lean_dec_ref(v___x_4497_);
v_fst_4499_ = lean_ctor_get(v_a_4498_, 0);
lean_inc(v_fst_4499_);
lean_dec(v_a_4498_);
v___x_4500_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_4471_, v_fst_4499_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
return v___x_4500_;
}
else
{
lean_object* v_a_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4508_; 
lean_dec_ref(v_a_4471_);
v_a_4501_ = lean_ctor_get(v___x_4497_, 0);
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4503_ = v___x_4497_;
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_a_4501_);
lean_dec(v___x_4497_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4506_; 
if (v_isShared_4504_ == 0)
{
v___x_4506_ = v___x_4503_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_a_4501_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
return v___x_4506_;
}
}
}
}
else
{
lean_object* v_a_4509_; lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4516_; 
lean_dec_ref(v_a_4473_);
lean_dec(v___x_4472_);
lean_dec_ref(v_a_4471_);
v_a_4509_ = lean_ctor_get(v___x_4484_, 0);
v_isSharedCheck_4516_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4511_ = v___x_4484_;
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
else
{
lean_inc(v_a_4509_);
lean_dec(v___x_4484_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v___x_4514_; 
if (v_isShared_4512_ == 0)
{
v___x_4514_ = v___x_4511_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v_a_4509_);
v___x_4514_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
return v___x_4514_;
}
}
}
}
else
{
lean_object* v_a_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4524_; 
lean_dec_ref(v_a_4473_);
lean_dec(v___x_4472_);
lean_dec_ref(v_a_4471_);
lean_dec_ref(v_a_4470_);
lean_dec_ref(v_config_4469_);
v_a_4517_ = lean_ctor_get(v___x_4479_, 0);
v_isSharedCheck_4524_ = !lean_is_exclusive(v___x_4479_);
if (v_isSharedCheck_4524_ == 0)
{
v___x_4519_ = v___x_4479_;
v_isShared_4520_ = v_isSharedCheck_4524_;
goto v_resetjp_4518_;
}
else
{
lean_inc(v_a_4517_);
lean_dec(v___x_4479_);
v___x_4519_ = lean_box(0);
v_isShared_4520_ = v_isSharedCheck_4524_;
goto v_resetjp_4518_;
}
v_resetjp_4518_:
{
lean_object* v___x_4522_; 
if (v_isShared_4520_ == 0)
{
v___x_4522_ = v___x_4519_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v_a_4517_);
v___x_4522_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
return v___x_4522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__8___boxed(lean_object* v_squash_4525_, lean_object* v_config_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v___x_4529_, lean_object* v_a_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_){
_start:
{
lean_object* v_res_4536_; 
v_res_4536_ = l_Lean_Elab_Tactic_NormCast_derive___lam__8(v_squash_4525_, v_config_4526_, v_a_4527_, v_a_4528_, v___x_4529_, v_a_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
lean_dec(v___y_4534_);
lean_dec_ref(v___y_4533_);
lean_dec(v___y_4532_);
lean_dec_ref(v___y_4531_);
lean_dec_ref(v_squash_4525_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__18(lean_object* v_e_4537_, lean_object* v_x_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_){
_start:
{
lean_object* v___x_4544_; lean_object* v___x_4545_; 
v___x_4544_ = l_Lean_MessageData_ofExpr(v_e_4537_);
v___x_4545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4545_, 0, v___x_4544_);
return v___x_4545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__18___boxed(lean_object* v_e_4546_, lean_object* v_x_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_){
_start:
{
lean_object* v_res_4553_; 
v_res_4553_ = l_Lean_Elab_Tactic_NormCast_derive___lam__18(v_e_4546_, v_x_4547_, v___y_4548_, v___y_4549_, v___y_4550_, v___y_4551_);
lean_dec(v___y_4551_);
lean_dec_ref(v___y_4550_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
lean_dec_ref(v_x_4547_);
return v_res_4553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__10(lean_object* v___x_4554_, uint8_t v_hasTrace_4555_, lean_object* v_phase_4556_, lean_object* v_k_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_){
_start:
{
lean_object* v_options_4563_; uint8_t v_hasTrace_4564_; 
v_options_4563_ = lean_ctor_get(v___y_4560_, 2);
v_hasTrace_4564_ = lean_ctor_get_uint8(v_options_4563_, sizeof(void*)*1);
if (v_hasTrace_4564_ == 0)
{
lean_object* v___x_4565_; 
lean_dec_ref(v_phase_4556_);
lean_dec(v___x_4554_);
lean_inc(v___y_4561_);
lean_inc_ref(v___y_4560_);
lean_inc(v___y_4559_);
lean_inc_ref(v___y_4558_);
v___x_4565_ = lean_apply_5(v_k_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, lean_box(0));
return v___x_4565_;
}
else
{
lean_object* v_inheritedTraceOptions_4566_; lean_object* v___f_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; uint8_t v___x_4571_; lean_object* v___y_4573_; lean_object* v___y_4574_; lean_object* v_a_4575_; lean_object* v___y_4588_; lean_object* v___y_4589_; lean_object* v_a_4590_; 
v_inheritedTraceOptions_4566_ = lean_ctor_get(v___y_4560_, 13);
v___f_4567_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4567_, 0, v_phase_4556_);
v___x_4568_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_4569_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__2));
lean_inc(v___x_4554_);
v___x_4570_ = l_Lean_Name_append(v___x_4569_, v___x_4554_);
v___x_4571_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4566_, v_options_4563_, v___x_4570_);
lean_dec(v___x_4570_);
if (v___x_4571_ == 0)
{
lean_object* v___x_4640_; uint8_t v___x_4641_; 
v___x_4640_ = l_Lean_trace_profiler;
v___x_4641_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_4563_, v___x_4640_);
if (v___x_4641_ == 0)
{
lean_object* v___x_4642_; 
lean_dec_ref(v___f_4567_);
lean_dec(v___x_4554_);
lean_inc(v___y_4561_);
lean_inc_ref(v___y_4560_);
lean_inc(v___y_4559_);
lean_inc_ref(v___y_4558_);
v___x_4642_ = lean_apply_5(v_k_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, lean_box(0));
return v___x_4642_;
}
else
{
goto v___jp_4599_;
}
}
else
{
goto v___jp_4599_;
}
v___jp_4572_:
{
lean_object* v___x_4576_; double v___x_4577_; double v___x_4578_; double v___x_4579_; double v___x_4580_; double v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; 
v___x_4576_ = lean_io_mono_nanos_now();
v___x_4577_ = lean_float_of_nat(v___y_4573_);
v___x_4578_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4);
v___x_4579_ = lean_float_div(v___x_4577_, v___x_4578_);
v___x_4580_ = lean_float_of_nat(v___x_4576_);
v___x_4581_ = lean_float_div(v___x_4580_, v___x_4578_);
v___x_4582_ = lean_box_float(v___x_4579_);
v___x_4583_ = lean_box_float(v___x_4581_);
v___x_4584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4584_, 0, v___x_4582_);
lean_ctor_set(v___x_4584_, 1, v___x_4583_);
v___x_4585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4585_, 0, v_a_4575_);
lean_ctor_set(v___x_4585_, 1, v___x_4584_);
v___x_4586_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4554_, v_hasTrace_4555_, v___x_4568_, v_options_4563_, v___x_4571_, v___y_4574_, v___f_4567_, v___x_4585_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_);
return v___x_4586_;
}
v___jp_4587_:
{
lean_object* v___x_4591_; double v___x_4592_; double v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; 
v___x_4591_ = lean_io_get_num_heartbeats();
v___x_4592_ = lean_float_of_nat(v___y_4589_);
v___x_4593_ = lean_float_of_nat(v___x_4591_);
v___x_4594_ = lean_box_float(v___x_4592_);
v___x_4595_ = lean_box_float(v___x_4593_);
v___x_4596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4594_);
lean_ctor_set(v___x_4596_, 1, v___x_4595_);
v___x_4597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4597_, 0, v_a_4590_);
lean_ctor_set(v___x_4597_, 1, v___x_4596_);
v___x_4598_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4554_, v_hasTrace_4555_, v___x_4568_, v_options_4563_, v___x_4571_, v___y_4588_, v___f_4567_, v___x_4597_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_);
return v___x_4598_;
}
v___jp_4599_:
{
lean_object* v___x_4600_; lean_object* v_a_4601_; lean_object* v___x_4602_; uint8_t v___x_4603_; 
v___x_4600_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___y_4561_);
v_a_4601_ = lean_ctor_get(v___x_4600_, 0);
lean_inc(v_a_4601_);
lean_dec_ref(v___x_4600_);
v___x_4602_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4603_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_4563_, v___x_4602_);
if (v___x_4603_ == 0)
{
lean_object* v___x_4604_; lean_object* v___x_4605_; 
v___x_4604_ = lean_io_mono_nanos_now();
lean_inc(v___y_4561_);
lean_inc_ref(v___y_4560_);
lean_inc(v___y_4559_);
lean_inc_ref(v___y_4558_);
v___x_4605_ = lean_apply_5(v_k_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, lean_box(0));
if (lean_obj_tag(v___x_4605_) == 0)
{
lean_object* v_a_4606_; lean_object* v___x_4608_; uint8_t v_isShared_4609_; uint8_t v_isSharedCheck_4613_; 
v_a_4606_ = lean_ctor_get(v___x_4605_, 0);
v_isSharedCheck_4613_ = !lean_is_exclusive(v___x_4605_);
if (v_isSharedCheck_4613_ == 0)
{
v___x_4608_ = v___x_4605_;
v_isShared_4609_ = v_isSharedCheck_4613_;
goto v_resetjp_4607_;
}
else
{
lean_inc(v_a_4606_);
lean_dec(v___x_4605_);
v___x_4608_ = lean_box(0);
v_isShared_4609_ = v_isSharedCheck_4613_;
goto v_resetjp_4607_;
}
v_resetjp_4607_:
{
lean_object* v___x_4611_; 
if (v_isShared_4609_ == 0)
{
lean_ctor_set_tag(v___x_4608_, 1);
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
v___y_4573_ = v___x_4604_;
v___y_4574_ = v_a_4601_;
v_a_4575_ = v___x_4611_;
goto v___jp_4572_;
}
}
}
else
{
lean_object* v_a_4614_; lean_object* v___x_4616_; uint8_t v_isShared_4617_; uint8_t v_isSharedCheck_4621_; 
v_a_4614_ = lean_ctor_get(v___x_4605_, 0);
v_isSharedCheck_4621_ = !lean_is_exclusive(v___x_4605_);
if (v_isSharedCheck_4621_ == 0)
{
v___x_4616_ = v___x_4605_;
v_isShared_4617_ = v_isSharedCheck_4621_;
goto v_resetjp_4615_;
}
else
{
lean_inc(v_a_4614_);
lean_dec(v___x_4605_);
v___x_4616_ = lean_box(0);
v_isShared_4617_ = v_isSharedCheck_4621_;
goto v_resetjp_4615_;
}
v_resetjp_4615_:
{
lean_object* v___x_4619_; 
if (v_isShared_4617_ == 0)
{
lean_ctor_set_tag(v___x_4616_, 0);
v___x_4619_ = v___x_4616_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4620_; 
v_reuseFailAlloc_4620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4620_, 0, v_a_4614_);
v___x_4619_ = v_reuseFailAlloc_4620_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
v___y_4573_ = v___x_4604_;
v___y_4574_ = v_a_4601_;
v_a_4575_ = v___x_4619_;
goto v___jp_4572_;
}
}
}
}
else
{
lean_object* v___x_4622_; lean_object* v___x_4623_; 
v___x_4622_ = lean_io_get_num_heartbeats();
lean_inc(v___y_4561_);
lean_inc_ref(v___y_4560_);
lean_inc(v___y_4559_);
lean_inc_ref(v___y_4558_);
v___x_4623_ = lean_apply_5(v_k_4557_, v___y_4558_, v___y_4559_, v___y_4560_, v___y_4561_, lean_box(0));
if (lean_obj_tag(v___x_4623_) == 0)
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4631_; 
v_a_4624_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4626_ = v___x_4623_;
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4623_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4629_; 
if (v_isShared_4627_ == 0)
{
lean_ctor_set_tag(v___x_4626_, 1);
v___x_4629_ = v___x_4626_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v_a_4624_);
v___x_4629_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
v___y_4588_ = v_a_4601_;
v___y_4589_ = v___x_4622_;
v_a_4590_ = v___x_4629_;
goto v___jp_4587_;
}
}
}
else
{
lean_object* v_a_4632_; lean_object* v___x_4634_; uint8_t v_isShared_4635_; uint8_t v_isSharedCheck_4639_; 
v_a_4632_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4639_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4639_ == 0)
{
v___x_4634_ = v___x_4623_;
v_isShared_4635_ = v_isSharedCheck_4639_;
goto v_resetjp_4633_;
}
else
{
lean_inc(v_a_4632_);
lean_dec(v___x_4623_);
v___x_4634_ = lean_box(0);
v_isShared_4635_ = v_isSharedCheck_4639_;
goto v_resetjp_4633_;
}
v_resetjp_4633_:
{
lean_object* v___x_4637_; 
if (v_isShared_4635_ == 0)
{
lean_ctor_set_tag(v___x_4634_, 0);
v___x_4637_ = v___x_4634_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v_a_4632_);
v___x_4637_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
v___y_4588_ = v_a_4601_;
v___y_4589_ = v___x_4622_;
v_a_4590_ = v___x_4637_;
goto v___jp_4587_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__10___boxed(lean_object* v___x_4643_, lean_object* v_hasTrace_4644_, lean_object* v_phase_4645_, lean_object* v_k_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_){
_start:
{
uint8_t v_hasTrace_boxed_4652_; lean_object* v_res_4653_; 
v_hasTrace_boxed_4652_ = lean_unbox(v_hasTrace_4644_);
v_res_4653_ = l_Lean_Elab_Tactic_NormCast_derive___lam__10(v___x_4643_, v_hasTrace_boxed_4652_, v_phase_4645_, v_k_4646_, v___y_4647_, v___y_4648_, v___y_4649_, v___y_4650_);
lean_dec(v___y_4650_);
lean_dec_ref(v___y_4649_);
lean_dec(v___y_4648_);
lean_dec_ref(v___y_4647_);
return v_res_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__9(lean_object* v___x_4654_, uint8_t v_hasTrace_4655_, lean_object* v_e_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_){
_start:
{
lean_object* v_a_4666_; lean_object* v___y_4670_; lean_object* v___x_4680_; 
lean_inc_ref(v_e_4656_);
v___x_4680_ = l_Lean_Elab_Tactic_NormCast_numeralToCoe(v_e_4656_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_);
if (lean_obj_tag(v___x_4680_) == 0)
{
lean_dec_ref(v_e_4656_);
lean_dec(v___x_4654_);
v___y_4670_ = v___x_4680_;
goto v___jp_4669_;
}
else
{
lean_object* v_a_4681_; uint8_t v___y_4683_; uint8_t v___x_4685_; 
v_a_4681_ = lean_ctor_get(v___x_4680_, 0);
lean_inc(v_a_4681_);
v___x_4685_ = l_Lean_Exception_isInterrupt(v_a_4681_);
if (v___x_4685_ == 0)
{
uint8_t v___x_4686_; 
v___x_4686_ = l_Lean_Exception_isRuntime(v_a_4681_);
v___y_4683_ = v___x_4686_;
goto v___jp_4682_;
}
else
{
lean_dec(v_a_4681_);
v___y_4683_ = v___x_4685_;
goto v___jp_4682_;
}
v___jp_4682_:
{
if (v___y_4683_ == 0)
{
lean_object* v___x_4684_; 
lean_dec_ref(v___x_4680_);
v___x_4684_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4684_, 0, v_e_4656_);
lean_ctor_set(v___x_4684_, 1, v___x_4654_);
lean_ctor_set_uint8(v___x_4684_, sizeof(void*)*2, v_hasTrace_4655_);
v_a_4666_ = v___x_4684_;
goto v___jp_4665_;
}
else
{
lean_dec_ref(v_e_4656_);
lean_dec(v___x_4654_);
v___y_4670_ = v___x_4680_;
goto v___jp_4669_;
}
}
}
v___jp_4665_:
{
lean_object* v___x_4667_; lean_object* v___x_4668_; 
v___x_4667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4667_, 0, v_a_4666_);
v___x_4668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4668_, 0, v___x_4667_);
return v___x_4668_;
}
v___jp_4669_:
{
if (lean_obj_tag(v___y_4670_) == 0)
{
lean_object* v_a_4671_; 
v_a_4671_ = lean_ctor_get(v___y_4670_, 0);
lean_inc(v_a_4671_);
lean_dec_ref(v___y_4670_);
v_a_4666_ = v_a_4671_;
goto v___jp_4665_;
}
else
{
lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4679_; 
v_a_4672_ = lean_ctor_get(v___y_4670_, 0);
v_isSharedCheck_4679_ = !lean_is_exclusive(v___y_4670_);
if (v_isSharedCheck_4679_ == 0)
{
v___x_4674_ = v___y_4670_;
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v___y_4670_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v___x_4677_; 
if (v_isShared_4675_ == 0)
{
v___x_4677_ = v___x_4674_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_a_4672_);
v___x_4677_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
return v___x_4677_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__9___boxed(lean_object* v___x_4687_, lean_object* v_hasTrace_4688_, lean_object* v_e_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_){
_start:
{
uint8_t v_hasTrace_boxed_4698_; lean_object* v_res_4699_; 
v_hasTrace_boxed_4698_ = lean_unbox(v_hasTrace_4688_);
v_res_4699_ = l_Lean_Elab_Tactic_NormCast_derive___lam__9(v___x_4687_, v_hasTrace_boxed_4698_, v_e_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_);
lean_dec(v___y_4696_);
lean_dec_ref(v___y_4695_);
lean_dec(v___y_4694_);
lean_dec_ref(v___y_4693_);
lean_dec(v___y_4692_);
lean_dec_ref(v___y_4691_);
lean_dec(v___y_4690_);
return v_res_4699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__14(lean_object* v_config_4700_, lean_object* v___x_4701_, lean_object* v_a_4702_, lean_object* v___x_4703_, lean_object* v___f_4704_, lean_object* v___f_4705_, lean_object* v___f_4706_, lean_object* v___f_4707_, lean_object* v___f_4708_, uint8_t v_hasTrace_4709_, lean_object* v_a_4710_, lean_object* v___x_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_, lean_object* v___y_4715_){
_start:
{
lean_object* v___x_4717_; 
v___x_4717_ = l_Lean_Meta_Simp_mkContext___redArg(v_config_4700_, v___x_4701_, v_a_4702_, v___y_4712_, v___y_4714_, v___y_4715_);
if (lean_obj_tag(v___x_4717_) == 0)
{
lean_object* v_a_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; size_t v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; 
v_a_4718_ = lean_ctor_get(v___x_4717_, 0);
lean_inc(v_a_4718_);
lean_dec_ref(v___x_4717_);
v___x_4719_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1, &l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1);
lean_inc_n(v___x_4703_, 2);
v___x_4720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4720_, 0, v___x_4719_);
lean_ctor_set(v___x_4720_, 1, v___x_4703_);
v___x_4721_ = lean_unsigned_to_nat(32u);
v___x_4722_ = lean_mk_empty_array_with_capacity(v___x_4721_);
v___x_4723_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8);
v___x_4724_ = ((size_t)5ULL);
v___x_4725_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4725_, 0, v___x_4723_);
lean_ctor_set(v___x_4725_, 1, v___x_4722_);
lean_ctor_set(v___x_4725_, 2, v___x_4703_);
lean_ctor_set(v___x_4725_, 3, v___x_4703_);
lean_ctor_set_usize(v___x_4725_, 4, v___x_4724_);
v___x_4726_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4726_, 0, v___x_4719_);
lean_ctor_set(v___x_4726_, 1, v___x_4719_);
lean_ctor_set(v___x_4726_, 2, v___x_4719_);
lean_ctor_set(v___x_4726_, 3, v___x_4725_);
v___x_4727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4727_, 0, v___x_4720_);
lean_ctor_set(v___x_4727_, 1, v___x_4726_);
v___x_4728_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4728_, 0, v___f_4704_);
lean_ctor_set(v___x_4728_, 1, v___f_4705_);
lean_ctor_set(v___x_4728_, 2, v___f_4706_);
lean_ctor_set(v___x_4728_, 3, v___f_4707_);
lean_ctor_set(v___x_4728_, 4, v___f_4708_);
lean_ctor_set_uint8(v___x_4728_, sizeof(void*)*5, v_hasTrace_4709_);
v___x_4729_ = l_Lean_Meta_Simp_main(v_a_4710_, v_a_4718_, v___x_4727_, v___x_4728_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_);
if (lean_obj_tag(v___x_4729_) == 0)
{
lean_object* v_a_4730_; lean_object* v_fst_4731_; lean_object* v___x_4732_; 
v_a_4730_ = lean_ctor_get(v___x_4729_, 0);
lean_inc(v_a_4730_);
lean_dec_ref(v___x_4729_);
v_fst_4731_ = lean_ctor_get(v_a_4730_, 0);
lean_inc(v_fst_4731_);
lean_dec(v_a_4730_);
v___x_4732_ = l_Lean_Meta_Simp_Result_mkEqTrans(v___x_4711_, v_fst_4731_, v___y_4712_, v___y_4713_, v___y_4714_, v___y_4715_);
return v___x_4732_;
}
else
{
lean_object* v_a_4733_; lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4740_; 
lean_dec_ref(v___x_4711_);
v_a_4733_ = lean_ctor_get(v___x_4729_, 0);
v_isSharedCheck_4740_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4740_ == 0)
{
v___x_4735_ = v___x_4729_;
v_isShared_4736_ = v_isSharedCheck_4740_;
goto v_resetjp_4734_;
}
else
{
lean_inc(v_a_4733_);
lean_dec(v___x_4729_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4740_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
lean_object* v___x_4738_; 
if (v_isShared_4736_ == 0)
{
v___x_4738_ = v___x_4735_;
goto v_reusejp_4737_;
}
else
{
lean_object* v_reuseFailAlloc_4739_; 
v_reuseFailAlloc_4739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4739_, 0, v_a_4733_);
v___x_4738_ = v_reuseFailAlloc_4739_;
goto v_reusejp_4737_;
}
v_reusejp_4737_:
{
return v___x_4738_;
}
}
}
}
else
{
lean_object* v_a_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4748_; 
lean_dec_ref(v___x_4711_);
lean_dec_ref(v_a_4710_);
lean_dec_ref(v___f_4708_);
lean_dec_ref(v___f_4707_);
lean_dec_ref(v___f_4706_);
lean_dec_ref(v___f_4705_);
lean_dec_ref(v___f_4704_);
lean_dec(v___x_4703_);
v_a_4741_ = lean_ctor_get(v___x_4717_, 0);
v_isSharedCheck_4748_ = !lean_is_exclusive(v___x_4717_);
if (v_isSharedCheck_4748_ == 0)
{
v___x_4743_ = v___x_4717_;
v_isShared_4744_ = v_isSharedCheck_4748_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_a_4741_);
lean_dec(v___x_4717_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4748_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v___x_4746_; 
if (v_isShared_4744_ == 0)
{
v___x_4746_ = v___x_4743_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v_a_4741_);
v___x_4746_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
return v___x_4746_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__14___boxed(lean_object** _args){
lean_object* v_config_4749_ = _args[0];
lean_object* v___x_4750_ = _args[1];
lean_object* v_a_4751_ = _args[2];
lean_object* v___x_4752_ = _args[3];
lean_object* v___f_4753_ = _args[4];
lean_object* v___f_4754_ = _args[5];
lean_object* v___f_4755_ = _args[6];
lean_object* v___f_4756_ = _args[7];
lean_object* v___f_4757_ = _args[8];
lean_object* v_hasTrace_4758_ = _args[9];
lean_object* v_a_4759_ = _args[10];
lean_object* v___x_4760_ = _args[11];
lean_object* v___y_4761_ = _args[12];
lean_object* v___y_4762_ = _args[13];
lean_object* v___y_4763_ = _args[14];
lean_object* v___y_4764_ = _args[15];
lean_object* v___y_4765_ = _args[16];
_start:
{
uint8_t v_hasTrace_boxed_4766_; lean_object* v_res_4767_; 
v_hasTrace_boxed_4766_ = lean_unbox(v_hasTrace_4758_);
v_res_4767_ = l_Lean_Elab_Tactic_NormCast_derive___lam__14(v_config_4749_, v___x_4750_, v_a_4751_, v___x_4752_, v___f_4753_, v___f_4754_, v___f_4755_, v___f_4756_, v___f_4757_, v_hasTrace_boxed_4766_, v_a_4759_, v___x_4760_, v___y_4761_, v___y_4762_, v___y_4763_, v___y_4764_);
lean_dec(v___y_4764_);
lean_dec_ref(v___y_4763_);
lean_dec(v___y_4762_);
lean_dec_ref(v___y_4761_);
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__15(lean_object* v_up_4768_, lean_object* v_config_4769_, lean_object* v___x_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v___x_4773_, lean_object* v___f_4774_, lean_object* v___f_4775_, lean_object* v___f_4776_, lean_object* v___f_4777_, uint8_t v_hasTrace_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_){
_start:
{
lean_object* v___x_4784_; 
v___x_4784_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_up_4768_, v___y_4782_);
if (lean_obj_tag(v___x_4784_) == 0)
{
lean_object* v_a_4785_; lean_object* v___x_4786_; 
v_a_4785_ = lean_ctor_get(v___x_4784_, 0);
lean_inc(v_a_4785_);
lean_dec_ref(v___x_4784_);
v___x_4786_ = l_Lean_Meta_Simp_mkContext___redArg(v_config_4769_, v___x_4770_, v_a_4771_, v___y_4779_, v___y_4781_, v___y_4782_);
if (lean_obj_tag(v___x_4786_) == 0)
{
lean_object* v_a_4787_; lean_object* v_expr_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; size_t v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; 
v_a_4787_ = lean_ctor_get(v___x_4786_, 0);
lean_inc(v_a_4787_);
lean_dec_ref(v___x_4786_);
v_expr_4788_ = lean_ctor_get(v_a_4772_, 0);
v___x_4789_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_upwardAndElim___boxed), 10, 1);
lean_closure_set(v___x_4789_, 0, v_a_4785_);
v___x_4790_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1, &l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1);
lean_inc_n(v___x_4773_, 2);
v___x_4791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4791_, 0, v___x_4790_);
lean_ctor_set(v___x_4791_, 1, v___x_4773_);
v___x_4792_ = lean_unsigned_to_nat(32u);
v___x_4793_ = lean_mk_empty_array_with_capacity(v___x_4792_);
v___x_4794_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8);
v___x_4795_ = ((size_t)5ULL);
v___x_4796_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4796_, 0, v___x_4794_);
lean_ctor_set(v___x_4796_, 1, v___x_4793_);
lean_ctor_set(v___x_4796_, 2, v___x_4773_);
lean_ctor_set(v___x_4796_, 3, v___x_4773_);
lean_ctor_set_usize(v___x_4796_, 4, v___x_4795_);
v___x_4797_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4797_, 0, v___x_4790_);
lean_ctor_set(v___x_4797_, 1, v___x_4790_);
lean_ctor_set(v___x_4797_, 2, v___x_4790_);
lean_ctor_set(v___x_4797_, 3, v___x_4796_);
v___x_4798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4798_, 0, v___x_4791_);
lean_ctor_set(v___x_4798_, 1, v___x_4797_);
v___x_4799_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4799_, 0, v___f_4774_);
lean_ctor_set(v___x_4799_, 1, v___x_4789_);
lean_ctor_set(v___x_4799_, 2, v___f_4775_);
lean_ctor_set(v___x_4799_, 3, v___f_4776_);
lean_ctor_set(v___x_4799_, 4, v___f_4777_);
lean_ctor_set_uint8(v___x_4799_, sizeof(void*)*5, v_hasTrace_4778_);
lean_inc_ref(v_expr_4788_);
v___x_4800_ = l_Lean_Meta_Simp_main(v_expr_4788_, v_a_4787_, v___x_4798_, v___x_4799_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_);
if (lean_obj_tag(v___x_4800_) == 0)
{
lean_object* v_a_4801_; lean_object* v_fst_4802_; lean_object* v___x_4803_; 
v_a_4801_ = lean_ctor_get(v___x_4800_, 0);
lean_inc(v_a_4801_);
lean_dec_ref(v___x_4800_);
v_fst_4802_ = lean_ctor_get(v_a_4801_, 0);
lean_inc(v_fst_4802_);
lean_dec(v_a_4801_);
v___x_4803_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_4772_, v_fst_4802_, v___y_4779_, v___y_4780_, v___y_4781_, v___y_4782_);
return v___x_4803_;
}
else
{
lean_object* v_a_4804_; lean_object* v___x_4806_; uint8_t v_isShared_4807_; uint8_t v_isSharedCheck_4811_; 
lean_dec_ref(v_a_4772_);
v_a_4804_ = lean_ctor_get(v___x_4800_, 0);
v_isSharedCheck_4811_ = !lean_is_exclusive(v___x_4800_);
if (v_isSharedCheck_4811_ == 0)
{
v___x_4806_ = v___x_4800_;
v_isShared_4807_ = v_isSharedCheck_4811_;
goto v_resetjp_4805_;
}
else
{
lean_inc(v_a_4804_);
lean_dec(v___x_4800_);
v___x_4806_ = lean_box(0);
v_isShared_4807_ = v_isSharedCheck_4811_;
goto v_resetjp_4805_;
}
v_resetjp_4805_:
{
lean_object* v___x_4809_; 
if (v_isShared_4807_ == 0)
{
v___x_4809_ = v___x_4806_;
goto v_reusejp_4808_;
}
else
{
lean_object* v_reuseFailAlloc_4810_; 
v_reuseFailAlloc_4810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4810_, 0, v_a_4804_);
v___x_4809_ = v_reuseFailAlloc_4810_;
goto v_reusejp_4808_;
}
v_reusejp_4808_:
{
return v___x_4809_;
}
}
}
}
else
{
lean_object* v_a_4812_; lean_object* v___x_4814_; uint8_t v_isShared_4815_; uint8_t v_isSharedCheck_4819_; 
lean_dec(v_a_4785_);
lean_dec_ref(v___f_4777_);
lean_dec_ref(v___f_4776_);
lean_dec_ref(v___f_4775_);
lean_dec_ref(v___f_4774_);
lean_dec(v___x_4773_);
lean_dec_ref(v_a_4772_);
v_a_4812_ = lean_ctor_get(v___x_4786_, 0);
v_isSharedCheck_4819_ = !lean_is_exclusive(v___x_4786_);
if (v_isSharedCheck_4819_ == 0)
{
v___x_4814_ = v___x_4786_;
v_isShared_4815_ = v_isSharedCheck_4819_;
goto v_resetjp_4813_;
}
else
{
lean_inc(v_a_4812_);
lean_dec(v___x_4786_);
v___x_4814_ = lean_box(0);
v_isShared_4815_ = v_isSharedCheck_4819_;
goto v_resetjp_4813_;
}
v_resetjp_4813_:
{
lean_object* v___x_4817_; 
if (v_isShared_4815_ == 0)
{
v___x_4817_ = v___x_4814_;
goto v_reusejp_4816_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v_a_4812_);
v___x_4817_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4816_;
}
v_reusejp_4816_:
{
return v___x_4817_;
}
}
}
}
else
{
lean_object* v_a_4820_; lean_object* v___x_4822_; uint8_t v_isShared_4823_; uint8_t v_isSharedCheck_4827_; 
lean_dec_ref(v___f_4777_);
lean_dec_ref(v___f_4776_);
lean_dec_ref(v___f_4775_);
lean_dec_ref(v___f_4774_);
lean_dec(v___x_4773_);
lean_dec_ref(v_a_4772_);
lean_dec_ref(v_a_4771_);
lean_dec_ref(v___x_4770_);
lean_dec_ref(v_config_4769_);
v_a_4820_ = lean_ctor_get(v___x_4784_, 0);
v_isSharedCheck_4827_ = !lean_is_exclusive(v___x_4784_);
if (v_isSharedCheck_4827_ == 0)
{
v___x_4822_ = v___x_4784_;
v_isShared_4823_ = v_isSharedCheck_4827_;
goto v_resetjp_4821_;
}
else
{
lean_inc(v_a_4820_);
lean_dec(v___x_4784_);
v___x_4822_ = lean_box(0);
v_isShared_4823_ = v_isSharedCheck_4827_;
goto v_resetjp_4821_;
}
v_resetjp_4821_:
{
lean_object* v___x_4825_; 
if (v_isShared_4823_ == 0)
{
v___x_4825_ = v___x_4822_;
goto v_reusejp_4824_;
}
else
{
lean_object* v_reuseFailAlloc_4826_; 
v_reuseFailAlloc_4826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4826_, 0, v_a_4820_);
v___x_4825_ = v_reuseFailAlloc_4826_;
goto v_reusejp_4824_;
}
v_reusejp_4824_:
{
return v___x_4825_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__15___boxed(lean_object* v_up_4828_, lean_object* v_config_4829_, lean_object* v___x_4830_, lean_object* v_a_4831_, lean_object* v_a_4832_, lean_object* v___x_4833_, lean_object* v___f_4834_, lean_object* v___f_4835_, lean_object* v___f_4836_, lean_object* v___f_4837_, lean_object* v_hasTrace_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_){
_start:
{
uint8_t v_hasTrace_boxed_4844_; lean_object* v_res_4845_; 
v_hasTrace_boxed_4844_ = lean_unbox(v_hasTrace_4838_);
v_res_4845_ = l_Lean_Elab_Tactic_NormCast_derive___lam__15(v_up_4828_, v_config_4829_, v___x_4830_, v_a_4831_, v_a_4832_, v___x_4833_, v___f_4834_, v___f_4835_, v___f_4836_, v___f_4837_, v_hasTrace_boxed_4844_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_);
lean_dec(v___y_4842_);
lean_dec_ref(v___y_4841_);
lean_dec(v___y_4840_);
lean_dec_ref(v___y_4839_);
lean_dec_ref(v_up_4828_);
return v_res_4845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__16(lean_object* v___x_4846_, uint8_t v___x_4847_, lean_object* v___x_4848_, lean_object* v___x_4849_, lean_object* v_phase_4850_, lean_object* v_k_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_){
_start:
{
lean_object* v_options_4857_; uint8_t v_hasTrace_4858_; 
v_options_4857_ = lean_ctor_get(v___y_4854_, 2);
v_hasTrace_4858_ = lean_ctor_get_uint8(v_options_4857_, sizeof(void*)*1);
if (v_hasTrace_4858_ == 0)
{
lean_object* v___x_4859_; 
lean_dec_ref(v_phase_4850_);
lean_dec_ref(v___x_4848_);
lean_dec(v___x_4846_);
lean_inc(v___y_4855_);
lean_inc_ref(v___y_4854_);
lean_inc(v___y_4853_);
lean_inc_ref(v___y_4852_);
v___x_4859_ = lean_apply_5(v_k_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, lean_box(0));
return v___x_4859_;
}
else
{
lean_object* v_inheritedTraceOptions_4860_; lean_object* v___f_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; uint8_t v___x_4864_; lean_object* v___y_4866_; lean_object* v___y_4867_; lean_object* v_a_4868_; lean_object* v___y_4881_; lean_object* v___y_4882_; lean_object* v_a_4883_; 
v_inheritedTraceOptions_4860_ = lean_ctor_get(v___y_4854_, 13);
v___f_4861_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4861_, 0, v_phase_4850_);
v___x_4862_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__2));
lean_inc(v___x_4846_);
v___x_4863_ = l_Lean_Name_append(v___x_4862_, v___x_4846_);
v___x_4864_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4860_, v_options_4857_, v___x_4863_);
lean_dec(v___x_4863_);
if (v___x_4864_ == 0)
{
lean_object* v___x_4932_; uint8_t v___x_4933_; 
v___x_4932_ = l_Lean_trace_profiler;
v___x_4933_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_4857_, v___x_4932_);
if (v___x_4933_ == 0)
{
lean_object* v___x_4934_; 
lean_dec_ref(v___f_4861_);
lean_dec_ref(v___x_4848_);
lean_dec(v___x_4846_);
lean_inc(v___y_4855_);
lean_inc_ref(v___y_4854_);
lean_inc(v___y_4853_);
lean_inc_ref(v___y_4852_);
v___x_4934_ = lean_apply_5(v_k_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, lean_box(0));
return v___x_4934_;
}
else
{
goto v___jp_4892_;
}
}
else
{
goto v___jp_4892_;
}
v___jp_4865_:
{
lean_object* v___x_4869_; double v___x_4870_; double v___x_4871_; double v___x_4872_; double v___x_4873_; double v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4869_ = lean_io_mono_nanos_now();
v___x_4870_ = lean_float_of_nat(v___y_4867_);
v___x_4871_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4);
v___x_4872_ = lean_float_div(v___x_4870_, v___x_4871_);
v___x_4873_ = lean_float_of_nat(v___x_4869_);
v___x_4874_ = lean_float_div(v___x_4873_, v___x_4871_);
v___x_4875_ = lean_box_float(v___x_4872_);
v___x_4876_ = lean_box_float(v___x_4874_);
v___x_4877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4875_);
lean_ctor_set(v___x_4877_, 1, v___x_4876_);
v___x_4878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4878_, 0, v_a_4868_);
lean_ctor_set(v___x_4878_, 1, v___x_4877_);
v___x_4879_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4846_, v___x_4847_, v___x_4848_, v_options_4857_, v___x_4864_, v___y_4866_, v___f_4861_, v___x_4878_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_);
return v___x_4879_;
}
v___jp_4880_:
{
lean_object* v___x_4884_; double v___x_4885_; double v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; 
v___x_4884_ = lean_io_get_num_heartbeats();
v___x_4885_ = lean_float_of_nat(v___y_4882_);
v___x_4886_ = lean_float_of_nat(v___x_4884_);
v___x_4887_ = lean_box_float(v___x_4885_);
v___x_4888_ = lean_box_float(v___x_4886_);
v___x_4889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4889_, 0, v___x_4887_);
lean_ctor_set(v___x_4889_, 1, v___x_4888_);
v___x_4890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4890_, 0, v_a_4883_);
lean_ctor_set(v___x_4890_, 1, v___x_4889_);
v___x_4891_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4846_, v___x_4847_, v___x_4848_, v_options_4857_, v___x_4864_, v___y_4881_, v___f_4861_, v___x_4890_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_);
return v___x_4891_;
}
v___jp_4892_:
{
lean_object* v___x_4893_; lean_object* v_a_4894_; uint8_t v___x_4895_; 
v___x_4893_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___y_4855_);
v_a_4894_ = lean_ctor_get(v___x_4893_, 0);
lean_inc(v_a_4894_);
lean_dec_ref(v___x_4893_);
v___x_4895_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_4857_, v___x_4849_);
if (v___x_4895_ == 0)
{
lean_object* v___x_4896_; lean_object* v___x_4897_; 
v___x_4896_ = lean_io_mono_nanos_now();
lean_inc(v___y_4855_);
lean_inc_ref(v___y_4854_);
lean_inc(v___y_4853_);
lean_inc_ref(v___y_4852_);
v___x_4897_ = lean_apply_5(v_k_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, lean_box(0));
if (lean_obj_tag(v___x_4897_) == 0)
{
lean_object* v_a_4898_; lean_object* v___x_4900_; uint8_t v_isShared_4901_; uint8_t v_isSharedCheck_4905_; 
v_a_4898_ = lean_ctor_get(v___x_4897_, 0);
v_isSharedCheck_4905_ = !lean_is_exclusive(v___x_4897_);
if (v_isSharedCheck_4905_ == 0)
{
v___x_4900_ = v___x_4897_;
v_isShared_4901_ = v_isSharedCheck_4905_;
goto v_resetjp_4899_;
}
else
{
lean_inc(v_a_4898_);
lean_dec(v___x_4897_);
v___x_4900_ = lean_box(0);
v_isShared_4901_ = v_isSharedCheck_4905_;
goto v_resetjp_4899_;
}
v_resetjp_4899_:
{
lean_object* v___x_4903_; 
if (v_isShared_4901_ == 0)
{
lean_ctor_set_tag(v___x_4900_, 1);
v___x_4903_ = v___x_4900_;
goto v_reusejp_4902_;
}
else
{
lean_object* v_reuseFailAlloc_4904_; 
v_reuseFailAlloc_4904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4904_, 0, v_a_4898_);
v___x_4903_ = v_reuseFailAlloc_4904_;
goto v_reusejp_4902_;
}
v_reusejp_4902_:
{
v___y_4866_ = v_a_4894_;
v___y_4867_ = v___x_4896_;
v_a_4868_ = v___x_4903_;
goto v___jp_4865_;
}
}
}
else
{
lean_object* v_a_4906_; lean_object* v___x_4908_; uint8_t v_isShared_4909_; uint8_t v_isSharedCheck_4913_; 
v_a_4906_ = lean_ctor_get(v___x_4897_, 0);
v_isSharedCheck_4913_ = !lean_is_exclusive(v___x_4897_);
if (v_isSharedCheck_4913_ == 0)
{
v___x_4908_ = v___x_4897_;
v_isShared_4909_ = v_isSharedCheck_4913_;
goto v_resetjp_4907_;
}
else
{
lean_inc(v_a_4906_);
lean_dec(v___x_4897_);
v___x_4908_ = lean_box(0);
v_isShared_4909_ = v_isSharedCheck_4913_;
goto v_resetjp_4907_;
}
v_resetjp_4907_:
{
lean_object* v___x_4911_; 
if (v_isShared_4909_ == 0)
{
lean_ctor_set_tag(v___x_4908_, 0);
v___x_4911_ = v___x_4908_;
goto v_reusejp_4910_;
}
else
{
lean_object* v_reuseFailAlloc_4912_; 
v_reuseFailAlloc_4912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4912_, 0, v_a_4906_);
v___x_4911_ = v_reuseFailAlloc_4912_;
goto v_reusejp_4910_;
}
v_reusejp_4910_:
{
v___y_4866_ = v_a_4894_;
v___y_4867_ = v___x_4896_;
v_a_4868_ = v___x_4911_;
goto v___jp_4865_;
}
}
}
}
else
{
lean_object* v___x_4914_; lean_object* v___x_4915_; 
v___x_4914_ = lean_io_get_num_heartbeats();
lean_inc(v___y_4855_);
lean_inc_ref(v___y_4854_);
lean_inc(v___y_4853_);
lean_inc_ref(v___y_4852_);
v___x_4915_ = lean_apply_5(v_k_4851_, v___y_4852_, v___y_4853_, v___y_4854_, v___y_4855_, lean_box(0));
if (lean_obj_tag(v___x_4915_) == 0)
{
lean_object* v_a_4916_; lean_object* v___x_4918_; uint8_t v_isShared_4919_; uint8_t v_isSharedCheck_4923_; 
v_a_4916_ = lean_ctor_get(v___x_4915_, 0);
v_isSharedCheck_4923_ = !lean_is_exclusive(v___x_4915_);
if (v_isSharedCheck_4923_ == 0)
{
v___x_4918_ = v___x_4915_;
v_isShared_4919_ = v_isSharedCheck_4923_;
goto v_resetjp_4917_;
}
else
{
lean_inc(v_a_4916_);
lean_dec(v___x_4915_);
v___x_4918_ = lean_box(0);
v_isShared_4919_ = v_isSharedCheck_4923_;
goto v_resetjp_4917_;
}
v_resetjp_4917_:
{
lean_object* v___x_4921_; 
if (v_isShared_4919_ == 0)
{
lean_ctor_set_tag(v___x_4918_, 1);
v___x_4921_ = v___x_4918_;
goto v_reusejp_4920_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_a_4916_);
v___x_4921_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4920_;
}
v_reusejp_4920_:
{
v___y_4881_ = v_a_4894_;
v___y_4882_ = v___x_4914_;
v_a_4883_ = v___x_4921_;
goto v___jp_4880_;
}
}
}
else
{
lean_object* v_a_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4931_; 
v_a_4924_ = lean_ctor_get(v___x_4915_, 0);
v_isSharedCheck_4931_ = !lean_is_exclusive(v___x_4915_);
if (v_isSharedCheck_4931_ == 0)
{
v___x_4926_ = v___x_4915_;
v_isShared_4927_ = v_isSharedCheck_4931_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_a_4924_);
lean_dec(v___x_4915_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4931_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v___x_4929_; 
if (v_isShared_4927_ == 0)
{
lean_ctor_set_tag(v___x_4926_, 0);
v___x_4929_ = v___x_4926_;
goto v_reusejp_4928_;
}
else
{
lean_object* v_reuseFailAlloc_4930_; 
v_reuseFailAlloc_4930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4930_, 0, v_a_4924_);
v___x_4929_ = v_reuseFailAlloc_4930_;
goto v_reusejp_4928_;
}
v_reusejp_4928_:
{
v___y_4881_ = v_a_4894_;
v___y_4882_ = v___x_4914_;
v_a_4883_ = v___x_4929_;
goto v___jp_4880_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__16___boxed(lean_object* v___x_4935_, lean_object* v___x_4936_, lean_object* v___x_4937_, lean_object* v___x_4938_, lean_object* v_phase_4939_, lean_object* v_k_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_){
_start:
{
uint8_t v___x_36330__boxed_4946_; lean_object* v_res_4947_; 
v___x_36330__boxed_4946_ = lean_unbox(v___x_4936_);
v_res_4947_ = l_Lean_Elab_Tactic_NormCast_derive___lam__16(v___x_4935_, v___x_36330__boxed_4946_, v___x_4937_, v___x_4938_, v_phase_4939_, v_k_4940_, v___y_4941_, v___y_4942_, v___y_4943_, v___y_4944_);
lean_dec(v___y_4944_);
lean_dec_ref(v___y_4943_);
lean_dec(v___y_4942_);
lean_dec_ref(v___y_4941_);
lean_dec_ref(v___x_4938_);
return v_res_4947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__27(lean_object* v___x_4948_, uint8_t v_hasTrace_4949_, lean_object* v_phase_4950_, lean_object* v_k_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_){
_start:
{
lean_object* v_options_4957_; uint8_t v_hasTrace_4958_; 
v_options_4957_ = lean_ctor_get(v___y_4954_, 2);
v_hasTrace_4958_ = lean_ctor_get_uint8(v_options_4957_, sizeof(void*)*1);
if (v_hasTrace_4958_ == 0)
{
lean_object* v___x_4959_; 
lean_dec_ref(v_phase_4950_);
lean_dec(v___x_4948_);
lean_inc(v___y_4955_);
lean_inc_ref(v___y_4954_);
lean_inc(v___y_4953_);
lean_inc_ref(v___y_4952_);
v___x_4959_ = lean_apply_5(v_k_4951_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_, lean_box(0));
return v___x_4959_;
}
else
{
lean_object* v_inheritedTraceOptions_4960_; lean_object* v___f_4961_; lean_object* v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; uint8_t v___x_4965_; lean_object* v___y_4967_; lean_object* v___y_4968_; lean_object* v_a_4969_; lean_object* v___y_4982_; lean_object* v___y_4983_; lean_object* v_a_4984_; 
v_inheritedTraceOptions_4960_ = lean_ctor_get(v___y_4954_, 13);
v___f_4961_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4961_, 0, v_phase_4950_);
v___x_4962_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_4963_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__2));
lean_inc(v___x_4948_);
v___x_4964_ = l_Lean_Name_append(v___x_4963_, v___x_4948_);
v___x_4965_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4960_, v_options_4957_, v___x_4964_);
lean_dec(v___x_4964_);
if (v___x_4965_ == 0)
{
lean_object* v___x_5034_; uint8_t v___x_5035_; 
v___x_5034_ = l_Lean_trace_profiler;
v___x_5035_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_4957_, v___x_5034_);
if (v___x_5035_ == 0)
{
lean_object* v___x_5036_; 
lean_dec_ref(v___f_4961_);
lean_dec(v___x_4948_);
lean_inc(v___y_4955_);
lean_inc_ref(v___y_4954_);
lean_inc(v___y_4953_);
lean_inc_ref(v___y_4952_);
v___x_5036_ = lean_apply_5(v_k_4951_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_, lean_box(0));
return v___x_5036_;
}
else
{
goto v___jp_4993_;
}
}
else
{
goto v___jp_4993_;
}
v___jp_4966_:
{
lean_object* v___x_4970_; double v___x_4971_; double v___x_4972_; double v___x_4973_; double v___x_4974_; double v___x_4975_; lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; 
v___x_4970_ = lean_io_mono_nanos_now();
v___x_4971_ = lean_float_of_nat(v___y_4968_);
v___x_4972_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4);
v___x_4973_ = lean_float_div(v___x_4971_, v___x_4972_);
v___x_4974_ = lean_float_of_nat(v___x_4970_);
v___x_4975_ = lean_float_div(v___x_4974_, v___x_4972_);
v___x_4976_ = lean_box_float(v___x_4973_);
v___x_4977_ = lean_box_float(v___x_4975_);
v___x_4978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4978_, 0, v___x_4976_);
lean_ctor_set(v___x_4978_, 1, v___x_4977_);
v___x_4979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4979_, 0, v_a_4969_);
lean_ctor_set(v___x_4979_, 1, v___x_4978_);
v___x_4980_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4948_, v_hasTrace_4949_, v___x_4962_, v_options_4957_, v___x_4965_, v___y_4967_, v___f_4961_, v___x_4979_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_);
return v___x_4980_;
}
v___jp_4981_:
{
lean_object* v___x_4985_; double v___x_4986_; double v___x_4987_; lean_object* v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; 
v___x_4985_ = lean_io_get_num_heartbeats();
v___x_4986_ = lean_float_of_nat(v___y_4983_);
v___x_4987_ = lean_float_of_nat(v___x_4985_);
v___x_4988_ = lean_box_float(v___x_4986_);
v___x_4989_ = lean_box_float(v___x_4987_);
v___x_4990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4990_, 0, v___x_4988_);
lean_ctor_set(v___x_4990_, 1, v___x_4989_);
v___x_4991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4991_, 0, v_a_4984_);
lean_ctor_set(v___x_4991_, 1, v___x_4990_);
v___x_4992_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4948_, v_hasTrace_4949_, v___x_4962_, v_options_4957_, v___x_4965_, v___y_4982_, v___f_4961_, v___x_4991_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_);
return v___x_4992_;
}
v___jp_4993_:
{
lean_object* v___x_4994_; lean_object* v_a_4995_; lean_object* v___x_4996_; uint8_t v___x_4997_; 
v___x_4994_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___y_4955_);
v_a_4995_ = lean_ctor_get(v___x_4994_, 0);
lean_inc(v_a_4995_);
lean_dec_ref(v___x_4994_);
v___x_4996_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4997_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_4957_, v___x_4996_);
if (v___x_4997_ == 0)
{
lean_object* v___x_4998_; lean_object* v___x_4999_; 
v___x_4998_ = lean_io_mono_nanos_now();
lean_inc(v___y_4955_);
lean_inc_ref(v___y_4954_);
lean_inc(v___y_4953_);
lean_inc_ref(v___y_4952_);
v___x_4999_ = lean_apply_5(v_k_4951_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_, lean_box(0));
if (lean_obj_tag(v___x_4999_) == 0)
{
lean_object* v_a_5000_; lean_object* v___x_5002_; uint8_t v_isShared_5003_; uint8_t v_isSharedCheck_5007_; 
v_a_5000_ = lean_ctor_get(v___x_4999_, 0);
v_isSharedCheck_5007_ = !lean_is_exclusive(v___x_4999_);
if (v_isSharedCheck_5007_ == 0)
{
v___x_5002_ = v___x_4999_;
v_isShared_5003_ = v_isSharedCheck_5007_;
goto v_resetjp_5001_;
}
else
{
lean_inc(v_a_5000_);
lean_dec(v___x_4999_);
v___x_5002_ = lean_box(0);
v_isShared_5003_ = v_isSharedCheck_5007_;
goto v_resetjp_5001_;
}
v_resetjp_5001_:
{
lean_object* v___x_5005_; 
if (v_isShared_5003_ == 0)
{
lean_ctor_set_tag(v___x_5002_, 1);
v___x_5005_ = v___x_5002_;
goto v_reusejp_5004_;
}
else
{
lean_object* v_reuseFailAlloc_5006_; 
v_reuseFailAlloc_5006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5006_, 0, v_a_5000_);
v___x_5005_ = v_reuseFailAlloc_5006_;
goto v_reusejp_5004_;
}
v_reusejp_5004_:
{
v___y_4967_ = v_a_4995_;
v___y_4968_ = v___x_4998_;
v_a_4969_ = v___x_5005_;
goto v___jp_4966_;
}
}
}
else
{
lean_object* v_a_5008_; lean_object* v___x_5010_; uint8_t v_isShared_5011_; uint8_t v_isSharedCheck_5015_; 
v_a_5008_ = lean_ctor_get(v___x_4999_, 0);
v_isSharedCheck_5015_ = !lean_is_exclusive(v___x_4999_);
if (v_isSharedCheck_5015_ == 0)
{
v___x_5010_ = v___x_4999_;
v_isShared_5011_ = v_isSharedCheck_5015_;
goto v_resetjp_5009_;
}
else
{
lean_inc(v_a_5008_);
lean_dec(v___x_4999_);
v___x_5010_ = lean_box(0);
v_isShared_5011_ = v_isSharedCheck_5015_;
goto v_resetjp_5009_;
}
v_resetjp_5009_:
{
lean_object* v___x_5013_; 
if (v_isShared_5011_ == 0)
{
lean_ctor_set_tag(v___x_5010_, 0);
v___x_5013_ = v___x_5010_;
goto v_reusejp_5012_;
}
else
{
lean_object* v_reuseFailAlloc_5014_; 
v_reuseFailAlloc_5014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5014_, 0, v_a_5008_);
v___x_5013_ = v_reuseFailAlloc_5014_;
goto v_reusejp_5012_;
}
v_reusejp_5012_:
{
v___y_4967_ = v_a_4995_;
v___y_4968_ = v___x_4998_;
v_a_4969_ = v___x_5013_;
goto v___jp_4966_;
}
}
}
}
else
{
lean_object* v___x_5016_; lean_object* v___x_5017_; 
v___x_5016_ = lean_io_get_num_heartbeats();
lean_inc(v___y_4955_);
lean_inc_ref(v___y_4954_);
lean_inc(v___y_4953_);
lean_inc_ref(v___y_4952_);
v___x_5017_ = lean_apply_5(v_k_4951_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_, lean_box(0));
if (lean_obj_tag(v___x_5017_) == 0)
{
lean_object* v_a_5018_; lean_object* v___x_5020_; uint8_t v_isShared_5021_; uint8_t v_isSharedCheck_5025_; 
v_a_5018_ = lean_ctor_get(v___x_5017_, 0);
v_isSharedCheck_5025_ = !lean_is_exclusive(v___x_5017_);
if (v_isSharedCheck_5025_ == 0)
{
v___x_5020_ = v___x_5017_;
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
else
{
lean_inc(v_a_5018_);
lean_dec(v___x_5017_);
v___x_5020_ = lean_box(0);
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
v_resetjp_5019_:
{
lean_object* v___x_5023_; 
if (v_isShared_5021_ == 0)
{
lean_ctor_set_tag(v___x_5020_, 1);
v___x_5023_ = v___x_5020_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5024_; 
v_reuseFailAlloc_5024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5024_, 0, v_a_5018_);
v___x_5023_ = v_reuseFailAlloc_5024_;
goto v_reusejp_5022_;
}
v_reusejp_5022_:
{
v___y_4982_ = v_a_4995_;
v___y_4983_ = v___x_5016_;
v_a_4984_ = v___x_5023_;
goto v___jp_4981_;
}
}
}
else
{
lean_object* v_a_5026_; lean_object* v___x_5028_; uint8_t v_isShared_5029_; uint8_t v_isSharedCheck_5033_; 
v_a_5026_ = lean_ctor_get(v___x_5017_, 0);
v_isSharedCheck_5033_ = !lean_is_exclusive(v___x_5017_);
if (v_isSharedCheck_5033_ == 0)
{
v___x_5028_ = v___x_5017_;
v_isShared_5029_ = v_isSharedCheck_5033_;
goto v_resetjp_5027_;
}
else
{
lean_inc(v_a_5026_);
lean_dec(v___x_5017_);
v___x_5028_ = lean_box(0);
v_isShared_5029_ = v_isSharedCheck_5033_;
goto v_resetjp_5027_;
}
v_resetjp_5027_:
{
lean_object* v___x_5031_; 
if (v_isShared_5029_ == 0)
{
lean_ctor_set_tag(v___x_5028_, 0);
v___x_5031_ = v___x_5028_;
goto v_reusejp_5030_;
}
else
{
lean_object* v_reuseFailAlloc_5032_; 
v_reuseFailAlloc_5032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5032_, 0, v_a_5026_);
v___x_5031_ = v_reuseFailAlloc_5032_;
goto v_reusejp_5030_;
}
v_reusejp_5030_:
{
v___y_4982_ = v_a_4995_;
v___y_4983_ = v___x_5016_;
v_a_4984_ = v___x_5031_;
goto v___jp_4981_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__27___boxed(lean_object* v___x_5037_, lean_object* v_hasTrace_5038_, lean_object* v_phase_5039_, lean_object* v_k_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_){
_start:
{
uint8_t v_hasTrace_boxed_5046_; lean_object* v_res_5047_; 
v_hasTrace_boxed_5046_ = lean_unbox(v_hasTrace_5038_);
v_res_5047_ = l_Lean_Elab_Tactic_NormCast_derive___lam__27(v___x_5037_, v_hasTrace_boxed_5046_, v_phase_5039_, v_k_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_);
lean_dec(v___y_5044_);
lean_dec_ref(v___y_5043_);
lean_dec(v___y_5042_);
lean_dec_ref(v___y_5041_);
return v_res_5047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive(lean_object* v_e_5066_, lean_object* v_config_5067_, lean_object* v_a_5068_, lean_object* v_a_5069_, lean_object* v_a_5070_, lean_object* v_a_5071_){
_start:
{
lean_object* v_options_5073_; lean_object* v_inheritedTraceOptions_5074_; uint8_t v_hasTrace_5075_; lean_object* v___x_5076_; 
v_options_5073_ = lean_ctor_get(v_a_5070_, 2);
v_inheritedTraceOptions_5074_ = lean_ctor_get(v_a_5070_, 13);
v_hasTrace_5075_ = lean_ctor_get_uint8(v_options_5073_, sizeof(void*)*1);
v___x_5076_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__2_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_));
if (v_hasTrace_5075_ == 0)
{
lean_object* v___x_5077_; lean_object* v_a_5078_; lean_object* v___x_5079_; 
v___x_5077_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_e_5066_, v_a_5069_);
v_a_5078_ = lean_ctor_get(v___x_5077_, 0);
lean_inc(v_a_5078_);
lean_dec_ref(v___x_5077_);
v___x_5079_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_5071_);
if (lean_obj_tag(v___x_5079_) == 0)
{
lean_object* v_a_5080_; lean_object* v___f_5081_; lean_object* v___f_5082_; lean_object* v___x_5083_; lean_object* v___f_5084_; lean_object* v___f_5085_; uint8_t v___x_5086_; lean_object* v___f_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___f_5093_; lean_object* v___x_5094_; 
v_a_5080_ = lean_ctor_get(v___x_5079_, 0);
lean_inc_n(v_a_5080_, 2);
lean_dec_ref(v___x_5079_);
v___f_5081_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__0));
v___f_5082_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__1));
v___x_5083_ = lean_box(0);
v___f_5084_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__2));
v___f_5085_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__3));
v___x_5086_ = 1;
v___f_5087_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__4));
lean_inc(v_a_5078_);
v___x_5088_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5088_, 0, v_a_5078_);
lean_ctor_set(v___x_5088_, 1, v___x_5083_);
lean_ctor_set_uint8(v___x_5088_, sizeof(void*)*2, v___x_5086_);
v___x_5089_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__5));
v___x_5090_ = lean_unsigned_to_nat(0u);
v___x_5091_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__6));
v___x_5092_ = lean_box(v___x_5086_);
lean_inc_ref(v_config_5067_);
v___f_5093_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__7___boxed), 17, 12);
lean_closure_set(v___f_5093_, 0, v_config_5067_);
lean_closure_set(v___f_5093_, 1, v___x_5091_);
lean_closure_set(v___f_5093_, 2, v_a_5080_);
lean_closure_set(v___f_5093_, 3, v___x_5090_);
lean_closure_set(v___f_5093_, 4, v___f_5081_);
lean_closure_set(v___f_5093_, 5, v___f_5087_);
lean_closure_set(v___f_5093_, 6, v___f_5084_);
lean_closure_set(v___f_5093_, 7, v___f_5082_);
lean_closure_set(v___f_5093_, 8, v___f_5085_);
lean_closure_set(v___f_5093_, 9, v___x_5092_);
lean_closure_set(v___f_5093_, 10, v_a_5078_);
lean_closure_set(v___f_5093_, 11, v___x_5088_);
v___x_5094_ = l_Lean_Elab_Tactic_NormCast_derive___lam__5(v___x_5076_, v___x_5086_, v___x_5089_, v___f_5093_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_);
if (lean_obj_tag(v___x_5094_) == 0)
{
lean_object* v_a_5095_; lean_object* v___x_5096_; lean_object* v_up_5097_; lean_object* v_squash_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___f_5101_; lean_object* v___x_5102_; 
v_a_5095_ = lean_ctor_get(v___x_5094_, 0);
lean_inc(v_a_5095_);
lean_dec_ref(v___x_5094_);
v___x_5096_ = l_Lean_Meta_NormCast_normCastExt;
v_up_5097_ = lean_ctor_get(v___x_5096_, 0);
v_squash_5098_ = lean_ctor_get(v___x_5096_, 2);
v___x_5099_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__7));
v___x_5100_ = lean_box(v___x_5086_);
lean_inc(v_a_5080_);
lean_inc_ref(v_config_5067_);
lean_inc_ref(v_up_5097_);
v___f_5101_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__12___boxed), 16, 11);
lean_closure_set(v___f_5101_, 0, v_up_5097_);
lean_closure_set(v___f_5101_, 1, v_config_5067_);
lean_closure_set(v___f_5101_, 2, v___x_5091_);
lean_closure_set(v___f_5101_, 3, v_a_5080_);
lean_closure_set(v___f_5101_, 4, v_a_5095_);
lean_closure_set(v___f_5101_, 5, v___x_5090_);
lean_closure_set(v___f_5101_, 6, v___f_5081_);
lean_closure_set(v___f_5101_, 7, v___f_5084_);
lean_closure_set(v___f_5101_, 8, v___f_5082_);
lean_closure_set(v___f_5101_, 9, v___f_5085_);
lean_closure_set(v___f_5101_, 10, v___x_5100_);
v___x_5102_ = l_Lean_Elab_Tactic_NormCast_derive___lam__5(v___x_5076_, v___x_5086_, v___x_5099_, v___f_5101_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_);
if (lean_obj_tag(v___x_5102_) == 0)
{
lean_object* v_a_5103_; lean_object* v___x_5104_; lean_object* v___x_5105_; 
v_a_5103_ = lean_ctor_get(v___x_5102_, 0);
lean_inc(v_a_5103_);
lean_dec_ref(v___x_5102_);
v___x_5104_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__9));
v___x_5105_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_5091_, v___x_5104_, v_hasTrace_5075_, v_a_5070_, v_a_5071_);
if (lean_obj_tag(v___x_5105_) == 0)
{
lean_object* v_a_5106_; lean_object* v___f_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; 
v_a_5106_ = lean_ctor_get(v___x_5105_, 0);
lean_inc(v_a_5106_);
lean_dec_ref(v___x_5105_);
lean_inc_ref(v_squash_5098_);
v___f_5107_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__8___boxed), 11, 6);
lean_closure_set(v___f_5107_, 0, v_squash_5098_);
lean_closure_set(v___f_5107_, 1, v_config_5067_);
lean_closure_set(v___f_5107_, 2, v_a_5080_);
lean_closure_set(v___f_5107_, 3, v_a_5103_);
lean_closure_set(v___f_5107_, 4, v___x_5090_);
lean_closure_set(v___f_5107_, 5, v_a_5106_);
v___x_5108_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__10));
v___x_5109_ = l_Lean_Elab_Tactic_NormCast_derive___lam__5(v___x_5076_, v___x_5086_, v___x_5108_, v___f_5107_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_);
return v___x_5109_;
}
else
{
lean_object* v_a_5110_; lean_object* v___x_5112_; uint8_t v_isShared_5113_; uint8_t v_isSharedCheck_5117_; 
lean_dec(v_a_5103_);
lean_dec(v_a_5080_);
lean_dec_ref(v_config_5067_);
v_a_5110_ = lean_ctor_get(v___x_5105_, 0);
v_isSharedCheck_5117_ = !lean_is_exclusive(v___x_5105_);
if (v_isSharedCheck_5117_ == 0)
{
v___x_5112_ = v___x_5105_;
v_isShared_5113_ = v_isSharedCheck_5117_;
goto v_resetjp_5111_;
}
else
{
lean_inc(v_a_5110_);
lean_dec(v___x_5105_);
v___x_5112_ = lean_box(0);
v_isShared_5113_ = v_isSharedCheck_5117_;
goto v_resetjp_5111_;
}
v_resetjp_5111_:
{
lean_object* v___x_5115_; 
if (v_isShared_5113_ == 0)
{
v___x_5115_ = v___x_5112_;
goto v_reusejp_5114_;
}
else
{
lean_object* v_reuseFailAlloc_5116_; 
v_reuseFailAlloc_5116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5116_, 0, v_a_5110_);
v___x_5115_ = v_reuseFailAlloc_5116_;
goto v_reusejp_5114_;
}
v_reusejp_5114_:
{
return v___x_5115_;
}
}
}
}
else
{
lean_dec(v_a_5080_);
lean_dec_ref(v_config_5067_);
return v___x_5102_;
}
}
else
{
lean_dec(v_a_5080_);
lean_dec_ref(v_config_5067_);
return v___x_5094_;
}
}
else
{
lean_object* v_a_5118_; lean_object* v___x_5120_; uint8_t v_isShared_5121_; uint8_t v_isSharedCheck_5125_; 
lean_dec(v_a_5078_);
lean_dec_ref(v_config_5067_);
v_a_5118_ = lean_ctor_get(v___x_5079_, 0);
v_isSharedCheck_5125_ = !lean_is_exclusive(v___x_5079_);
if (v_isSharedCheck_5125_ == 0)
{
v___x_5120_ = v___x_5079_;
v_isShared_5121_ = v_isSharedCheck_5125_;
goto v_resetjp_5119_;
}
else
{
lean_inc(v_a_5118_);
lean_dec(v___x_5079_);
v___x_5120_ = lean_box(0);
v_isShared_5121_ = v_isSharedCheck_5125_;
goto v_resetjp_5119_;
}
v_resetjp_5119_:
{
lean_object* v___x_5123_; 
if (v_isShared_5121_ == 0)
{
v___x_5123_ = v___x_5120_;
goto v_reusejp_5122_;
}
else
{
lean_object* v_reuseFailAlloc_5124_; 
v_reuseFailAlloc_5124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5124_, 0, v_a_5118_);
v___x_5123_ = v_reuseFailAlloc_5124_;
goto v_reusejp_5122_;
}
v_reusejp_5122_:
{
return v___x_5123_;
}
}
}
}
else
{
lean_object* v___f_5126_; lean_object* v___f_5127_; lean_object* v___f_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; uint8_t v___x_5131_; lean_object* v___y_5133_; lean_object* v___y_5134_; lean_object* v_a_5135_; lean_object* v___y_5145_; lean_object* v___y_5146_; lean_object* v_a_5147_; lean_object* v___y_5150_; lean_object* v___y_5151_; lean_object* v_a_5152_; lean_object* v___y_5165_; lean_object* v___y_5166_; lean_object* v_a_5167_; 
v___f_5126_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__1));
v___f_5127_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__0));
lean_inc_ref(v_e_5066_);
v___f_5128_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__18___boxed), 7, 1);
lean_closure_set(v___f_5128_, 0, v_e_5066_);
v___x_5129_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_5130_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3);
v___x_5131_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5074_, v_options_5073_, v___x_5130_);
if (v___x_5131_ == 0)
{
lean_object* v___x_5265_; uint8_t v___x_5266_; 
v___x_5265_ = l_Lean_trace_profiler;
v___x_5266_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_5073_, v___x_5265_);
if (v___x_5266_ == 0)
{
lean_object* v___x_5267_; lean_object* v_a_5268_; lean_object* v___x_5269_; 
lean_dec_ref(v___f_5128_);
v___x_5267_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_e_5066_, v_a_5069_);
v_a_5268_ = lean_ctor_get(v___x_5267_, 0);
lean_inc(v_a_5268_);
lean_dec_ref(v___x_5267_);
v___x_5269_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_5071_);
if (lean_obj_tag(v___x_5269_) == 0)
{
lean_object* v_a_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___f_5273_; lean_object* v___f_5274_; lean_object* v___f_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___f_5281_; lean_object* v___x_5282_; 
v_a_5270_ = lean_ctor_get(v___x_5269_, 0);
lean_inc_n(v_a_5270_, 2);
lean_dec_ref(v___x_5269_);
v___x_5271_ = lean_box(0);
v___x_5272_ = lean_box(v_hasTrace_5075_);
v___f_5273_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__9___boxed), 11, 2);
lean_closure_set(v___f_5273_, 0, v___x_5271_);
lean_closure_set(v___f_5273_, 1, v___x_5272_);
v___f_5274_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__2));
v___f_5275_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__3));
lean_inc(v_a_5268_);
v___x_5276_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5276_, 0, v_a_5268_);
lean_ctor_set(v___x_5276_, 1, v___x_5271_);
lean_ctor_set_uint8(v___x_5276_, sizeof(void*)*2, v_hasTrace_5075_);
v___x_5277_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__5));
v___x_5278_ = lean_unsigned_to_nat(0u);
v___x_5279_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__6));
v___x_5280_ = lean_box(v_hasTrace_5075_);
lean_inc_ref(v_config_5067_);
v___f_5281_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__14___boxed), 17, 12);
lean_closure_set(v___f_5281_, 0, v_config_5067_);
lean_closure_set(v___f_5281_, 1, v___x_5279_);
lean_closure_set(v___f_5281_, 2, v_a_5270_);
lean_closure_set(v___f_5281_, 3, v___x_5278_);
lean_closure_set(v___f_5281_, 4, v___f_5127_);
lean_closure_set(v___f_5281_, 5, v___f_5273_);
lean_closure_set(v___f_5281_, 6, v___f_5274_);
lean_closure_set(v___f_5281_, 7, v___f_5126_);
lean_closure_set(v___f_5281_, 8, v___f_5275_);
lean_closure_set(v___f_5281_, 9, v___x_5280_);
lean_closure_set(v___f_5281_, 10, v_a_5268_);
lean_closure_set(v___f_5281_, 11, v___x_5276_);
v___x_5282_ = l_Lean_Elab_Tactic_NormCast_derive___lam__27(v___x_5076_, v_hasTrace_5075_, v___x_5277_, v___f_5281_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_);
if (lean_obj_tag(v___x_5282_) == 0)
{
lean_object* v_a_5283_; lean_object* v___x_5284_; lean_object* v_up_5285_; lean_object* v_squash_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___f_5289_; lean_object* v___x_5290_; 
v_a_5283_ = lean_ctor_get(v___x_5282_, 0);
lean_inc(v_a_5283_);
lean_dec_ref(v___x_5282_);
v___x_5284_ = l_Lean_Meta_NormCast_normCastExt;
v_up_5285_ = lean_ctor_get(v___x_5284_, 0);
v_squash_5286_ = lean_ctor_get(v___x_5284_, 2);
v___x_5287_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__7));
v___x_5288_ = lean_box(v_hasTrace_5075_);
lean_inc(v_a_5270_);
lean_inc_ref(v_config_5067_);
lean_inc_ref(v_up_5285_);
v___f_5289_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__15___boxed), 16, 11);
lean_closure_set(v___f_5289_, 0, v_up_5285_);
lean_closure_set(v___f_5289_, 1, v_config_5067_);
lean_closure_set(v___f_5289_, 2, v___x_5279_);
lean_closure_set(v___f_5289_, 3, v_a_5270_);
lean_closure_set(v___f_5289_, 4, v_a_5283_);
lean_closure_set(v___f_5289_, 5, v___x_5278_);
lean_closure_set(v___f_5289_, 6, v___f_5127_);
lean_closure_set(v___f_5289_, 7, v___f_5274_);
lean_closure_set(v___f_5289_, 8, v___f_5126_);
lean_closure_set(v___f_5289_, 9, v___f_5275_);
lean_closure_set(v___f_5289_, 10, v___x_5288_);
v___x_5290_ = l_Lean_Elab_Tactic_NormCast_derive___lam__27(v___x_5076_, v_hasTrace_5075_, v___x_5287_, v___f_5289_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_);
if (lean_obj_tag(v___x_5290_) == 0)
{
lean_object* v_a_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; 
v_a_5291_ = lean_ctor_get(v___x_5290_, 0);
lean_inc(v_a_5291_);
lean_dec_ref(v___x_5290_);
v___x_5292_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__9));
v___x_5293_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_5279_, v___x_5292_, v___x_5266_, v_a_5070_, v_a_5071_);
if (lean_obj_tag(v___x_5293_) == 0)
{
lean_object* v_a_5294_; lean_object* v___f_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; 
v_a_5294_ = lean_ctor_get(v___x_5293_, 0);
lean_inc(v_a_5294_);
lean_dec_ref(v___x_5293_);
lean_inc_ref(v_squash_5286_);
v___f_5295_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__8___boxed), 11, 6);
lean_closure_set(v___f_5295_, 0, v_squash_5286_);
lean_closure_set(v___f_5295_, 1, v_config_5067_);
lean_closure_set(v___f_5295_, 2, v_a_5270_);
lean_closure_set(v___f_5295_, 3, v_a_5291_);
lean_closure_set(v___f_5295_, 4, v___x_5278_);
lean_closure_set(v___f_5295_, 5, v_a_5294_);
v___x_5296_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__10));
v___x_5297_ = l_Lean_Elab_Tactic_NormCast_derive___lam__27(v___x_5076_, v_hasTrace_5075_, v___x_5296_, v___f_5295_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_);
return v___x_5297_;
}
else
{
lean_object* v_a_5298_; lean_object* v___x_5300_; uint8_t v_isShared_5301_; uint8_t v_isSharedCheck_5305_; 
lean_dec(v_a_5291_);
lean_dec(v_a_5270_);
lean_dec_ref(v_config_5067_);
v_a_5298_ = lean_ctor_get(v___x_5293_, 0);
v_isSharedCheck_5305_ = !lean_is_exclusive(v___x_5293_);
if (v_isSharedCheck_5305_ == 0)
{
v___x_5300_ = v___x_5293_;
v_isShared_5301_ = v_isSharedCheck_5305_;
goto v_resetjp_5299_;
}
else
{
lean_inc(v_a_5298_);
lean_dec(v___x_5293_);
v___x_5300_ = lean_box(0);
v_isShared_5301_ = v_isSharedCheck_5305_;
goto v_resetjp_5299_;
}
v_resetjp_5299_:
{
lean_object* v___x_5303_; 
if (v_isShared_5301_ == 0)
{
v___x_5303_ = v___x_5300_;
goto v_reusejp_5302_;
}
else
{
lean_object* v_reuseFailAlloc_5304_; 
v_reuseFailAlloc_5304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5304_, 0, v_a_5298_);
v___x_5303_ = v_reuseFailAlloc_5304_;
goto v_reusejp_5302_;
}
v_reusejp_5302_:
{
return v___x_5303_;
}
}
}
}
else
{
lean_dec(v_a_5270_);
lean_dec_ref(v_config_5067_);
return v___x_5290_;
}
}
else
{
lean_dec(v_a_5270_);
lean_dec_ref(v_config_5067_);
return v___x_5282_;
}
}
else
{
lean_object* v_a_5306_; lean_object* v___x_5308_; uint8_t v_isShared_5309_; uint8_t v_isSharedCheck_5313_; 
lean_dec(v_a_5268_);
lean_dec_ref(v_config_5067_);
v_a_5306_ = lean_ctor_get(v___x_5269_, 0);
v_isSharedCheck_5313_ = !lean_is_exclusive(v___x_5269_);
if (v_isSharedCheck_5313_ == 0)
{
v___x_5308_ = v___x_5269_;
v_isShared_5309_ = v_isSharedCheck_5313_;
goto v_resetjp_5307_;
}
else
{
lean_inc(v_a_5306_);
lean_dec(v___x_5269_);
v___x_5308_ = lean_box(0);
v_isShared_5309_ = v_isSharedCheck_5313_;
goto v_resetjp_5307_;
}
v_resetjp_5307_:
{
lean_object* v___x_5311_; 
if (v_isShared_5309_ == 0)
{
v___x_5311_ = v___x_5308_;
goto v_reusejp_5310_;
}
else
{
lean_object* v_reuseFailAlloc_5312_; 
v_reuseFailAlloc_5312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5312_, 0, v_a_5306_);
v___x_5311_ = v_reuseFailAlloc_5312_;
goto v_reusejp_5310_;
}
v_reusejp_5310_:
{
return v___x_5311_;
}
}
}
}
else
{
goto v___jp_5169_;
}
}
else
{
goto v___jp_5169_;
}
v___jp_5132_:
{
lean_object* v___x_5136_; double v___x_5137_; double v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; 
v___x_5136_ = lean_io_get_num_heartbeats();
v___x_5137_ = lean_float_of_nat(v___y_5134_);
v___x_5138_ = lean_float_of_nat(v___x_5136_);
v___x_5139_ = lean_box_float(v___x_5137_);
v___x_5140_ = lean_box_float(v___x_5138_);
v___x_5141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5141_, 0, v___x_5139_);
lean_ctor_set(v___x_5141_, 1, v___x_5140_);
v___x_5142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5142_, 0, v_a_5135_);
lean_ctor_set(v___x_5142_, 1, v___x_5141_);
v___x_5143_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_5076_, v_hasTrace_5075_, v___x_5129_, v_options_5073_, v___x_5131_, v___y_5133_, v___f_5128_, v___x_5142_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_);
return v___x_5143_;
}
v___jp_5144_:
{
lean_object* v___x_5148_; 
v___x_5148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5148_, 0, v_a_5147_);
v___y_5133_ = v___y_5145_;
v___y_5134_ = v___y_5146_;
v_a_5135_ = v___x_5148_;
goto v___jp_5132_;
}
v___jp_5149_:
{
lean_object* v___x_5153_; double v___x_5154_; double v___x_5155_; double v___x_5156_; double v___x_5157_; double v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; 
v___x_5153_ = lean_io_mono_nanos_now();
v___x_5154_ = lean_float_of_nat(v___y_5150_);
v___x_5155_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4);
v___x_5156_ = lean_float_div(v___x_5154_, v___x_5155_);
v___x_5157_ = lean_float_of_nat(v___x_5153_);
v___x_5158_ = lean_float_div(v___x_5157_, v___x_5155_);
v___x_5159_ = lean_box_float(v___x_5156_);
v___x_5160_ = lean_box_float(v___x_5158_);
v___x_5161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5161_, 0, v___x_5159_);
lean_ctor_set(v___x_5161_, 1, v___x_5160_);
v___x_5162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5162_, 0, v_a_5152_);
lean_ctor_set(v___x_5162_, 1, v___x_5161_);
v___x_5163_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_5076_, v_hasTrace_5075_, v___x_5129_, v_options_5073_, v___x_5131_, v___y_5151_, v___f_5128_, v___x_5162_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_);
return v___x_5163_;
}
v___jp_5164_:
{
lean_object* v___x_5168_; 
v___x_5168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5168_, 0, v_a_5167_);
v___y_5150_ = v___y_5165_;
v___y_5151_ = v___y_5166_;
v_a_5152_ = v___x_5168_;
goto v___jp_5149_;
}
v___jp_5169_:
{
lean_object* v___x_5170_; lean_object* v_a_5171_; lean_object* v___x_5172_; uint8_t v___x_5173_; 
v___x_5170_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v_a_5071_);
v_a_5171_ = lean_ctor_get(v___x_5170_, 0);
lean_inc(v_a_5171_);
lean_dec_ref(v___x_5170_);
v___x_5172_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5173_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_5073_, v___x_5172_);
if (v___x_5173_ == 0)
{
lean_object* v___x_5174_; lean_object* v___x_5175_; lean_object* v_a_5176_; lean_object* v___x_5177_; 
v___x_5174_ = lean_io_mono_nanos_now();
v___x_5175_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_e_5066_, v_a_5069_);
v_a_5176_ = lean_ctor_get(v___x_5175_, 0);
lean_inc(v_a_5176_);
lean_dec_ref(v___x_5175_);
v___x_5177_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_5071_);
if (lean_obj_tag(v___x_5177_) == 0)
{
lean_object* v_a_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; lean_object* v___f_5181_; lean_object* v___f_5182_; lean_object* v___f_5183_; lean_object* v___x_5184_; lean_object* v___x_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___f_5189_; lean_object* v___x_5190_; 
v_a_5178_ = lean_ctor_get(v___x_5177_, 0);
lean_inc_n(v_a_5178_, 2);
lean_dec_ref(v___x_5177_);
v___x_5179_ = lean_box(0);
v___x_5180_ = lean_box(v_hasTrace_5075_);
v___f_5181_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__9___boxed), 11, 2);
lean_closure_set(v___f_5181_, 0, v___x_5179_);
lean_closure_set(v___f_5181_, 1, v___x_5180_);
v___f_5182_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__2));
v___f_5183_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__3));
lean_inc(v_a_5176_);
v___x_5184_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5184_, 0, v_a_5176_);
lean_ctor_set(v___x_5184_, 1, v___x_5179_);
lean_ctor_set_uint8(v___x_5184_, sizeof(void*)*2, v_hasTrace_5075_);
v___x_5185_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__5));
v___x_5186_ = lean_unsigned_to_nat(0u);
v___x_5187_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__6));
v___x_5188_ = lean_box(v_hasTrace_5075_);
lean_inc_ref(v_config_5067_);
v___f_5189_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__14___boxed), 17, 12);
lean_closure_set(v___f_5189_, 0, v_config_5067_);
lean_closure_set(v___f_5189_, 1, v___x_5187_);
lean_closure_set(v___f_5189_, 2, v_a_5178_);
lean_closure_set(v___f_5189_, 3, v___x_5186_);
lean_closure_set(v___f_5189_, 4, v___f_5127_);
lean_closure_set(v___f_5189_, 5, v___f_5181_);
lean_closure_set(v___f_5189_, 6, v___f_5182_);
lean_closure_set(v___f_5189_, 7, v___f_5126_);
lean_closure_set(v___f_5189_, 8, v___f_5183_);
lean_closure_set(v___f_5189_, 9, v___x_5188_);
lean_closure_set(v___f_5189_, 10, v_a_5176_);
lean_closure_set(v___f_5189_, 11, v___x_5184_);
v___x_5190_ = l_Lean_Elab_Tactic_NormCast_derive___lam__10(v___x_5076_, v_hasTrace_5075_, v___x_5185_, v___f_5189_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_);
if (lean_obj_tag(v___x_5190_) == 0)
{
lean_object* v_a_5191_; lean_object* v___x_5192_; lean_object* v_up_5193_; lean_object* v_squash_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___f_5197_; lean_object* v___x_5198_; 
v_a_5191_ = lean_ctor_get(v___x_5190_, 0);
lean_inc(v_a_5191_);
lean_dec_ref(v___x_5190_);
v___x_5192_ = l_Lean_Meta_NormCast_normCastExt;
v_up_5193_ = lean_ctor_get(v___x_5192_, 0);
v_squash_5194_ = lean_ctor_get(v___x_5192_, 2);
v___x_5195_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__7));
v___x_5196_ = lean_box(v_hasTrace_5075_);
lean_inc(v_a_5178_);
lean_inc_ref(v_config_5067_);
lean_inc_ref(v_up_5193_);
v___f_5197_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__15___boxed), 16, 11);
lean_closure_set(v___f_5197_, 0, v_up_5193_);
lean_closure_set(v___f_5197_, 1, v_config_5067_);
lean_closure_set(v___f_5197_, 2, v___x_5187_);
lean_closure_set(v___f_5197_, 3, v_a_5178_);
lean_closure_set(v___f_5197_, 4, v_a_5191_);
lean_closure_set(v___f_5197_, 5, v___x_5186_);
lean_closure_set(v___f_5197_, 6, v___f_5127_);
lean_closure_set(v___f_5197_, 7, v___f_5182_);
lean_closure_set(v___f_5197_, 8, v___f_5126_);
lean_closure_set(v___f_5197_, 9, v___f_5183_);
lean_closure_set(v___f_5197_, 10, v___x_5196_);
v___x_5198_ = l_Lean_Elab_Tactic_NormCast_derive___lam__10(v___x_5076_, v_hasTrace_5075_, v___x_5195_, v___f_5197_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_);
if (lean_obj_tag(v___x_5198_) == 0)
{
lean_object* v_a_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; 
v_a_5199_ = lean_ctor_get(v___x_5198_, 0);
lean_inc(v_a_5199_);
lean_dec_ref(v___x_5198_);
v___x_5200_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__9));
v___x_5201_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_5187_, v___x_5200_, v___x_5173_, v_a_5070_, v_a_5071_);
if (lean_obj_tag(v___x_5201_) == 0)
{
lean_object* v_a_5202_; lean_object* v___f_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; 
v_a_5202_ = lean_ctor_get(v___x_5201_, 0);
lean_inc(v_a_5202_);
lean_dec_ref(v___x_5201_);
lean_inc_ref(v_squash_5194_);
v___f_5203_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__8___boxed), 11, 6);
lean_closure_set(v___f_5203_, 0, v_squash_5194_);
lean_closure_set(v___f_5203_, 1, v_config_5067_);
lean_closure_set(v___f_5203_, 2, v_a_5178_);
lean_closure_set(v___f_5203_, 3, v_a_5199_);
lean_closure_set(v___f_5203_, 4, v___x_5186_);
lean_closure_set(v___f_5203_, 5, v_a_5202_);
v___x_5204_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__10));
v___x_5205_ = l_Lean_Elab_Tactic_NormCast_derive___lam__10(v___x_5076_, v_hasTrace_5075_, v___x_5204_, v___f_5203_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_);
if (lean_obj_tag(v___x_5205_) == 0)
{
lean_object* v_a_5206_; lean_object* v___x_5208_; uint8_t v_isShared_5209_; uint8_t v_isSharedCheck_5213_; 
v_a_5206_ = lean_ctor_get(v___x_5205_, 0);
v_isSharedCheck_5213_ = !lean_is_exclusive(v___x_5205_);
if (v_isSharedCheck_5213_ == 0)
{
v___x_5208_ = v___x_5205_;
v_isShared_5209_ = v_isSharedCheck_5213_;
goto v_resetjp_5207_;
}
else
{
lean_inc(v_a_5206_);
lean_dec(v___x_5205_);
v___x_5208_ = lean_box(0);
v_isShared_5209_ = v_isSharedCheck_5213_;
goto v_resetjp_5207_;
}
v_resetjp_5207_:
{
lean_object* v___x_5211_; 
if (v_isShared_5209_ == 0)
{
lean_ctor_set_tag(v___x_5208_, 1);
v___x_5211_ = v___x_5208_;
goto v_reusejp_5210_;
}
else
{
lean_object* v_reuseFailAlloc_5212_; 
v_reuseFailAlloc_5212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5212_, 0, v_a_5206_);
v___x_5211_ = v_reuseFailAlloc_5212_;
goto v_reusejp_5210_;
}
v_reusejp_5210_:
{
v___y_5150_ = v___x_5174_;
v___y_5151_ = v_a_5171_;
v_a_5152_ = v___x_5211_;
goto v___jp_5149_;
}
}
}
else
{
lean_object* v_a_5214_; 
v_a_5214_ = lean_ctor_get(v___x_5205_, 0);
lean_inc(v_a_5214_);
lean_dec_ref(v___x_5205_);
v___y_5165_ = v___x_5174_;
v___y_5166_ = v_a_5171_;
v_a_5167_ = v_a_5214_;
goto v___jp_5164_;
}
}
else
{
lean_object* v_a_5215_; 
lean_dec(v_a_5199_);
lean_dec(v_a_5178_);
lean_dec_ref(v_config_5067_);
v_a_5215_ = lean_ctor_get(v___x_5201_, 0);
lean_inc(v_a_5215_);
lean_dec_ref(v___x_5201_);
v___y_5165_ = v___x_5174_;
v___y_5166_ = v_a_5171_;
v_a_5167_ = v_a_5215_;
goto v___jp_5164_;
}
}
else
{
lean_object* v_a_5216_; 
lean_dec(v_a_5178_);
lean_dec_ref(v_config_5067_);
v_a_5216_ = lean_ctor_get(v___x_5198_, 0);
lean_inc(v_a_5216_);
lean_dec_ref(v___x_5198_);
v___y_5165_ = v___x_5174_;
v___y_5166_ = v_a_5171_;
v_a_5167_ = v_a_5216_;
goto v___jp_5164_;
}
}
else
{
lean_object* v_a_5217_; 
lean_dec(v_a_5178_);
lean_dec_ref(v_config_5067_);
v_a_5217_ = lean_ctor_get(v___x_5190_, 0);
lean_inc(v_a_5217_);
lean_dec_ref(v___x_5190_);
v___y_5165_ = v___x_5174_;
v___y_5166_ = v_a_5171_;
v_a_5167_ = v_a_5217_;
goto v___jp_5164_;
}
}
else
{
lean_object* v_a_5218_; 
lean_dec(v_a_5176_);
lean_dec_ref(v_config_5067_);
v_a_5218_ = lean_ctor_get(v___x_5177_, 0);
lean_inc(v_a_5218_);
lean_dec_ref(v___x_5177_);
v___y_5165_ = v___x_5174_;
v___y_5166_ = v_a_5171_;
v_a_5167_ = v_a_5218_;
goto v___jp_5164_;
}
}
else
{
lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v_a_5221_; lean_object* v___x_5222_; 
v___x_5219_ = lean_io_get_num_heartbeats();
v___x_5220_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_e_5066_, v_a_5069_);
v_a_5221_ = lean_ctor_get(v___x_5220_, 0);
lean_inc(v_a_5221_);
lean_dec_ref(v___x_5220_);
v___x_5222_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_5071_);
if (lean_obj_tag(v___x_5222_) == 0)
{
lean_object* v_a_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___f_5226_; lean_object* v___f_5227_; lean_object* v___f_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___f_5234_; lean_object* v___x_5235_; 
v_a_5223_ = lean_ctor_get(v___x_5222_, 0);
lean_inc_n(v_a_5223_, 2);
lean_dec_ref(v___x_5222_);
v___x_5224_ = lean_box(0);
v___x_5225_ = lean_box(v___x_5173_);
v___f_5226_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__6___boxed), 11, 2);
lean_closure_set(v___f_5226_, 0, v___x_5224_);
lean_closure_set(v___f_5226_, 1, v___x_5225_);
v___f_5227_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__2));
v___f_5228_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__3));
lean_inc(v_a_5221_);
v___x_5229_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5229_, 0, v_a_5221_);
lean_ctor_set(v___x_5229_, 1, v___x_5224_);
lean_ctor_set_uint8(v___x_5229_, sizeof(void*)*2, v___x_5173_);
v___x_5230_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__5));
v___x_5231_ = lean_unsigned_to_nat(0u);
v___x_5232_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__6));
v___x_5233_ = lean_box(v___x_5173_);
lean_inc_ref(v_config_5067_);
v___f_5234_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__7___boxed), 17, 12);
lean_closure_set(v___f_5234_, 0, v_config_5067_);
lean_closure_set(v___f_5234_, 1, v___x_5232_);
lean_closure_set(v___f_5234_, 2, v_a_5223_);
lean_closure_set(v___f_5234_, 3, v___x_5231_);
lean_closure_set(v___f_5234_, 4, v___f_5127_);
lean_closure_set(v___f_5234_, 5, v___f_5226_);
lean_closure_set(v___f_5234_, 6, v___f_5227_);
lean_closure_set(v___f_5234_, 7, v___f_5126_);
lean_closure_set(v___f_5234_, 8, v___f_5228_);
lean_closure_set(v___f_5234_, 9, v___x_5233_);
lean_closure_set(v___f_5234_, 10, v_a_5221_);
lean_closure_set(v___f_5234_, 11, v___x_5229_);
v___x_5235_ = l_Lean_Elab_Tactic_NormCast_derive___lam__16(v___x_5076_, v___x_5173_, v___x_5129_, v___x_5172_, v___x_5230_, v___f_5234_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_);
if (lean_obj_tag(v___x_5235_) == 0)
{
lean_object* v_a_5236_; lean_object* v___x_5237_; lean_object* v_up_5238_; lean_object* v_squash_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___f_5242_; lean_object* v___x_5243_; 
v_a_5236_ = lean_ctor_get(v___x_5235_, 0);
lean_inc(v_a_5236_);
lean_dec_ref(v___x_5235_);
v___x_5237_ = l_Lean_Meta_NormCast_normCastExt;
v_up_5238_ = lean_ctor_get(v___x_5237_, 0);
v_squash_5239_ = lean_ctor_get(v___x_5237_, 2);
v___x_5240_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__7));
v___x_5241_ = lean_box(v___x_5173_);
lean_inc(v_a_5223_);
lean_inc_ref(v_config_5067_);
lean_inc_ref(v_up_5238_);
v___f_5242_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__12___boxed), 16, 11);
lean_closure_set(v___f_5242_, 0, v_up_5238_);
lean_closure_set(v___f_5242_, 1, v_config_5067_);
lean_closure_set(v___f_5242_, 2, v___x_5232_);
lean_closure_set(v___f_5242_, 3, v_a_5223_);
lean_closure_set(v___f_5242_, 4, v_a_5236_);
lean_closure_set(v___f_5242_, 5, v___x_5231_);
lean_closure_set(v___f_5242_, 6, v___f_5127_);
lean_closure_set(v___f_5242_, 7, v___f_5227_);
lean_closure_set(v___f_5242_, 8, v___f_5126_);
lean_closure_set(v___f_5242_, 9, v___f_5228_);
lean_closure_set(v___f_5242_, 10, v___x_5241_);
v___x_5243_ = l_Lean_Elab_Tactic_NormCast_derive___lam__16(v___x_5076_, v___x_5173_, v___x_5129_, v___x_5172_, v___x_5240_, v___f_5242_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_);
if (lean_obj_tag(v___x_5243_) == 0)
{
lean_object* v_a_5244_; lean_object* v___x_5245_; uint8_t v___x_5246_; lean_object* v___x_5247_; 
v_a_5244_ = lean_ctor_get(v___x_5243_, 0);
lean_inc(v_a_5244_);
lean_dec_ref(v___x_5243_);
v___x_5245_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__9));
v___x_5246_ = 0;
v___x_5247_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_5232_, v___x_5245_, v___x_5246_, v_a_5070_, v_a_5071_);
if (lean_obj_tag(v___x_5247_) == 0)
{
lean_object* v_a_5248_; lean_object* v___f_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; 
v_a_5248_ = lean_ctor_get(v___x_5247_, 0);
lean_inc(v_a_5248_);
lean_dec_ref(v___x_5247_);
lean_inc_ref(v_squash_5239_);
v___f_5249_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__8___boxed), 11, 6);
lean_closure_set(v___f_5249_, 0, v_squash_5239_);
lean_closure_set(v___f_5249_, 1, v_config_5067_);
lean_closure_set(v___f_5249_, 2, v_a_5223_);
lean_closure_set(v___f_5249_, 3, v_a_5244_);
lean_closure_set(v___f_5249_, 4, v___x_5231_);
lean_closure_set(v___f_5249_, 5, v_a_5248_);
v___x_5250_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__10));
v___x_5251_ = l_Lean_Elab_Tactic_NormCast_derive___lam__16(v___x_5076_, v___x_5173_, v___x_5129_, v___x_5172_, v___x_5250_, v___f_5249_, v_a_5068_, v_a_5069_, v_a_5070_, v_a_5071_);
if (lean_obj_tag(v___x_5251_) == 0)
{
lean_object* v_a_5252_; lean_object* v___x_5254_; uint8_t v_isShared_5255_; uint8_t v_isSharedCheck_5259_; 
v_a_5252_ = lean_ctor_get(v___x_5251_, 0);
v_isSharedCheck_5259_ = !lean_is_exclusive(v___x_5251_);
if (v_isSharedCheck_5259_ == 0)
{
v___x_5254_ = v___x_5251_;
v_isShared_5255_ = v_isSharedCheck_5259_;
goto v_resetjp_5253_;
}
else
{
lean_inc(v_a_5252_);
lean_dec(v___x_5251_);
v___x_5254_ = lean_box(0);
v_isShared_5255_ = v_isSharedCheck_5259_;
goto v_resetjp_5253_;
}
v_resetjp_5253_:
{
lean_object* v___x_5257_; 
if (v_isShared_5255_ == 0)
{
lean_ctor_set_tag(v___x_5254_, 1);
v___x_5257_ = v___x_5254_;
goto v_reusejp_5256_;
}
else
{
lean_object* v_reuseFailAlloc_5258_; 
v_reuseFailAlloc_5258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5258_, 0, v_a_5252_);
v___x_5257_ = v_reuseFailAlloc_5258_;
goto v_reusejp_5256_;
}
v_reusejp_5256_:
{
v___y_5133_ = v_a_5171_;
v___y_5134_ = v___x_5219_;
v_a_5135_ = v___x_5257_;
goto v___jp_5132_;
}
}
}
else
{
lean_object* v_a_5260_; 
v_a_5260_ = lean_ctor_get(v___x_5251_, 0);
lean_inc(v_a_5260_);
lean_dec_ref(v___x_5251_);
v___y_5145_ = v_a_5171_;
v___y_5146_ = v___x_5219_;
v_a_5147_ = v_a_5260_;
goto v___jp_5144_;
}
}
else
{
lean_object* v_a_5261_; 
lean_dec(v_a_5244_);
lean_dec(v_a_5223_);
lean_dec_ref(v_config_5067_);
v_a_5261_ = lean_ctor_get(v___x_5247_, 0);
lean_inc(v_a_5261_);
lean_dec_ref(v___x_5247_);
v___y_5145_ = v_a_5171_;
v___y_5146_ = v___x_5219_;
v_a_5147_ = v_a_5261_;
goto v___jp_5144_;
}
}
else
{
lean_object* v_a_5262_; 
lean_dec(v_a_5223_);
lean_dec_ref(v_config_5067_);
v_a_5262_ = lean_ctor_get(v___x_5243_, 0);
lean_inc(v_a_5262_);
lean_dec_ref(v___x_5243_);
v___y_5145_ = v_a_5171_;
v___y_5146_ = v___x_5219_;
v_a_5147_ = v_a_5262_;
goto v___jp_5144_;
}
}
else
{
lean_object* v_a_5263_; 
lean_dec(v_a_5223_);
lean_dec_ref(v_config_5067_);
v_a_5263_ = lean_ctor_get(v___x_5235_, 0);
lean_inc(v_a_5263_);
lean_dec_ref(v___x_5235_);
v___y_5145_ = v_a_5171_;
v___y_5146_ = v___x_5219_;
v_a_5147_ = v_a_5263_;
goto v___jp_5144_;
}
}
else
{
lean_object* v_a_5264_; 
lean_dec(v_a_5221_);
lean_dec_ref(v_config_5067_);
v_a_5264_ = lean_ctor_get(v___x_5222_, 0);
lean_inc(v_a_5264_);
lean_dec_ref(v___x_5222_);
v___y_5145_ = v_a_5171_;
v___y_5146_ = v___x_5219_;
v_a_5147_ = v_a_5264_;
goto v___jp_5144_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___boxed(lean_object* v_e_5314_, lean_object* v_config_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_, lean_object* v_a_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_){
_start:
{
lean_object* v_res_5321_; 
v_res_5321_ = l_Lean_Elab_Tactic_NormCast_derive(v_e_5314_, v_config_5315_, v_a_5316_, v_a_5317_, v_a_5318_, v_a_5319_);
lean_dec(v_a_5319_);
lean_dec_ref(v_a_5318_);
lean_dec(v_a_5317_);
lean_dec_ref(v_a_5316_);
return v_res_5321_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; 
v___x_5322_ = lean_box(0);
v___x_5323_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_5324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5324_, 0, v___x_5323_);
lean_ctor_set(v___x_5324_, 1, v___x_5322_);
return v___x_5324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg(){
_start:
{
lean_object* v___x_5326_; lean_object* v___x_5327_; 
v___x_5326_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0);
v___x_5327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5327_, 0, v___x_5326_);
return v___x_5327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___boxed(lean_object* v___y_5328_){
_start:
{
lean_object* v_res_5329_; 
v_res_5329_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg();
return v_res_5329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0(lean_object* v_00_u03b1_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_){
_start:
{
lean_object* v___x_5338_; 
v___x_5338_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg();
return v___x_5338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___boxed(lean_object* v_00_u03b1_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_){
_start:
{
lean_object* v_res_5347_; 
v_res_5347_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0(v_00_u03b1_5339_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_, v___y_5344_, v___y_5345_);
lean_dec(v___y_5345_);
lean_dec_ref(v___y_5344_);
lean_dec(v___y_5343_);
lean_dec_ref(v___y_5342_);
lean_dec(v___y_5341_);
lean_dec_ref(v___y_5340_);
return v_res_5347_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg(lean_object* v_e_5348_, lean_object* v___y_5349_){
_start:
{
uint8_t v___x_5351_; 
v___x_5351_ = l_Lean_Expr_hasMVar(v_e_5348_);
if (v___x_5351_ == 0)
{
lean_object* v___x_5352_; 
v___x_5352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5352_, 0, v_e_5348_);
return v___x_5352_;
}
else
{
lean_object* v___x_5353_; lean_object* v_mctx_5354_; lean_object* v___x_5355_; lean_object* v_fst_5356_; lean_object* v_snd_5357_; lean_object* v___x_5358_; lean_object* v_cache_5359_; lean_object* v_zetaDeltaFVarIds_5360_; lean_object* v_postponed_5361_; lean_object* v_diag_5362_; lean_object* v___x_5364_; uint8_t v_isShared_5365_; uint8_t v_isSharedCheck_5371_; 
v___x_5353_ = lean_st_ref_get(v___y_5349_);
v_mctx_5354_ = lean_ctor_get(v___x_5353_, 0);
lean_inc_ref(v_mctx_5354_);
lean_dec(v___x_5353_);
v___x_5355_ = l_Lean_instantiateMVarsCore(v_mctx_5354_, v_e_5348_);
v_fst_5356_ = lean_ctor_get(v___x_5355_, 0);
lean_inc(v_fst_5356_);
v_snd_5357_ = lean_ctor_get(v___x_5355_, 1);
lean_inc(v_snd_5357_);
lean_dec_ref(v___x_5355_);
v___x_5358_ = lean_st_ref_take(v___y_5349_);
v_cache_5359_ = lean_ctor_get(v___x_5358_, 1);
v_zetaDeltaFVarIds_5360_ = lean_ctor_get(v___x_5358_, 2);
v_postponed_5361_ = lean_ctor_get(v___x_5358_, 3);
v_diag_5362_ = lean_ctor_get(v___x_5358_, 4);
v_isSharedCheck_5371_ = !lean_is_exclusive(v___x_5358_);
if (v_isSharedCheck_5371_ == 0)
{
lean_object* v_unused_5372_; 
v_unused_5372_ = lean_ctor_get(v___x_5358_, 0);
lean_dec(v_unused_5372_);
v___x_5364_ = v___x_5358_;
v_isShared_5365_ = v_isSharedCheck_5371_;
goto v_resetjp_5363_;
}
else
{
lean_inc(v_diag_5362_);
lean_inc(v_postponed_5361_);
lean_inc(v_zetaDeltaFVarIds_5360_);
lean_inc(v_cache_5359_);
lean_dec(v___x_5358_);
v___x_5364_ = lean_box(0);
v_isShared_5365_ = v_isSharedCheck_5371_;
goto v_resetjp_5363_;
}
v_resetjp_5363_:
{
lean_object* v___x_5367_; 
if (v_isShared_5365_ == 0)
{
lean_ctor_set(v___x_5364_, 0, v_snd_5357_);
v___x_5367_ = v___x_5364_;
goto v_reusejp_5366_;
}
else
{
lean_object* v_reuseFailAlloc_5370_; 
v_reuseFailAlloc_5370_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5370_, 0, v_snd_5357_);
lean_ctor_set(v_reuseFailAlloc_5370_, 1, v_cache_5359_);
lean_ctor_set(v_reuseFailAlloc_5370_, 2, v_zetaDeltaFVarIds_5360_);
lean_ctor_set(v_reuseFailAlloc_5370_, 3, v_postponed_5361_);
lean_ctor_set(v_reuseFailAlloc_5370_, 4, v_diag_5362_);
v___x_5367_ = v_reuseFailAlloc_5370_;
goto v_reusejp_5366_;
}
v_reusejp_5366_:
{
lean_object* v___x_5368_; lean_object* v___x_5369_; 
v___x_5368_ = lean_st_ref_set(v___y_5349_, v___x_5367_);
v___x_5369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5369_, 0, v_fst_5356_);
return v___x_5369_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg___boxed(lean_object* v_e_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_){
_start:
{
lean_object* v_res_5376_; 
v_res_5376_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg(v_e_5373_, v___y_5374_);
lean_dec(v___y_5374_);
return v_res_5376_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1(lean_object* v_e_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_){
_start:
{
lean_object* v___x_5385_; 
v___x_5385_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg(v_e_5377_, v___y_5381_);
return v___x_5385_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___boxed(lean_object* v_e_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_){
_start:
{
lean_object* v_res_5394_; 
v_res_5394_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1(v_e_5386_, v___y_5387_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_, v___y_5392_);
lean_dec(v___y_5392_);
lean_dec_ref(v___y_5391_);
lean_dec(v___y_5390_);
lean_dec_ref(v___y_5389_);
lean_dec(v___y_5388_);
lean_dec_ref(v___y_5387_);
return v_res_5394_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__2(void){
_start:
{
lean_object* v___x_5398_; lean_object* v___x_5399_; 
v___x_5398_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__1));
v___x_5399_ = l_Lean_MessageData_ofFormat(v___x_5398_);
return v___x_5399_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5400_; lean_object* v___x_5401_; 
v___x_5400_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__2, &l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__2);
v___x_5401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5401_, 0, v___x_5400_);
return v___x_5401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0(uint8_t v___x_5402_, lean_object* v___x_5403_, lean_object* v_expectedType_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_){
_start:
{
lean_object* v___y_5413_; lean_object* v___y_5414_; lean_object* v___y_5415_; lean_object* v___y_5416_; lean_object* v___y_5417_; lean_object* v___y_5418_; lean_object* v___y_5419_; lean_object* v___y_5442_; lean_object* v___y_5443_; lean_object* v___y_5444_; lean_object* v___y_5445_; lean_object* v___y_5446_; lean_object* v___y_5447_; lean_object* v___y_5448_; lean_object* v___y_5449_; lean_object* v___y_5450_; lean_object* v___y_5485_; lean_object* v___y_5486_; lean_object* v___y_5487_; lean_object* v___y_5488_; lean_object* v___y_5489_; lean_object* v___y_5490_; lean_object* v___x_5535_; lean_object* v_a_5536_; uint8_t v___x_5537_; 
lean_inc_ref(v_expectedType_5404_);
v___x_5535_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg(v_expectedType_5404_, v___y_5408_);
v_a_5536_ = lean_ctor_get(v___x_5535_, 0);
lean_inc(v_a_5536_);
lean_dec_ref(v___x_5535_);
v___x_5537_ = l_Lean_Expr_hasExprMVar(v_a_5536_);
lean_dec(v_a_5536_);
if (v___x_5537_ == 0)
{
v___y_5485_ = v___y_5405_;
v___y_5486_ = v___y_5406_;
v___y_5487_ = v___y_5407_;
v___y_5488_ = v___y_5408_;
v___y_5489_ = v___y_5409_;
v___y_5490_ = v___y_5410_;
goto v___jp_5484_;
}
else
{
lean_object* v___x_5538_; 
v___x_5538_ = l_Lean_Elab_Term_tryPostpone(v___y_5405_, v___y_5406_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_);
if (lean_obj_tag(v___x_5538_) == 0)
{
lean_dec_ref(v___x_5538_);
v___y_5485_ = v___y_5405_;
v___y_5486_ = v___y_5406_;
v___y_5487_ = v___y_5407_;
v___y_5488_ = v___y_5408_;
v___y_5489_ = v___y_5409_;
v___y_5490_ = v___y_5410_;
goto v___jp_5484_;
}
else
{
lean_object* v_a_5539_; lean_object* v___x_5541_; uint8_t v_isShared_5542_; uint8_t v_isSharedCheck_5546_; 
lean_dec_ref(v_expectedType_5404_);
lean_dec(v___x_5403_);
v_a_5539_ = lean_ctor_get(v___x_5538_, 0);
v_isSharedCheck_5546_ = !lean_is_exclusive(v___x_5538_);
if (v_isSharedCheck_5546_ == 0)
{
v___x_5541_ = v___x_5538_;
v_isShared_5542_ = v_isSharedCheck_5546_;
goto v_resetjp_5540_;
}
else
{
lean_inc(v_a_5539_);
lean_dec(v___x_5538_);
v___x_5541_ = lean_box(0);
v_isShared_5542_ = v_isSharedCheck_5546_;
goto v_resetjp_5540_;
}
v_resetjp_5540_:
{
lean_object* v___x_5544_; 
if (v_isShared_5542_ == 0)
{
v___x_5544_ = v___x_5541_;
goto v_reusejp_5543_;
}
else
{
lean_object* v_reuseFailAlloc_5545_; 
v_reuseFailAlloc_5545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5545_, 0, v_a_5539_);
v___x_5544_ = v_reuseFailAlloc_5545_;
goto v_reusejp_5543_;
}
v_reusejp_5543_:
{
return v___x_5544_;
}
}
}
}
v___jp_5412_:
{
lean_object* v___x_5420_; 
v___x_5420_ = l_Lean_Meta_Simp_Result_mkEqSymm(v_expectedType_5404_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_);
if (lean_obj_tag(v___x_5420_) == 0)
{
lean_object* v_a_5421_; lean_object* v___x_5422_; 
v_a_5421_ = lean_ctor_get(v___x_5420_, 0);
lean_inc(v_a_5421_);
lean_dec_ref(v___x_5420_);
v___x_5422_ = l_Lean_Meta_Simp_Result_mkEqTrans(v___y_5413_, v_a_5421_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_);
if (lean_obj_tag(v___x_5422_) == 0)
{
lean_object* v_a_5423_; lean_object* v___x_5424_; 
v_a_5423_ = lean_ctor_get(v___x_5422_, 0);
lean_inc(v_a_5423_);
lean_dec_ref(v___x_5422_);
v___x_5424_ = l_Lean_Meta_Simp_Result_mkCast(v_a_5423_, v___y_5414_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_);
return v___x_5424_;
}
else
{
lean_object* v_a_5425_; lean_object* v___x_5427_; uint8_t v_isShared_5428_; uint8_t v_isSharedCheck_5432_; 
lean_dec_ref(v___y_5414_);
v_a_5425_ = lean_ctor_get(v___x_5422_, 0);
v_isSharedCheck_5432_ = !lean_is_exclusive(v___x_5422_);
if (v_isSharedCheck_5432_ == 0)
{
v___x_5427_ = v___x_5422_;
v_isShared_5428_ = v_isSharedCheck_5432_;
goto v_resetjp_5426_;
}
else
{
lean_inc(v_a_5425_);
lean_dec(v___x_5422_);
v___x_5427_ = lean_box(0);
v_isShared_5428_ = v_isSharedCheck_5432_;
goto v_resetjp_5426_;
}
v_resetjp_5426_:
{
lean_object* v___x_5430_; 
if (v_isShared_5428_ == 0)
{
v___x_5430_ = v___x_5427_;
goto v_reusejp_5429_;
}
else
{
lean_object* v_reuseFailAlloc_5431_; 
v_reuseFailAlloc_5431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5431_, 0, v_a_5425_);
v___x_5430_ = v_reuseFailAlloc_5431_;
goto v_reusejp_5429_;
}
v_reusejp_5429_:
{
return v___x_5430_;
}
}
}
}
else
{
lean_object* v_a_5433_; lean_object* v___x_5435_; uint8_t v_isShared_5436_; uint8_t v_isSharedCheck_5440_; 
lean_dec_ref(v___y_5414_);
lean_dec_ref(v___y_5413_);
v_a_5433_ = lean_ctor_get(v___x_5420_, 0);
v_isSharedCheck_5440_ = !lean_is_exclusive(v___x_5420_);
if (v_isSharedCheck_5440_ == 0)
{
v___x_5435_ = v___x_5420_;
v_isShared_5436_ = v_isSharedCheck_5440_;
goto v_resetjp_5434_;
}
else
{
lean_inc(v_a_5433_);
lean_dec(v___x_5420_);
v___x_5435_ = lean_box(0);
v_isShared_5436_ = v_isSharedCheck_5440_;
goto v_resetjp_5434_;
}
v_resetjp_5434_:
{
lean_object* v___x_5438_; 
if (v_isShared_5436_ == 0)
{
v___x_5438_ = v___x_5435_;
goto v_reusejp_5437_;
}
else
{
lean_object* v_reuseFailAlloc_5439_; 
v_reuseFailAlloc_5439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5439_, 0, v_a_5433_);
v___x_5438_ = v_reuseFailAlloc_5439_;
goto v_reusejp_5437_;
}
v_reusejp_5437_:
{
return v___x_5438_;
}
}
}
}
v___jp_5441_:
{
lean_object* v___x_5451_; 
v___x_5451_ = l_Lean_Elab_Tactic_NormCast_derive(v___y_5446_, v___y_5443_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_);
if (lean_obj_tag(v___x_5451_) == 0)
{
lean_object* v_a_5452_; lean_object* v_expr_5453_; lean_object* v___x_5454_; 
v_a_5452_ = lean_ctor_get(v___x_5451_, 0);
lean_inc(v_a_5452_);
lean_dec_ref(v___x_5451_);
v_expr_5453_ = lean_ctor_get(v_a_5452_, 0);
lean_inc_ref(v___y_5444_);
lean_inc_ref(v_expr_5453_);
v___x_5454_ = l_Lean_Meta_isExprDefEq(v_expr_5453_, v___y_5444_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_);
if (lean_obj_tag(v___x_5454_) == 0)
{
lean_object* v_a_5455_; uint8_t v___x_5456_; 
v_a_5455_ = lean_ctor_get(v___x_5454_, 0);
lean_inc(v_a_5455_);
lean_dec_ref(v___x_5454_);
v___x_5456_ = lean_unbox(v_a_5455_);
lean_dec(v_a_5455_);
if (v___x_5456_ == 0)
{
lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; 
v___x_5457_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__3, &l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__3);
v___x_5458_ = lean_box(0);
lean_inc_ref(v___y_5442_);
lean_inc_ref(v_expr_5453_);
v___x_5459_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_5457_, v___y_5444_, v_expr_5453_, v___y_5442_, v___x_5458_, v___y_5447_, v___y_5448_, v___y_5449_, v___y_5450_);
if (lean_obj_tag(v___x_5459_) == 0)
{
lean_dec_ref(v___x_5459_);
v___y_5413_ = v_a_5452_;
v___y_5414_ = v___y_5442_;
v___y_5415_ = v___y_5445_;
v___y_5416_ = v___y_5447_;
v___y_5417_ = v___y_5448_;
v___y_5418_ = v___y_5449_;
v___y_5419_ = v___y_5450_;
goto v___jp_5412_;
}
else
{
lean_object* v_a_5460_; lean_object* v___x_5462_; uint8_t v_isShared_5463_; uint8_t v_isSharedCheck_5467_; 
lean_dec(v_a_5452_);
lean_dec_ref(v___y_5445_);
lean_dec_ref(v___y_5442_);
lean_dec_ref(v_expectedType_5404_);
v_a_5460_ = lean_ctor_get(v___x_5459_, 0);
v_isSharedCheck_5467_ = !lean_is_exclusive(v___x_5459_);
if (v_isSharedCheck_5467_ == 0)
{
v___x_5462_ = v___x_5459_;
v_isShared_5463_ = v_isSharedCheck_5467_;
goto v_resetjp_5461_;
}
else
{
lean_inc(v_a_5460_);
lean_dec(v___x_5459_);
v___x_5462_ = lean_box(0);
v_isShared_5463_ = v_isSharedCheck_5467_;
goto v_resetjp_5461_;
}
v_resetjp_5461_:
{
lean_object* v___x_5465_; 
if (v_isShared_5463_ == 0)
{
v___x_5465_ = v___x_5462_;
goto v_reusejp_5464_;
}
else
{
lean_object* v_reuseFailAlloc_5466_; 
v_reuseFailAlloc_5466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5466_, 0, v_a_5460_);
v___x_5465_ = v_reuseFailAlloc_5466_;
goto v_reusejp_5464_;
}
v_reusejp_5464_:
{
return v___x_5465_;
}
}
}
}
else
{
lean_dec_ref(v___y_5444_);
v___y_5413_ = v_a_5452_;
v___y_5414_ = v___y_5442_;
v___y_5415_ = v___y_5445_;
v___y_5416_ = v___y_5447_;
v___y_5417_ = v___y_5448_;
v___y_5418_ = v___y_5449_;
v___y_5419_ = v___y_5450_;
goto v___jp_5412_;
}
}
else
{
lean_object* v_a_5468_; lean_object* v___x_5470_; uint8_t v_isShared_5471_; uint8_t v_isSharedCheck_5475_; 
lean_dec(v_a_5452_);
lean_dec_ref(v___y_5445_);
lean_dec_ref(v___y_5444_);
lean_dec_ref(v___y_5442_);
lean_dec_ref(v_expectedType_5404_);
v_a_5468_ = lean_ctor_get(v___x_5454_, 0);
v_isSharedCheck_5475_ = !lean_is_exclusive(v___x_5454_);
if (v_isSharedCheck_5475_ == 0)
{
v___x_5470_ = v___x_5454_;
v_isShared_5471_ = v_isSharedCheck_5475_;
goto v_resetjp_5469_;
}
else
{
lean_inc(v_a_5468_);
lean_dec(v___x_5454_);
v___x_5470_ = lean_box(0);
v_isShared_5471_ = v_isSharedCheck_5475_;
goto v_resetjp_5469_;
}
v_resetjp_5469_:
{
lean_object* v___x_5473_; 
if (v_isShared_5471_ == 0)
{
v___x_5473_ = v___x_5470_;
goto v_reusejp_5472_;
}
else
{
lean_object* v_reuseFailAlloc_5474_; 
v_reuseFailAlloc_5474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5474_, 0, v_a_5468_);
v___x_5473_ = v_reuseFailAlloc_5474_;
goto v_reusejp_5472_;
}
v_reusejp_5472_:
{
return v___x_5473_;
}
}
}
}
else
{
lean_object* v_a_5476_; lean_object* v___x_5478_; uint8_t v_isShared_5479_; uint8_t v_isSharedCheck_5483_; 
lean_dec_ref(v___y_5445_);
lean_dec_ref(v___y_5444_);
lean_dec_ref(v___y_5442_);
lean_dec_ref(v_expectedType_5404_);
v_a_5476_ = lean_ctor_get(v___x_5451_, 0);
v_isSharedCheck_5483_ = !lean_is_exclusive(v___x_5451_);
if (v_isSharedCheck_5483_ == 0)
{
v___x_5478_ = v___x_5451_;
v_isShared_5479_ = v_isSharedCheck_5483_;
goto v_resetjp_5477_;
}
else
{
lean_inc(v_a_5476_);
lean_dec(v___x_5451_);
v___x_5478_ = lean_box(0);
v_isShared_5479_ = v_isSharedCheck_5483_;
goto v_resetjp_5477_;
}
v_resetjp_5477_:
{
lean_object* v___x_5481_; 
if (v_isShared_5479_ == 0)
{
v___x_5481_ = v___x_5478_;
goto v_reusejp_5480_;
}
else
{
lean_object* v_reuseFailAlloc_5482_; 
v_reuseFailAlloc_5482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5482_, 0, v_a_5476_);
v___x_5481_ = v_reuseFailAlloc_5482_;
goto v_reusejp_5480_;
}
v_reusejp_5480_:
{
return v___x_5481_;
}
}
}
}
v___jp_5484_:
{
lean_object* v___x_5491_; lean_object* v___x_5492_; uint8_t v___x_5493_; uint8_t v___x_5494_; lean_object* v___x_5495_; lean_object* v___x_5496_; lean_object* v___x_5497_; 
v___x_5491_ = lean_unsigned_to_nat(100000u);
v___x_5492_ = lean_unsigned_to_nat(2u);
v___x_5493_ = 0;
v___x_5494_ = 0;
v___x_5495_ = lean_box(0);
v___x_5496_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_5496_, 0, v___x_5491_);
lean_ctor_set(v___x_5496_, 1, v___x_5492_);
lean_ctor_set(v___x_5496_, 2, v___x_5495_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3, v___x_5493_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 1, v___x_5402_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 2, v___x_5493_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 3, v___x_5493_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 4, v___x_5493_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 5, v___x_5493_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 6, v___x_5494_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 7, v___x_5493_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 8, v___x_5493_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 9, v___x_5493_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 10, v___x_5493_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 11, v___x_5493_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 12, v___x_5402_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 13, v___x_5402_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 14, v___x_5493_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 15, v___x_5493_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 16, v___x_5493_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 17, v___x_5402_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 18, v___x_5402_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 19, v___x_5402_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 20, v___x_5402_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 21, v___x_5402_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 22, v___x_5402_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 23, v___x_5402_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 24, v___x_5402_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 25, v___x_5402_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 26, v___x_5493_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 27, v___x_5493_);
lean_ctor_set_uint8(v___x_5496_, sizeof(void*)*3 + 28, v___x_5493_);
lean_inc_ref(v___x_5496_);
lean_inc_ref(v_expectedType_5404_);
v___x_5497_ = l_Lean_Elab_Tactic_NormCast_derive(v_expectedType_5404_, v___x_5496_, v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_);
if (lean_obj_tag(v___x_5497_) == 0)
{
lean_object* v_a_5498_; lean_object* v_expr_5499_; lean_object* v___x_5500_; lean_object* v___x_5501_; 
v_a_5498_ = lean_ctor_get(v___x_5497_, 0);
lean_inc(v_a_5498_);
lean_dec_ref(v___x_5497_);
v_expr_5499_ = lean_ctor_get(v_a_5498_, 0);
lean_inc_ref_n(v_expr_5499_, 2);
v___x_5500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5500_, 0, v_expr_5499_);
v___x_5501_ = l_Lean_Elab_Term_elabTerm(v___x_5403_, v___x_5500_, v___x_5402_, v___x_5402_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_);
if (lean_obj_tag(v___x_5501_) == 0)
{
lean_object* v_a_5502_; uint8_t v___x_5503_; lean_object* v___x_5504_; 
v_a_5502_ = lean_ctor_get(v___x_5501_, 0);
lean_inc(v_a_5502_);
lean_dec_ref(v___x_5501_);
v___x_5503_ = 0;
v___x_5504_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_5503_, v___x_5493_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_);
if (lean_obj_tag(v___x_5504_) == 0)
{
lean_object* v___x_5505_; 
lean_dec_ref(v___x_5504_);
lean_inc(v___y_5490_);
lean_inc_ref(v___y_5489_);
lean_inc(v___y_5488_);
lean_inc_ref(v___y_5487_);
lean_inc(v_a_5502_);
v___x_5505_ = lean_infer_type(v_a_5502_, v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_);
if (lean_obj_tag(v___x_5505_) == 0)
{
lean_object* v_a_5506_; lean_object* v___x_5507_; lean_object* v_a_5508_; uint8_t v___x_5509_; 
v_a_5506_ = lean_ctor_get(v___x_5505_, 0);
lean_inc(v_a_5506_);
lean_dec_ref(v___x_5505_);
v___x_5507_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg(v_a_5506_, v___y_5488_);
v_a_5508_ = lean_ctor_get(v___x_5507_, 0);
lean_inc(v_a_5508_);
lean_dec_ref(v___x_5507_);
v___x_5509_ = l_Lean_Expr_hasExprMVar(v_a_5508_);
if (v___x_5509_ == 0)
{
v___y_5442_ = v_a_5502_;
v___y_5443_ = v___x_5496_;
v___y_5444_ = v_expr_5499_;
v___y_5445_ = v_a_5498_;
v___y_5446_ = v_a_5508_;
v___y_5447_ = v___y_5487_;
v___y_5448_ = v___y_5488_;
v___y_5449_ = v___y_5489_;
v___y_5450_ = v___y_5490_;
goto v___jp_5441_;
}
else
{
lean_object* v___x_5510_; 
v___x_5510_ = l_Lean_Elab_Term_tryPostpone(v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_, v___y_5490_);
if (lean_obj_tag(v___x_5510_) == 0)
{
lean_dec_ref(v___x_5510_);
v___y_5442_ = v_a_5502_;
v___y_5443_ = v___x_5496_;
v___y_5444_ = v_expr_5499_;
v___y_5445_ = v_a_5498_;
v___y_5446_ = v_a_5508_;
v___y_5447_ = v___y_5487_;
v___y_5448_ = v___y_5488_;
v___y_5449_ = v___y_5489_;
v___y_5450_ = v___y_5490_;
goto v___jp_5441_;
}
else
{
lean_object* v_a_5511_; lean_object* v___x_5513_; uint8_t v_isShared_5514_; uint8_t v_isSharedCheck_5518_; 
lean_dec(v_a_5508_);
lean_dec(v_a_5502_);
lean_dec_ref(v_expr_5499_);
lean_dec(v_a_5498_);
lean_dec_ref(v___x_5496_);
lean_dec_ref(v_expectedType_5404_);
v_a_5511_ = lean_ctor_get(v___x_5510_, 0);
v_isSharedCheck_5518_ = !lean_is_exclusive(v___x_5510_);
if (v_isSharedCheck_5518_ == 0)
{
v___x_5513_ = v___x_5510_;
v_isShared_5514_ = v_isSharedCheck_5518_;
goto v_resetjp_5512_;
}
else
{
lean_inc(v_a_5511_);
lean_dec(v___x_5510_);
v___x_5513_ = lean_box(0);
v_isShared_5514_ = v_isSharedCheck_5518_;
goto v_resetjp_5512_;
}
v_resetjp_5512_:
{
lean_object* v___x_5516_; 
if (v_isShared_5514_ == 0)
{
v___x_5516_ = v___x_5513_;
goto v_reusejp_5515_;
}
else
{
lean_object* v_reuseFailAlloc_5517_; 
v_reuseFailAlloc_5517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5517_, 0, v_a_5511_);
v___x_5516_ = v_reuseFailAlloc_5517_;
goto v_reusejp_5515_;
}
v_reusejp_5515_:
{
return v___x_5516_;
}
}
}
}
}
else
{
lean_dec(v_a_5502_);
lean_dec_ref(v_expr_5499_);
lean_dec(v_a_5498_);
lean_dec_ref(v___x_5496_);
lean_dec_ref(v_expectedType_5404_);
return v___x_5505_;
}
}
else
{
lean_object* v_a_5519_; lean_object* v___x_5521_; uint8_t v_isShared_5522_; uint8_t v_isSharedCheck_5526_; 
lean_dec(v_a_5502_);
lean_dec_ref(v_expr_5499_);
lean_dec(v_a_5498_);
lean_dec_ref(v___x_5496_);
lean_dec_ref(v_expectedType_5404_);
v_a_5519_ = lean_ctor_get(v___x_5504_, 0);
v_isSharedCheck_5526_ = !lean_is_exclusive(v___x_5504_);
if (v_isSharedCheck_5526_ == 0)
{
v___x_5521_ = v___x_5504_;
v_isShared_5522_ = v_isSharedCheck_5526_;
goto v_resetjp_5520_;
}
else
{
lean_inc(v_a_5519_);
lean_dec(v___x_5504_);
v___x_5521_ = lean_box(0);
v_isShared_5522_ = v_isSharedCheck_5526_;
goto v_resetjp_5520_;
}
v_resetjp_5520_:
{
lean_object* v___x_5524_; 
if (v_isShared_5522_ == 0)
{
v___x_5524_ = v___x_5521_;
goto v_reusejp_5523_;
}
else
{
lean_object* v_reuseFailAlloc_5525_; 
v_reuseFailAlloc_5525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5525_, 0, v_a_5519_);
v___x_5524_ = v_reuseFailAlloc_5525_;
goto v_reusejp_5523_;
}
v_reusejp_5523_:
{
return v___x_5524_;
}
}
}
}
else
{
lean_dec_ref(v_expr_5499_);
lean_dec(v_a_5498_);
lean_dec_ref(v___x_5496_);
lean_dec_ref(v_expectedType_5404_);
return v___x_5501_;
}
}
else
{
lean_object* v_a_5527_; lean_object* v___x_5529_; uint8_t v_isShared_5530_; uint8_t v_isSharedCheck_5534_; 
lean_dec_ref(v___x_5496_);
lean_dec_ref(v_expectedType_5404_);
lean_dec(v___x_5403_);
v_a_5527_ = lean_ctor_get(v___x_5497_, 0);
v_isSharedCheck_5534_ = !lean_is_exclusive(v___x_5497_);
if (v_isSharedCheck_5534_ == 0)
{
v___x_5529_ = v___x_5497_;
v_isShared_5530_ = v_isSharedCheck_5534_;
goto v_resetjp_5528_;
}
else
{
lean_inc(v_a_5527_);
lean_dec(v___x_5497_);
v___x_5529_ = lean_box(0);
v_isShared_5530_ = v_isSharedCheck_5534_;
goto v_resetjp_5528_;
}
v_resetjp_5528_:
{
lean_object* v___x_5532_; 
if (v_isShared_5530_ == 0)
{
v___x_5532_ = v___x_5529_;
goto v_reusejp_5531_;
}
else
{
lean_object* v_reuseFailAlloc_5533_; 
v_reuseFailAlloc_5533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5533_, 0, v_a_5527_);
v___x_5532_ = v_reuseFailAlloc_5533_;
goto v_reusejp_5531_;
}
v_reusejp_5531_:
{
return v___x_5532_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___boxed(lean_object* v___x_5547_, lean_object* v___x_5548_, lean_object* v_expectedType_5549_, lean_object* v___y_5550_, lean_object* v___y_5551_, lean_object* v___y_5552_, lean_object* v___y_5553_, lean_object* v___y_5554_, lean_object* v___y_5555_, lean_object* v___y_5556_){
_start:
{
uint8_t v___x_4153__boxed_5557_; lean_object* v_res_5558_; 
v___x_4153__boxed_5557_ = lean_unbox(v___x_5547_);
v_res_5558_ = l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0(v___x_4153__boxed_5557_, v___x_5548_, v_expectedType_5549_, v___y_5550_, v___y_5551_, v___y_5552_, v___y_5553_, v___y_5554_, v___y_5555_);
lean_dec(v___y_5555_);
lean_dec_ref(v___y_5554_);
lean_dec(v___y_5553_);
lean_dec_ref(v___y_5552_);
lean_dec(v___y_5551_);
lean_dec_ref(v___y_5550_);
return v_res_5558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast(lean_object* v_stx_5563_, lean_object* v_expectedType_x3f_5564_, lean_object* v_a_5565_, lean_object* v_a_5566_, lean_object* v_a_5567_, lean_object* v_a_5568_, lean_object* v_a_5569_, lean_object* v_a_5570_){
_start:
{
lean_object* v___x_5572_; uint8_t v___x_5573_; 
v___x_5572_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabModCast___closed__1));
lean_inc(v_stx_5563_);
v___x_5573_ = l_Lean_Syntax_isOfKind(v_stx_5563_, v___x_5572_);
if (v___x_5573_ == 0)
{
lean_object* v___x_5574_; 
lean_dec(v_expectedType_x3f_5564_);
lean_dec(v_stx_5563_);
v___x_5574_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg();
return v___x_5574_;
}
else
{
lean_object* v___x_5575_; lean_object* v___x_5576_; lean_object* v___x_5577_; lean_object* v___f_5578_; lean_object* v___x_5579_; 
v___x_5575_ = lean_unsigned_to_nat(1u);
v___x_5576_ = l_Lean_Syntax_getArg(v_stx_5563_, v___x_5575_);
lean_dec(v_stx_5563_);
v___x_5577_ = lean_box(v___x_5573_);
v___f_5578_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___boxed), 10, 2);
lean_closure_set(v___f_5578_, 0, v___x_5577_);
lean_closure_set(v___f_5578_, 1, v___x_5576_);
v___x_5579_ = l_Lean_Elab_Term_withExpectedType(v_expectedType_x3f_5564_, v___f_5578_, v_a_5565_, v_a_5566_, v_a_5567_, v_a_5568_, v_a_5569_, v_a_5570_);
return v___x_5579_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___boxed(lean_object* v_stx_5580_, lean_object* v_expectedType_x3f_5581_, lean_object* v_a_5582_, lean_object* v_a_5583_, lean_object* v_a_5584_, lean_object* v_a_5585_, lean_object* v_a_5586_, lean_object* v_a_5587_, lean_object* v_a_5588_){
_start:
{
lean_object* v_res_5589_; 
v_res_5589_ = l_Lean_Elab_Tactic_NormCast_elabModCast(v_stx_5580_, v_expectedType_x3f_5581_, v_a_5582_, v_a_5583_, v_a_5584_, v_a_5585_, v_a_5586_, v_a_5587_);
lean_dec(v_a_5587_);
lean_dec_ref(v_a_5586_);
lean_dec(v_a_5585_);
lean_dec_ref(v_a_5584_);
lean_dec(v_a_5583_);
lean_dec_ref(v_a_5582_);
return v_res_5589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1(){
_start:
{
lean_object* v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; lean_object* v___x_5601_; lean_object* v___x_5602_; 
v___x_5598_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5599_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabModCast___closed__1));
v___x_5600_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1));
v___x_5601_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_elabModCast___boxed), 9, 0);
v___x_5602_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5598_, v___x_5599_, v___x_5600_, v___x_5601_);
return v___x_5602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___boxed(lean_object* v_a_5603_){
_start:
{
lean_object* v_res_5604_; 
v_res_5604_ = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1();
return v_res_5604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3(){
_start:
{
lean_object* v___x_5631_; lean_object* v___x_5632_; lean_object* v___x_5633_; 
v___x_5631_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1));
v___x_5632_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__6));
v___x_5633_ = l_Lean_addBuiltinDeclarationRanges(v___x_5631_, v___x_5632_);
return v___x_5633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___boxed(lean_object* v_a_5634_){
_start:
{
lean_object* v_res_5635_; 
v_res_5635_ = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3();
return v_res_5635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___lam__0(lean_object* v_cfg_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_, lean_object* v___y_5640_, lean_object* v___y_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_){
_start:
{
lean_object* v___x_5646_; 
v___x_5646_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_5638_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_);
if (lean_obj_tag(v___x_5646_) == 0)
{
lean_object* v_a_5647_; lean_object* v___x_5648_; 
v_a_5647_ = lean_ctor_get(v___x_5646_, 0);
lean_inc_n(v_a_5647_, 2);
lean_dec_ref(v___x_5646_);
v___x_5648_ = l_Lean_MVarId_getType(v_a_5647_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_);
if (lean_obj_tag(v___x_5648_) == 0)
{
lean_object* v_a_5649_; lean_object* v___x_5650_; lean_object* v_a_5651_; lean_object* v___x_5652_; 
v_a_5649_ = lean_ctor_get(v___x_5648_, 0);
lean_inc(v_a_5649_);
lean_dec_ref(v___x_5648_);
v___x_5650_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_a_5649_, v___y_5642_);
v_a_5651_ = lean_ctor_get(v___x_5650_, 0);
lean_inc_n(v_a_5651_, 2);
lean_dec_ref(v___x_5650_);
v___x_5652_ = l_Lean_Elab_Tactic_NormCast_derive(v_a_5651_, v_cfg_5636_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_);
if (lean_obj_tag(v___x_5652_) == 0)
{
lean_object* v_a_5653_; lean_object* v___x_5654_; 
v_a_5653_ = lean_ctor_get(v___x_5652_, 0);
lean_inc(v_a_5653_);
lean_dec_ref(v___x_5652_);
v___x_5654_ = l_Lean_Meta_applySimpResultToTarget(v_a_5647_, v_a_5651_, v_a_5653_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_);
lean_dec(v_a_5651_);
if (lean_obj_tag(v___x_5654_) == 0)
{
lean_object* v_a_5655_; lean_object* v___x_5656_; lean_object* v___x_5657_; lean_object* v___x_5658_; 
v_a_5655_ = lean_ctor_get(v___x_5654_, 0);
lean_inc(v_a_5655_);
lean_dec_ref(v___x_5654_);
v___x_5656_ = lean_box(0);
v___x_5657_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5657_, 0, v_a_5655_);
lean_ctor_set(v___x_5657_, 1, v___x_5656_);
v___x_5658_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_5657_, v___y_5638_, v___y_5641_, v___y_5642_, v___y_5643_, v___y_5644_);
return v___x_5658_;
}
else
{
lean_object* v_a_5659_; lean_object* v___x_5661_; uint8_t v_isShared_5662_; uint8_t v_isSharedCheck_5666_; 
v_a_5659_ = lean_ctor_get(v___x_5654_, 0);
v_isSharedCheck_5666_ = !lean_is_exclusive(v___x_5654_);
if (v_isSharedCheck_5666_ == 0)
{
v___x_5661_ = v___x_5654_;
v_isShared_5662_ = v_isSharedCheck_5666_;
goto v_resetjp_5660_;
}
else
{
lean_inc(v_a_5659_);
lean_dec(v___x_5654_);
v___x_5661_ = lean_box(0);
v_isShared_5662_ = v_isSharedCheck_5666_;
goto v_resetjp_5660_;
}
v_resetjp_5660_:
{
lean_object* v___x_5664_; 
if (v_isShared_5662_ == 0)
{
v___x_5664_ = v___x_5661_;
goto v_reusejp_5663_;
}
else
{
lean_object* v_reuseFailAlloc_5665_; 
v_reuseFailAlloc_5665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5665_, 0, v_a_5659_);
v___x_5664_ = v_reuseFailAlloc_5665_;
goto v_reusejp_5663_;
}
v_reusejp_5663_:
{
return v___x_5664_;
}
}
}
}
else
{
lean_object* v_a_5667_; lean_object* v___x_5669_; uint8_t v_isShared_5670_; uint8_t v_isSharedCheck_5674_; 
lean_dec(v_a_5651_);
lean_dec(v_a_5647_);
v_a_5667_ = lean_ctor_get(v___x_5652_, 0);
v_isSharedCheck_5674_ = !lean_is_exclusive(v___x_5652_);
if (v_isSharedCheck_5674_ == 0)
{
v___x_5669_ = v___x_5652_;
v_isShared_5670_ = v_isSharedCheck_5674_;
goto v_resetjp_5668_;
}
else
{
lean_inc(v_a_5667_);
lean_dec(v___x_5652_);
v___x_5669_ = lean_box(0);
v_isShared_5670_ = v_isSharedCheck_5674_;
goto v_resetjp_5668_;
}
v_resetjp_5668_:
{
lean_object* v___x_5672_; 
if (v_isShared_5670_ == 0)
{
v___x_5672_ = v___x_5669_;
goto v_reusejp_5671_;
}
else
{
lean_object* v_reuseFailAlloc_5673_; 
v_reuseFailAlloc_5673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5673_, 0, v_a_5667_);
v___x_5672_ = v_reuseFailAlloc_5673_;
goto v_reusejp_5671_;
}
v_reusejp_5671_:
{
return v___x_5672_;
}
}
}
}
else
{
lean_object* v_a_5675_; lean_object* v___x_5677_; uint8_t v_isShared_5678_; uint8_t v_isSharedCheck_5682_; 
lean_dec(v_a_5647_);
lean_dec_ref(v_cfg_5636_);
v_a_5675_ = lean_ctor_get(v___x_5648_, 0);
v_isSharedCheck_5682_ = !lean_is_exclusive(v___x_5648_);
if (v_isSharedCheck_5682_ == 0)
{
v___x_5677_ = v___x_5648_;
v_isShared_5678_ = v_isSharedCheck_5682_;
goto v_resetjp_5676_;
}
else
{
lean_inc(v_a_5675_);
lean_dec(v___x_5648_);
v___x_5677_ = lean_box(0);
v_isShared_5678_ = v_isSharedCheck_5682_;
goto v_resetjp_5676_;
}
v_resetjp_5676_:
{
lean_object* v___x_5680_; 
if (v_isShared_5678_ == 0)
{
v___x_5680_ = v___x_5677_;
goto v_reusejp_5679_;
}
else
{
lean_object* v_reuseFailAlloc_5681_; 
v_reuseFailAlloc_5681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5681_, 0, v_a_5675_);
v___x_5680_ = v_reuseFailAlloc_5681_;
goto v_reusejp_5679_;
}
v_reusejp_5679_:
{
return v___x_5680_;
}
}
}
}
else
{
lean_object* v_a_5683_; lean_object* v___x_5685_; uint8_t v_isShared_5686_; uint8_t v_isSharedCheck_5690_; 
lean_dec_ref(v_cfg_5636_);
v_a_5683_ = lean_ctor_get(v___x_5646_, 0);
v_isSharedCheck_5690_ = !lean_is_exclusive(v___x_5646_);
if (v_isSharedCheck_5690_ == 0)
{
v___x_5685_ = v___x_5646_;
v_isShared_5686_ = v_isSharedCheck_5690_;
goto v_resetjp_5684_;
}
else
{
lean_inc(v_a_5683_);
lean_dec(v___x_5646_);
v___x_5685_ = lean_box(0);
v_isShared_5686_ = v_isSharedCheck_5690_;
goto v_resetjp_5684_;
}
v_resetjp_5684_:
{
lean_object* v___x_5688_; 
if (v_isShared_5686_ == 0)
{
v___x_5688_ = v___x_5685_;
goto v_reusejp_5687_;
}
else
{
lean_object* v_reuseFailAlloc_5689_; 
v_reuseFailAlloc_5689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5689_, 0, v_a_5683_);
v___x_5688_ = v_reuseFailAlloc_5689_;
goto v_reusejp_5687_;
}
v_reusejp_5687_:
{
return v___x_5688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___lam__0___boxed(lean_object* v_cfg_5691_, lean_object* v___y_5692_, lean_object* v___y_5693_, lean_object* v___y_5694_, lean_object* v___y_5695_, lean_object* v___y_5696_, lean_object* v___y_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_){
_start:
{
lean_object* v_res_5701_; 
v_res_5701_ = l_Lean_Elab_Tactic_NormCast_normCastTarget___lam__0(v_cfg_5691_, v___y_5692_, v___y_5693_, v___y_5694_, v___y_5695_, v___y_5696_, v___y_5697_, v___y_5698_, v___y_5699_);
lean_dec(v___y_5699_);
lean_dec_ref(v___y_5698_);
lean_dec(v___y_5697_);
lean_dec_ref(v___y_5696_);
lean_dec(v___y_5695_);
lean_dec_ref(v___y_5694_);
lean_dec(v___y_5693_);
lean_dec_ref(v___y_5692_);
return v_res_5701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget(lean_object* v_cfg_5702_, lean_object* v_a_5703_, lean_object* v_a_5704_, lean_object* v_a_5705_, lean_object* v_a_5706_, lean_object* v_a_5707_, lean_object* v_a_5708_, lean_object* v_a_5709_, lean_object* v_a_5710_){
_start:
{
lean_object* v___f_5712_; lean_object* v___x_5713_; 
v___f_5712_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_normCastTarget___lam__0___boxed), 10, 1);
lean_closure_set(v___f_5712_, 0, v_cfg_5702_);
v___x_5713_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_5712_, v_a_5703_, v_a_5704_, v_a_5705_, v_a_5706_, v_a_5707_, v_a_5708_, v_a_5709_, v_a_5710_);
return v___x_5713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___boxed(lean_object* v_cfg_5714_, lean_object* v_a_5715_, lean_object* v_a_5716_, lean_object* v_a_5717_, lean_object* v_a_5718_, lean_object* v_a_5719_, lean_object* v_a_5720_, lean_object* v_a_5721_, lean_object* v_a_5722_, lean_object* v_a_5723_){
_start:
{
lean_object* v_res_5724_; 
v_res_5724_ = l_Lean_Elab_Tactic_NormCast_normCastTarget(v_cfg_5714_, v_a_5715_, v_a_5716_, v_a_5717_, v_a_5718_, v_a_5719_, v_a_5720_, v_a_5721_, v_a_5722_);
lean_dec(v_a_5722_);
lean_dec_ref(v_a_5721_);
lean_dec(v_a_5720_);
lean_dec_ref(v_a_5719_);
lean_dec(v_a_5718_);
lean_dec_ref(v_a_5717_);
lean_dec(v_a_5716_);
lean_dec_ref(v_a_5715_);
return v_res_5724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp___lam__0(lean_object* v_fvarId_5725_, lean_object* v_cfg_5726_, lean_object* v___y_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_, lean_object* v___y_5730_, lean_object* v___y_5731_, lean_object* v___y_5732_, lean_object* v___y_5733_, lean_object* v___y_5734_){
_start:
{
lean_object* v___x_5736_; 
v___x_5736_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_5728_, v___y_5731_, v___y_5732_, v___y_5733_, v___y_5734_);
if (lean_obj_tag(v___x_5736_) == 0)
{
lean_object* v_a_5737_; lean_object* v___x_5738_; 
v_a_5737_ = lean_ctor_get(v___x_5736_, 0);
lean_inc(v_a_5737_);
lean_dec_ref(v___x_5736_);
lean_inc(v_fvarId_5725_);
v___x_5738_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_5725_, v___y_5731_, v___y_5733_, v___y_5734_);
if (lean_obj_tag(v___x_5738_) == 0)
{
lean_object* v_a_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v_a_5742_; lean_object* v___x_5743_; 
v_a_5739_ = lean_ctor_get(v___x_5738_, 0);
lean_inc(v_a_5739_);
lean_dec_ref(v___x_5738_);
v___x_5740_ = l_Lean_LocalDecl_type(v_a_5739_);
lean_dec(v_a_5739_);
v___x_5741_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v___x_5740_, v___y_5732_);
v_a_5742_ = lean_ctor_get(v___x_5741_, 0);
lean_inc(v_a_5742_);
lean_dec_ref(v___x_5741_);
v___x_5743_ = l_Lean_Elab_Tactic_NormCast_derive(v_a_5742_, v_cfg_5726_, v___y_5731_, v___y_5732_, v___y_5733_, v___y_5734_);
if (lean_obj_tag(v___x_5743_) == 0)
{
lean_object* v_a_5744_; uint8_t v___x_5745_; lean_object* v___x_5746_; 
v_a_5744_ = lean_ctor_get(v___x_5743_, 0);
lean_inc(v_a_5744_);
lean_dec_ref(v___x_5743_);
v___x_5745_ = 0;
v___x_5746_ = l_Lean_Meta_applySimpResultToLocalDecl(v_a_5737_, v_fvarId_5725_, v_a_5744_, v___x_5745_, v___y_5731_, v___y_5732_, v___y_5733_, v___y_5734_);
if (lean_obj_tag(v___x_5746_) == 0)
{
lean_object* v_a_5747_; 
v_a_5747_ = lean_ctor_get(v___x_5746_, 0);
lean_inc(v_a_5747_);
lean_dec_ref(v___x_5746_);
if (lean_obj_tag(v_a_5747_) == 0)
{
lean_object* v___x_5748_; lean_object* v___x_5749_; 
v___x_5748_ = lean_box(0);
v___x_5749_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_5748_, v___y_5728_, v___y_5731_, v___y_5732_, v___y_5733_, v___y_5734_);
return v___x_5749_;
}
else
{
lean_object* v_val_5750_; lean_object* v_snd_5751_; lean_object* v___x_5753_; uint8_t v_isShared_5754_; uint8_t v_isSharedCheck_5760_; 
v_val_5750_ = lean_ctor_get(v_a_5747_, 0);
lean_inc(v_val_5750_);
lean_dec_ref(v_a_5747_);
v_snd_5751_ = lean_ctor_get(v_val_5750_, 1);
v_isSharedCheck_5760_ = !lean_is_exclusive(v_val_5750_);
if (v_isSharedCheck_5760_ == 0)
{
lean_object* v_unused_5761_; 
v_unused_5761_ = lean_ctor_get(v_val_5750_, 0);
lean_dec(v_unused_5761_);
v___x_5753_ = v_val_5750_;
v_isShared_5754_ = v_isSharedCheck_5760_;
goto v_resetjp_5752_;
}
else
{
lean_inc(v_snd_5751_);
lean_dec(v_val_5750_);
v___x_5753_ = lean_box(0);
v_isShared_5754_ = v_isSharedCheck_5760_;
goto v_resetjp_5752_;
}
v_resetjp_5752_:
{
lean_object* v___x_5755_; lean_object* v___x_5757_; 
v___x_5755_ = lean_box(0);
if (v_isShared_5754_ == 0)
{
lean_ctor_set_tag(v___x_5753_, 1);
lean_ctor_set(v___x_5753_, 1, v___x_5755_);
lean_ctor_set(v___x_5753_, 0, v_snd_5751_);
v___x_5757_ = v___x_5753_;
goto v_reusejp_5756_;
}
else
{
lean_object* v_reuseFailAlloc_5759_; 
v_reuseFailAlloc_5759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5759_, 0, v_snd_5751_);
lean_ctor_set(v_reuseFailAlloc_5759_, 1, v___x_5755_);
v___x_5757_ = v_reuseFailAlloc_5759_;
goto v_reusejp_5756_;
}
v_reusejp_5756_:
{
lean_object* v___x_5758_; 
v___x_5758_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_5757_, v___y_5728_, v___y_5731_, v___y_5732_, v___y_5733_, v___y_5734_);
return v___x_5758_;
}
}
}
}
else
{
lean_object* v_a_5762_; lean_object* v___x_5764_; uint8_t v_isShared_5765_; uint8_t v_isSharedCheck_5769_; 
v_a_5762_ = lean_ctor_get(v___x_5746_, 0);
v_isSharedCheck_5769_ = !lean_is_exclusive(v___x_5746_);
if (v_isSharedCheck_5769_ == 0)
{
v___x_5764_ = v___x_5746_;
v_isShared_5765_ = v_isSharedCheck_5769_;
goto v_resetjp_5763_;
}
else
{
lean_inc(v_a_5762_);
lean_dec(v___x_5746_);
v___x_5764_ = lean_box(0);
v_isShared_5765_ = v_isSharedCheck_5769_;
goto v_resetjp_5763_;
}
v_resetjp_5763_:
{
lean_object* v___x_5767_; 
if (v_isShared_5765_ == 0)
{
v___x_5767_ = v___x_5764_;
goto v_reusejp_5766_;
}
else
{
lean_object* v_reuseFailAlloc_5768_; 
v_reuseFailAlloc_5768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5768_, 0, v_a_5762_);
v___x_5767_ = v_reuseFailAlloc_5768_;
goto v_reusejp_5766_;
}
v_reusejp_5766_:
{
return v___x_5767_;
}
}
}
}
else
{
lean_object* v_a_5770_; lean_object* v___x_5772_; uint8_t v_isShared_5773_; uint8_t v_isSharedCheck_5777_; 
lean_dec(v_a_5737_);
lean_dec(v_fvarId_5725_);
v_a_5770_ = lean_ctor_get(v___x_5743_, 0);
v_isSharedCheck_5777_ = !lean_is_exclusive(v___x_5743_);
if (v_isSharedCheck_5777_ == 0)
{
v___x_5772_ = v___x_5743_;
v_isShared_5773_ = v_isSharedCheck_5777_;
goto v_resetjp_5771_;
}
else
{
lean_inc(v_a_5770_);
lean_dec(v___x_5743_);
v___x_5772_ = lean_box(0);
v_isShared_5773_ = v_isSharedCheck_5777_;
goto v_resetjp_5771_;
}
v_resetjp_5771_:
{
lean_object* v___x_5775_; 
if (v_isShared_5773_ == 0)
{
v___x_5775_ = v___x_5772_;
goto v_reusejp_5774_;
}
else
{
lean_object* v_reuseFailAlloc_5776_; 
v_reuseFailAlloc_5776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5776_, 0, v_a_5770_);
v___x_5775_ = v_reuseFailAlloc_5776_;
goto v_reusejp_5774_;
}
v_reusejp_5774_:
{
return v___x_5775_;
}
}
}
}
else
{
lean_object* v_a_5778_; lean_object* v___x_5780_; uint8_t v_isShared_5781_; uint8_t v_isSharedCheck_5785_; 
lean_dec(v_a_5737_);
lean_dec_ref(v_cfg_5726_);
lean_dec(v_fvarId_5725_);
v_a_5778_ = lean_ctor_get(v___x_5738_, 0);
v_isSharedCheck_5785_ = !lean_is_exclusive(v___x_5738_);
if (v_isSharedCheck_5785_ == 0)
{
v___x_5780_ = v___x_5738_;
v_isShared_5781_ = v_isSharedCheck_5785_;
goto v_resetjp_5779_;
}
else
{
lean_inc(v_a_5778_);
lean_dec(v___x_5738_);
v___x_5780_ = lean_box(0);
v_isShared_5781_ = v_isSharedCheck_5785_;
goto v_resetjp_5779_;
}
v_resetjp_5779_:
{
lean_object* v___x_5783_; 
if (v_isShared_5781_ == 0)
{
v___x_5783_ = v___x_5780_;
goto v_reusejp_5782_;
}
else
{
lean_object* v_reuseFailAlloc_5784_; 
v_reuseFailAlloc_5784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5784_, 0, v_a_5778_);
v___x_5783_ = v_reuseFailAlloc_5784_;
goto v_reusejp_5782_;
}
v_reusejp_5782_:
{
return v___x_5783_;
}
}
}
}
else
{
lean_object* v_a_5786_; lean_object* v___x_5788_; uint8_t v_isShared_5789_; uint8_t v_isSharedCheck_5793_; 
lean_dec_ref(v_cfg_5726_);
lean_dec(v_fvarId_5725_);
v_a_5786_ = lean_ctor_get(v___x_5736_, 0);
v_isSharedCheck_5793_ = !lean_is_exclusive(v___x_5736_);
if (v_isSharedCheck_5793_ == 0)
{
v___x_5788_ = v___x_5736_;
v_isShared_5789_ = v_isSharedCheck_5793_;
goto v_resetjp_5787_;
}
else
{
lean_inc(v_a_5786_);
lean_dec(v___x_5736_);
v___x_5788_ = lean_box(0);
v_isShared_5789_ = v_isSharedCheck_5793_;
goto v_resetjp_5787_;
}
v_resetjp_5787_:
{
lean_object* v___x_5791_; 
if (v_isShared_5789_ == 0)
{
v___x_5791_ = v___x_5788_;
goto v_reusejp_5790_;
}
else
{
lean_object* v_reuseFailAlloc_5792_; 
v_reuseFailAlloc_5792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5792_, 0, v_a_5786_);
v___x_5791_ = v_reuseFailAlloc_5792_;
goto v_reusejp_5790_;
}
v_reusejp_5790_:
{
return v___x_5791_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp___lam__0___boxed(lean_object* v_fvarId_5794_, lean_object* v_cfg_5795_, lean_object* v___y_5796_, lean_object* v___y_5797_, lean_object* v___y_5798_, lean_object* v___y_5799_, lean_object* v___y_5800_, lean_object* v___y_5801_, lean_object* v___y_5802_, lean_object* v___y_5803_, lean_object* v___y_5804_){
_start:
{
lean_object* v_res_5805_; 
v_res_5805_ = l_Lean_Elab_Tactic_NormCast_normCastHyp___lam__0(v_fvarId_5794_, v_cfg_5795_, v___y_5796_, v___y_5797_, v___y_5798_, v___y_5799_, v___y_5800_, v___y_5801_, v___y_5802_, v___y_5803_);
lean_dec(v___y_5803_);
lean_dec_ref(v___y_5802_);
lean_dec(v___y_5801_);
lean_dec_ref(v___y_5800_);
lean_dec(v___y_5799_);
lean_dec_ref(v___y_5798_);
lean_dec(v___y_5797_);
lean_dec_ref(v___y_5796_);
return v_res_5805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp(lean_object* v_cfg_5806_, lean_object* v_fvarId_5807_, lean_object* v_a_5808_, lean_object* v_a_5809_, lean_object* v_a_5810_, lean_object* v_a_5811_, lean_object* v_a_5812_, lean_object* v_a_5813_, lean_object* v_a_5814_, lean_object* v_a_5815_){
_start:
{
lean_object* v___f_5817_; lean_object* v___x_5818_; 
v___f_5817_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_normCastHyp___lam__0___boxed), 11, 2);
lean_closure_set(v___f_5817_, 0, v_fvarId_5807_);
lean_closure_set(v___f_5817_, 1, v_cfg_5806_);
v___x_5818_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_5817_, v_a_5808_, v_a_5809_, v_a_5810_, v_a_5811_, v_a_5812_, v_a_5813_, v_a_5814_, v_a_5815_);
return v___x_5818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp___boxed(lean_object* v_cfg_5819_, lean_object* v_fvarId_5820_, lean_object* v_a_5821_, lean_object* v_a_5822_, lean_object* v_a_5823_, lean_object* v_a_5824_, lean_object* v_a_5825_, lean_object* v_a_5826_, lean_object* v_a_5827_, lean_object* v_a_5828_, lean_object* v_a_5829_){
_start:
{
lean_object* v_res_5830_; 
v_res_5830_ = l_Lean_Elab_Tactic_NormCast_normCastHyp(v_cfg_5819_, v_fvarId_5820_, v_a_5821_, v_a_5822_, v_a_5823_, v_a_5824_, v_a_5825_, v_a_5826_, v_a_5827_, v_a_5828_);
lean_dec(v_a_5828_);
lean_dec_ref(v_a_5827_);
lean_dec(v_a_5826_);
lean_dec_ref(v_a_5825_);
lean_dec(v_a_5824_);
lean_dec_ref(v_a_5823_);
lean_dec(v_a_5822_);
lean_dec_ref(v_a_5821_);
return v_res_5830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg(){
_start:
{
lean_object* v___x_5832_; lean_object* v___x_5833_; 
v___x_5832_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0);
v___x_5833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5833_, 0, v___x_5832_);
return v___x_5833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg___boxed(lean_object* v___y_5834_){
_start:
{
lean_object* v_res_5835_; 
v_res_5835_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg();
return v_res_5835_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0(lean_object* v_00_u03b1_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_, lean_object* v___y_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_, lean_object* v___y_5844_){
_start:
{
lean_object* v___x_5846_; 
v___x_5846_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg();
return v___x_5846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___boxed(lean_object* v_00_u03b1_5847_, lean_object* v___y_5848_, lean_object* v___y_5849_, lean_object* v___y_5850_, lean_object* v___y_5851_, lean_object* v___y_5852_, lean_object* v___y_5853_, lean_object* v___y_5854_, lean_object* v___y_5855_, lean_object* v___y_5856_){
_start:
{
lean_object* v_res_5857_; 
v_res_5857_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0(v_00_u03b1_5847_, v___y_5848_, v___y_5849_, v___y_5850_, v___y_5851_, v___y_5852_, v___y_5853_, v___y_5854_, v___y_5855_);
lean_dec(v___y_5855_);
lean_dec_ref(v___y_5854_);
lean_dec(v___y_5853_);
lean_dec_ref(v___y_5852_);
lean_dec(v___y_5851_);
lean_dec_ref(v___y_5850_);
lean_dec(v___y_5849_);
lean_dec_ref(v___y_5848_);
return v_res_5857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1(lean_object* v_a_5858_, lean_object* v_as_5859_, size_t v_i_5860_, size_t v_stop_5861_, lean_object* v_b_5862_, lean_object* v___y_5863_, lean_object* v___y_5864_, lean_object* v___y_5865_, lean_object* v___y_5866_, lean_object* v___y_5867_, lean_object* v___y_5868_, lean_object* v___y_5869_, lean_object* v___y_5870_){
_start:
{
uint8_t v___x_5872_; 
v___x_5872_ = lean_usize_dec_eq(v_i_5860_, v_stop_5861_);
if (v___x_5872_ == 0)
{
lean_object* v___x_5873_; lean_object* v___x_5874_; 
v___x_5873_ = lean_array_uget_borrowed(v_as_5859_, v_i_5860_);
lean_inc(v___x_5873_);
lean_inc_ref(v_a_5858_);
v___x_5874_ = l_Lean_Elab_Tactic_NormCast_normCastHyp(v_a_5858_, v___x_5873_, v___y_5863_, v___y_5864_, v___y_5865_, v___y_5866_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_);
if (lean_obj_tag(v___x_5874_) == 0)
{
lean_object* v_a_5875_; size_t v___x_5876_; size_t v___x_5877_; 
v_a_5875_ = lean_ctor_get(v___x_5874_, 0);
lean_inc(v_a_5875_);
lean_dec_ref(v___x_5874_);
v___x_5876_ = ((size_t)1ULL);
v___x_5877_ = lean_usize_add(v_i_5860_, v___x_5876_);
v_i_5860_ = v___x_5877_;
v_b_5862_ = v_a_5875_;
goto _start;
}
else
{
lean_dec_ref(v_a_5858_);
return v___x_5874_;
}
}
else
{
lean_object* v___x_5879_; 
lean_dec_ref(v_a_5858_);
v___x_5879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5879_, 0, v_b_5862_);
return v___x_5879_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1___boxed(lean_object* v_a_5880_, lean_object* v_as_5881_, lean_object* v_i_5882_, lean_object* v_stop_5883_, lean_object* v_b_5884_, lean_object* v___y_5885_, lean_object* v___y_5886_, lean_object* v___y_5887_, lean_object* v___y_5888_, lean_object* v___y_5889_, lean_object* v___y_5890_, lean_object* v___y_5891_, lean_object* v___y_5892_, lean_object* v___y_5893_){
_start:
{
size_t v_i_boxed_5894_; size_t v_stop_boxed_5895_; lean_object* v_res_5896_; 
v_i_boxed_5894_ = lean_unbox_usize(v_i_5882_);
lean_dec(v_i_5882_);
v_stop_boxed_5895_ = lean_unbox_usize(v_stop_5883_);
lean_dec(v_stop_5883_);
v_res_5896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1(v_a_5880_, v_as_5881_, v_i_boxed_5894_, v_stop_boxed_5895_, v_b_5884_, v___y_5885_, v___y_5886_, v___y_5887_, v___y_5888_, v___y_5889_, v___y_5890_, v___y_5891_, v___y_5892_);
lean_dec(v___y_5892_);
lean_dec_ref(v___y_5891_);
lean_dec(v___y_5890_);
lean_dec_ref(v___y_5889_);
lean_dec(v___y_5888_);
lean_dec_ref(v___y_5887_);
lean_dec(v___y_5886_);
lean_dec_ref(v___y_5885_);
lean_dec_ref(v_as_5881_);
return v_res_5896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lam__0(lean_object* v___y_5897_, lean_object* v_a_5898_, lean_object* v___x_5899_, lean_object* v___y_5900_, lean_object* v___y_5901_, lean_object* v___y_5902_, lean_object* v___y_5903_, lean_object* v___y_5904_, lean_object* v___y_5905_, lean_object* v___y_5906_, lean_object* v___y_5907_){
_start:
{
if (lean_obj_tag(v___y_5897_) == 0)
{
lean_object* v___x_5909_; 
lean_inc_ref(v_a_5898_);
v___x_5909_ = l_Lean_Elab_Tactic_NormCast_normCastTarget(v_a_5898_, v___y_5900_, v___y_5901_, v___y_5902_, v___y_5903_, v___y_5904_, v___y_5905_, v___y_5906_, v___y_5907_);
if (lean_obj_tag(v___x_5909_) == 0)
{
lean_object* v___x_5910_; 
lean_dec_ref(v___x_5909_);
v___x_5910_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_5901_, v___y_5904_, v___y_5905_, v___y_5906_, v___y_5907_);
if (lean_obj_tag(v___x_5910_) == 0)
{
lean_object* v_a_5911_; lean_object* v___x_5912_; 
v_a_5911_ = lean_ctor_get(v___x_5910_, 0);
lean_inc(v_a_5911_);
lean_dec_ref(v___x_5910_);
v___x_5912_ = l_Lean_MVarId_getNondepPropHyps(v_a_5911_, v___y_5904_, v___y_5905_, v___y_5906_, v___y_5907_);
if (lean_obj_tag(v___x_5912_) == 0)
{
lean_object* v_a_5913_; lean_object* v___x_5915_; uint8_t v_isShared_5916_; uint8_t v_isSharedCheck_5933_; 
v_a_5913_ = lean_ctor_get(v___x_5912_, 0);
v_isSharedCheck_5933_ = !lean_is_exclusive(v___x_5912_);
if (v_isSharedCheck_5933_ == 0)
{
v___x_5915_ = v___x_5912_;
v_isShared_5916_ = v_isSharedCheck_5933_;
goto v_resetjp_5914_;
}
else
{
lean_inc(v_a_5913_);
lean_dec(v___x_5912_);
v___x_5915_ = lean_box(0);
v_isShared_5916_ = v_isSharedCheck_5933_;
goto v_resetjp_5914_;
}
v_resetjp_5914_:
{
lean_object* v___x_5917_; lean_object* v___x_5918_; uint8_t v___x_5919_; 
v___x_5917_ = lean_array_get_size(v_a_5913_);
v___x_5918_ = lean_box(0);
v___x_5919_ = lean_nat_dec_lt(v___x_5899_, v___x_5917_);
if (v___x_5919_ == 0)
{
lean_object* v___x_5921_; 
lean_dec(v_a_5913_);
lean_dec_ref(v_a_5898_);
if (v_isShared_5916_ == 0)
{
lean_ctor_set(v___x_5915_, 0, v___x_5918_);
v___x_5921_ = v___x_5915_;
goto v_reusejp_5920_;
}
else
{
lean_object* v_reuseFailAlloc_5922_; 
v_reuseFailAlloc_5922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5922_, 0, v___x_5918_);
v___x_5921_ = v_reuseFailAlloc_5922_;
goto v_reusejp_5920_;
}
v_reusejp_5920_:
{
return v___x_5921_;
}
}
else
{
uint8_t v___x_5923_; 
v___x_5923_ = lean_nat_dec_le(v___x_5917_, v___x_5917_);
if (v___x_5923_ == 0)
{
if (v___x_5919_ == 0)
{
lean_object* v___x_5925_; 
lean_dec(v_a_5913_);
lean_dec_ref(v_a_5898_);
if (v_isShared_5916_ == 0)
{
lean_ctor_set(v___x_5915_, 0, v___x_5918_);
v___x_5925_ = v___x_5915_;
goto v_reusejp_5924_;
}
else
{
lean_object* v_reuseFailAlloc_5926_; 
v_reuseFailAlloc_5926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5926_, 0, v___x_5918_);
v___x_5925_ = v_reuseFailAlloc_5926_;
goto v_reusejp_5924_;
}
v_reusejp_5924_:
{
return v___x_5925_;
}
}
else
{
size_t v___x_5927_; size_t v___x_5928_; lean_object* v___x_5929_; 
lean_del_object(v___x_5915_);
v___x_5927_ = ((size_t)0ULL);
v___x_5928_ = lean_usize_of_nat(v___x_5917_);
v___x_5929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1(v_a_5898_, v_a_5913_, v___x_5927_, v___x_5928_, v___x_5918_, v___y_5900_, v___y_5901_, v___y_5902_, v___y_5903_, v___y_5904_, v___y_5905_, v___y_5906_, v___y_5907_);
lean_dec(v_a_5913_);
return v___x_5929_;
}
}
else
{
size_t v___x_5930_; size_t v___x_5931_; lean_object* v___x_5932_; 
lean_del_object(v___x_5915_);
v___x_5930_ = ((size_t)0ULL);
v___x_5931_ = lean_usize_of_nat(v___x_5917_);
v___x_5932_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1(v_a_5898_, v_a_5913_, v___x_5930_, v___x_5931_, v___x_5918_, v___y_5900_, v___y_5901_, v___y_5902_, v___y_5903_, v___y_5904_, v___y_5905_, v___y_5906_, v___y_5907_);
lean_dec(v_a_5913_);
return v___x_5932_;
}
}
}
}
else
{
lean_object* v_a_5934_; lean_object* v___x_5936_; uint8_t v_isShared_5937_; uint8_t v_isSharedCheck_5941_; 
lean_dec_ref(v_a_5898_);
v_a_5934_ = lean_ctor_get(v___x_5912_, 0);
v_isSharedCheck_5941_ = !lean_is_exclusive(v___x_5912_);
if (v_isSharedCheck_5941_ == 0)
{
v___x_5936_ = v___x_5912_;
v_isShared_5937_ = v_isSharedCheck_5941_;
goto v_resetjp_5935_;
}
else
{
lean_inc(v_a_5934_);
lean_dec(v___x_5912_);
v___x_5936_ = lean_box(0);
v_isShared_5937_ = v_isSharedCheck_5941_;
goto v_resetjp_5935_;
}
v_resetjp_5935_:
{
lean_object* v___x_5939_; 
if (v_isShared_5937_ == 0)
{
v___x_5939_ = v___x_5936_;
goto v_reusejp_5938_;
}
else
{
lean_object* v_reuseFailAlloc_5940_; 
v_reuseFailAlloc_5940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5940_, 0, v_a_5934_);
v___x_5939_ = v_reuseFailAlloc_5940_;
goto v_reusejp_5938_;
}
v_reusejp_5938_:
{
return v___x_5939_;
}
}
}
}
else
{
lean_object* v_a_5942_; lean_object* v___x_5944_; uint8_t v_isShared_5945_; uint8_t v_isSharedCheck_5949_; 
lean_dec_ref(v_a_5898_);
v_a_5942_ = lean_ctor_get(v___x_5910_, 0);
v_isSharedCheck_5949_ = !lean_is_exclusive(v___x_5910_);
if (v_isSharedCheck_5949_ == 0)
{
v___x_5944_ = v___x_5910_;
v_isShared_5945_ = v_isSharedCheck_5949_;
goto v_resetjp_5943_;
}
else
{
lean_inc(v_a_5942_);
lean_dec(v___x_5910_);
v___x_5944_ = lean_box(0);
v_isShared_5945_ = v_isSharedCheck_5949_;
goto v_resetjp_5943_;
}
v_resetjp_5943_:
{
lean_object* v___x_5947_; 
if (v_isShared_5945_ == 0)
{
v___x_5947_ = v___x_5944_;
goto v_reusejp_5946_;
}
else
{
lean_object* v_reuseFailAlloc_5948_; 
v_reuseFailAlloc_5948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5948_, 0, v_a_5942_);
v___x_5947_ = v_reuseFailAlloc_5948_;
goto v_reusejp_5946_;
}
v_reusejp_5946_:
{
return v___x_5947_;
}
}
}
}
else
{
lean_dec_ref(v_a_5898_);
return v___x_5909_;
}
}
else
{
lean_object* v_hypotheses_5950_; uint8_t v_type_5951_; lean_object* v___y_5953_; lean_object* v___y_5954_; lean_object* v___y_5955_; lean_object* v___y_5956_; lean_object* v___y_5957_; lean_object* v___y_5958_; lean_object* v___y_5959_; lean_object* v___y_5960_; 
v_hypotheses_5950_ = lean_ctor_get(v___y_5897_, 0);
lean_inc_ref(v_hypotheses_5950_);
v_type_5951_ = lean_ctor_get_uint8(v___y_5897_, sizeof(void*)*1);
lean_dec_ref(v___y_5897_);
if (v_type_5951_ == 0)
{
v___y_5953_ = v___y_5900_;
v___y_5954_ = v___y_5901_;
v___y_5955_ = v___y_5902_;
v___y_5956_ = v___y_5903_;
v___y_5957_ = v___y_5904_;
v___y_5958_ = v___y_5905_;
v___y_5959_ = v___y_5906_;
v___y_5960_ = v___y_5907_;
goto v___jp_5952_;
}
else
{
lean_object* v___x_5991_; 
lean_inc_ref(v_a_5898_);
v___x_5991_ = l_Lean_Elab_Tactic_NormCast_normCastTarget(v_a_5898_, v___y_5900_, v___y_5901_, v___y_5902_, v___y_5903_, v___y_5904_, v___y_5905_, v___y_5906_, v___y_5907_);
if (lean_obj_tag(v___x_5991_) == 0)
{
lean_dec_ref(v___x_5991_);
v___y_5953_ = v___y_5900_;
v___y_5954_ = v___y_5901_;
v___y_5955_ = v___y_5902_;
v___y_5956_ = v___y_5903_;
v___y_5957_ = v___y_5904_;
v___y_5958_ = v___y_5905_;
v___y_5959_ = v___y_5906_;
v___y_5960_ = v___y_5907_;
goto v___jp_5952_;
}
else
{
lean_dec_ref(v_hypotheses_5950_);
lean_dec_ref(v_a_5898_);
return v___x_5991_;
}
}
v___jp_5952_:
{
lean_object* v___x_5961_; 
v___x_5961_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_5950_, v___y_5953_, v___y_5954_, v___y_5955_, v___y_5956_, v___y_5957_, v___y_5958_, v___y_5959_, v___y_5960_);
if (lean_obj_tag(v___x_5961_) == 0)
{
lean_object* v_a_5962_; lean_object* v___x_5964_; uint8_t v_isShared_5965_; uint8_t v_isSharedCheck_5982_; 
v_a_5962_ = lean_ctor_get(v___x_5961_, 0);
v_isSharedCheck_5982_ = !lean_is_exclusive(v___x_5961_);
if (v_isSharedCheck_5982_ == 0)
{
v___x_5964_ = v___x_5961_;
v_isShared_5965_ = v_isSharedCheck_5982_;
goto v_resetjp_5963_;
}
else
{
lean_inc(v_a_5962_);
lean_dec(v___x_5961_);
v___x_5964_ = lean_box(0);
v_isShared_5965_ = v_isSharedCheck_5982_;
goto v_resetjp_5963_;
}
v_resetjp_5963_:
{
lean_object* v___x_5966_; lean_object* v___x_5967_; uint8_t v___x_5968_; 
v___x_5966_ = lean_array_get_size(v_a_5962_);
v___x_5967_ = lean_box(0);
v___x_5968_ = lean_nat_dec_lt(v___x_5899_, v___x_5966_);
if (v___x_5968_ == 0)
{
lean_object* v___x_5970_; 
lean_dec(v_a_5962_);
lean_dec_ref(v_a_5898_);
if (v_isShared_5965_ == 0)
{
lean_ctor_set(v___x_5964_, 0, v___x_5967_);
v___x_5970_ = v___x_5964_;
goto v_reusejp_5969_;
}
else
{
lean_object* v_reuseFailAlloc_5971_; 
v_reuseFailAlloc_5971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5971_, 0, v___x_5967_);
v___x_5970_ = v_reuseFailAlloc_5971_;
goto v_reusejp_5969_;
}
v_reusejp_5969_:
{
return v___x_5970_;
}
}
else
{
uint8_t v___x_5972_; 
v___x_5972_ = lean_nat_dec_le(v___x_5966_, v___x_5966_);
if (v___x_5972_ == 0)
{
if (v___x_5968_ == 0)
{
lean_object* v___x_5974_; 
lean_dec(v_a_5962_);
lean_dec_ref(v_a_5898_);
if (v_isShared_5965_ == 0)
{
lean_ctor_set(v___x_5964_, 0, v___x_5967_);
v___x_5974_ = v___x_5964_;
goto v_reusejp_5973_;
}
else
{
lean_object* v_reuseFailAlloc_5975_; 
v_reuseFailAlloc_5975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5975_, 0, v___x_5967_);
v___x_5974_ = v_reuseFailAlloc_5975_;
goto v_reusejp_5973_;
}
v_reusejp_5973_:
{
return v___x_5974_;
}
}
else
{
size_t v___x_5976_; size_t v___x_5977_; lean_object* v___x_5978_; 
lean_del_object(v___x_5964_);
v___x_5976_ = ((size_t)0ULL);
v___x_5977_ = lean_usize_of_nat(v___x_5966_);
v___x_5978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1(v_a_5898_, v_a_5962_, v___x_5976_, v___x_5977_, v___x_5967_, v___y_5953_, v___y_5954_, v___y_5955_, v___y_5956_, v___y_5957_, v___y_5958_, v___y_5959_, v___y_5960_);
lean_dec(v_a_5962_);
return v___x_5978_;
}
}
else
{
size_t v___x_5979_; size_t v___x_5980_; lean_object* v___x_5981_; 
lean_del_object(v___x_5964_);
v___x_5979_ = ((size_t)0ULL);
v___x_5980_ = lean_usize_of_nat(v___x_5966_);
v___x_5981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1(v_a_5898_, v_a_5962_, v___x_5979_, v___x_5980_, v___x_5967_, v___y_5953_, v___y_5954_, v___y_5955_, v___y_5956_, v___y_5957_, v___y_5958_, v___y_5959_, v___y_5960_);
lean_dec(v_a_5962_);
return v___x_5981_;
}
}
}
}
else
{
lean_object* v_a_5983_; lean_object* v___x_5985_; uint8_t v_isShared_5986_; uint8_t v_isSharedCheck_5990_; 
lean_dec_ref(v_a_5898_);
v_a_5983_ = lean_ctor_get(v___x_5961_, 0);
v_isSharedCheck_5990_ = !lean_is_exclusive(v___x_5961_);
if (v_isSharedCheck_5990_ == 0)
{
v___x_5985_ = v___x_5961_;
v_isShared_5986_ = v_isSharedCheck_5990_;
goto v_resetjp_5984_;
}
else
{
lean_inc(v_a_5983_);
lean_dec(v___x_5961_);
v___x_5985_ = lean_box(0);
v_isShared_5986_ = v_isSharedCheck_5990_;
goto v_resetjp_5984_;
}
v_resetjp_5984_:
{
lean_object* v___x_5988_; 
if (v_isShared_5986_ == 0)
{
v___x_5988_ = v___x_5985_;
goto v_reusejp_5987_;
}
else
{
lean_object* v_reuseFailAlloc_5989_; 
v_reuseFailAlloc_5989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5989_, 0, v_a_5983_);
v___x_5988_ = v_reuseFailAlloc_5989_;
goto v_reusejp_5987_;
}
v_reusejp_5987_:
{
return v___x_5988_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lam__0___boxed(lean_object* v___y_5992_, lean_object* v_a_5993_, lean_object* v___x_5994_, lean_object* v___y_5995_, lean_object* v___y_5996_, lean_object* v___y_5997_, lean_object* v___y_5998_, lean_object* v___y_5999_, lean_object* v___y_6000_, lean_object* v___y_6001_, lean_object* v___y_6002_, lean_object* v___y_6003_){
_start:
{
lean_object* v_res_6004_; 
v_res_6004_ = l_Lean_Elab_Tactic_NormCast_evalNormCast0___lam__0(v___y_5992_, v_a_5993_, v___x_5994_, v___y_5995_, v___y_5996_, v___y_5997_, v___y_5998_, v___y_5999_, v___y_6000_, v___y_6001_, v___y_6002_);
lean_dec(v___y_6002_);
lean_dec_ref(v___y_6001_);
lean_dec(v___y_6000_);
lean_dec_ref(v___y_5999_);
lean_dec(v___y_5998_);
lean_dec_ref(v___y_5997_);
lean_dec(v___y_5996_);
lean_dec_ref(v___y_5995_);
lean_dec(v___x_5994_);
return v_res_6004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0(lean_object* v_stx_6014_, lean_object* v_a_6015_, lean_object* v_a_6016_, lean_object* v_a_6017_, lean_object* v_a_6018_, lean_object* v_a_6019_, lean_object* v_a_6020_, lean_object* v_a_6021_, lean_object* v_a_6022_){
_start:
{
lean_object* v___x_6024_; uint8_t v___x_6025_; 
v___x_6024_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__2));
lean_inc(v_stx_6014_);
v___x_6025_ = l_Lean_Syntax_isOfKind(v_stx_6014_, v___x_6024_);
if (v___x_6025_ == 0)
{
lean_object* v___x_6026_; 
lean_dec(v_stx_6014_);
v___x_6026_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg();
return v___x_6026_;
}
else
{
lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___y_6031_; lean_object* v___y_6032_; lean_object* v___y_6033_; lean_object* v___y_6034_; lean_object* v___y_6035_; lean_object* v___y_6036_; lean_object* v___y_6037_; lean_object* v___y_6038_; lean_object* v___y_6039_; lean_object* v___x_6052_; lean_object* v___x_6053_; uint8_t v___x_6054_; 
v___x_6027_ = lean_unsigned_to_nat(0u);
v___x_6028_ = lean_unsigned_to_nat(1u);
v___x_6029_ = l_Lean_Syntax_getArg(v_stx_6014_, v___x_6028_);
v___x_6052_ = lean_unsigned_to_nat(2u);
v___x_6053_ = l_Lean_Syntax_getArg(v_stx_6014_, v___x_6052_);
lean_dec(v_stx_6014_);
v___x_6054_ = l_Lean_Syntax_isNone(v___x_6053_);
if (v___x_6054_ == 0)
{
uint8_t v___x_6055_; 
lean_inc(v___x_6053_);
v___x_6055_ = l_Lean_Syntax_matchesNull(v___x_6053_, v___x_6028_);
if (v___x_6055_ == 0)
{
lean_object* v___x_6056_; 
lean_dec(v___x_6053_);
lean_dec(v___x_6029_);
v___x_6056_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg();
return v___x_6056_;
}
else
{
lean_object* v_loc_x3f_6057_; lean_object* v___x_6058_; 
v_loc_x3f_6057_ = l_Lean_Syntax_getArg(v___x_6053_, v___x_6027_);
lean_dec(v___x_6053_);
v___x_6058_ = l_Lean_Elab_Tactic_expandLocation(v_loc_x3f_6057_);
lean_dec(v_loc_x3f_6057_);
v___y_6031_ = v_a_6017_;
v___y_6032_ = v_a_6020_;
v___y_6033_ = v_a_6021_;
v___y_6034_ = v_a_6018_;
v___y_6035_ = v_a_6019_;
v___y_6036_ = v_a_6016_;
v___y_6037_ = v_a_6015_;
v___y_6038_ = v_a_6022_;
v___y_6039_ = v___x_6058_;
goto v___jp_6030_;
}
}
else
{
lean_object* v___x_6059_; lean_object* v___x_6060_; 
lean_dec(v___x_6053_);
v___x_6059_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__3));
v___x_6060_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_6060_, 0, v___x_6059_);
lean_ctor_set_uint8(v___x_6060_, sizeof(void*)*1, v___x_6025_);
v___y_6031_ = v_a_6017_;
v___y_6032_ = v_a_6020_;
v___y_6033_ = v_a_6021_;
v___y_6034_ = v_a_6018_;
v___y_6035_ = v_a_6019_;
v___y_6036_ = v_a_6016_;
v___y_6037_ = v_a_6015_;
v___y_6038_ = v_a_6022_;
v___y_6039_ = v___x_6060_;
goto v___jp_6030_;
}
v___jp_6030_:
{
lean_object* v___x_6040_; 
v___x_6040_ = l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg(v___x_6029_, v___y_6037_, v___y_6031_, v___y_6034_, v___y_6035_, v___y_6032_, v___y_6033_, v___y_6038_);
if (lean_obj_tag(v___x_6040_) == 0)
{
lean_object* v_a_6041_; lean_object* v___y_6042_; lean_object* v___x_6043_; 
v_a_6041_ = lean_ctor_get(v___x_6040_, 0);
lean_inc(v_a_6041_);
lean_dec_ref(v___x_6040_);
v___y_6042_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___lam__0___boxed), 12, 3);
lean_closure_set(v___y_6042_, 0, v___y_6039_);
lean_closure_set(v___y_6042_, 1, v_a_6041_);
lean_closure_set(v___y_6042_, 2, v___x_6027_);
v___x_6043_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_6042_, v___y_6037_, v___y_6036_, v___y_6031_, v___y_6034_, v___y_6035_, v___y_6032_, v___y_6033_, v___y_6038_);
return v___x_6043_;
}
else
{
lean_object* v_a_6044_; lean_object* v___x_6046_; uint8_t v_isShared_6047_; uint8_t v_isSharedCheck_6051_; 
lean_dec(v___y_6039_);
v_a_6044_ = lean_ctor_get(v___x_6040_, 0);
v_isSharedCheck_6051_ = !lean_is_exclusive(v___x_6040_);
if (v_isSharedCheck_6051_ == 0)
{
v___x_6046_ = v___x_6040_;
v_isShared_6047_ = v_isSharedCheck_6051_;
goto v_resetjp_6045_;
}
else
{
lean_inc(v_a_6044_);
lean_dec(v___x_6040_);
v___x_6046_ = lean_box(0);
v_isShared_6047_ = v_isSharedCheck_6051_;
goto v_resetjp_6045_;
}
v_resetjp_6045_:
{
lean_object* v___x_6049_; 
if (v_isShared_6047_ == 0)
{
v___x_6049_ = v___x_6046_;
goto v_reusejp_6048_;
}
else
{
lean_object* v_reuseFailAlloc_6050_; 
v_reuseFailAlloc_6050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6050_, 0, v_a_6044_);
v___x_6049_ = v_reuseFailAlloc_6050_;
goto v_reusejp_6048_;
}
v_reusejp_6048_:
{
return v___x_6049_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___boxed(lean_object* v_stx_6061_, lean_object* v_a_6062_, lean_object* v_a_6063_, lean_object* v_a_6064_, lean_object* v_a_6065_, lean_object* v_a_6066_, lean_object* v_a_6067_, lean_object* v_a_6068_, lean_object* v_a_6069_, lean_object* v_a_6070_){
_start:
{
lean_object* v_res_6071_; 
v_res_6071_ = l_Lean_Elab_Tactic_NormCast_evalNormCast0(v_stx_6061_, v_a_6062_, v_a_6063_, v_a_6064_, v_a_6065_, v_a_6066_, v_a_6067_, v_a_6068_, v_a_6069_);
lean_dec(v_a_6069_);
lean_dec_ref(v_a_6068_);
lean_dec(v_a_6067_);
lean_dec_ref(v_a_6066_);
lean_dec(v_a_6065_);
lean_dec_ref(v_a_6064_);
lean_dec(v_a_6063_);
lean_dec_ref(v_a_6062_);
return v_res_6071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1(){
_start:
{
lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; 
v___x_6080_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6081_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__2));
v___x_6082_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1));
v___x_6083_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___boxed), 10, 0);
v___x_6084_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6080_, v___x_6081_, v___x_6082_, v___x_6083_);
return v___x_6084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___boxed(lean_object* v_a_6085_){
_start:
{
lean_object* v_res_6086_; 
v_res_6086_ = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1();
return v_res_6086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3(){
_start:
{
lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; 
v___x_6113_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1));
v___x_6114_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__6));
v___x_6115_ = l_Lean_addBuiltinDeclarationRanges(v___x_6113_, v___x_6114_);
return v___x_6115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___boxed(lean_object* v_a_6116_){
_start:
{
lean_object* v_res_6117_; 
v_res_6117_ = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3();
return v_res_6117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___lam__0(lean_object* v___y_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_, lean_object* v___y_6122_, lean_object* v___y_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_){
_start:
{
lean_object* v___x_6127_; 
v___x_6127_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_6119_, v___y_6122_, v___y_6123_, v___y_6124_, v___y_6125_);
if (lean_obj_tag(v___x_6127_) == 0)
{
lean_object* v_a_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; 
v_a_6128_ = lean_ctor_get(v___x_6127_, 0);
lean_inc(v_a_6128_);
lean_dec_ref(v___x_6127_);
v___x_6129_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__10));
v___x_6130_ = l_Lean_Elab_Tactic_NormCast_derive(v_a_6128_, v___x_6129_, v___y_6122_, v___y_6123_, v___y_6124_, v___y_6125_);
if (lean_obj_tag(v___x_6130_) == 0)
{
lean_object* v_a_6131_; lean_object* v___x_6132_; 
v_a_6131_ = lean_ctor_get(v___x_6130_, 0);
lean_inc(v_a_6131_);
lean_dec_ref(v___x_6130_);
v___x_6132_ = l_Lean_Elab_Tactic_Conv_applySimpResult(v_a_6131_, v___y_6118_, v___y_6119_, v___y_6120_, v___y_6121_, v___y_6122_, v___y_6123_, v___y_6124_, v___y_6125_);
return v___x_6132_;
}
else
{
lean_object* v_a_6133_; lean_object* v___x_6135_; uint8_t v_isShared_6136_; uint8_t v_isSharedCheck_6140_; 
v_a_6133_ = lean_ctor_get(v___x_6130_, 0);
v_isSharedCheck_6140_ = !lean_is_exclusive(v___x_6130_);
if (v_isSharedCheck_6140_ == 0)
{
v___x_6135_ = v___x_6130_;
v_isShared_6136_ = v_isSharedCheck_6140_;
goto v_resetjp_6134_;
}
else
{
lean_inc(v_a_6133_);
lean_dec(v___x_6130_);
v___x_6135_ = lean_box(0);
v_isShared_6136_ = v_isSharedCheck_6140_;
goto v_resetjp_6134_;
}
v_resetjp_6134_:
{
lean_object* v___x_6138_; 
if (v_isShared_6136_ == 0)
{
v___x_6138_ = v___x_6135_;
goto v_reusejp_6137_;
}
else
{
lean_object* v_reuseFailAlloc_6139_; 
v_reuseFailAlloc_6139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6139_, 0, v_a_6133_);
v___x_6138_ = v_reuseFailAlloc_6139_;
goto v_reusejp_6137_;
}
v_reusejp_6137_:
{
return v___x_6138_;
}
}
}
}
else
{
lean_object* v_a_6141_; lean_object* v___x_6143_; uint8_t v_isShared_6144_; uint8_t v_isSharedCheck_6148_; 
v_a_6141_ = lean_ctor_get(v___x_6127_, 0);
v_isSharedCheck_6148_ = !lean_is_exclusive(v___x_6127_);
if (v_isSharedCheck_6148_ == 0)
{
v___x_6143_ = v___x_6127_;
v_isShared_6144_ = v_isSharedCheck_6148_;
goto v_resetjp_6142_;
}
else
{
lean_inc(v_a_6141_);
lean_dec(v___x_6127_);
v___x_6143_ = lean_box(0);
v_isShared_6144_ = v_isSharedCheck_6148_;
goto v_resetjp_6142_;
}
v_resetjp_6142_:
{
lean_object* v___x_6146_; 
if (v_isShared_6144_ == 0)
{
v___x_6146_ = v___x_6143_;
goto v_reusejp_6145_;
}
else
{
lean_object* v_reuseFailAlloc_6147_; 
v_reuseFailAlloc_6147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6147_, 0, v_a_6141_);
v___x_6146_ = v_reuseFailAlloc_6147_;
goto v_reusejp_6145_;
}
v_reusejp_6145_:
{
return v___x_6146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___lam__0___boxed(lean_object* v___y_6149_, lean_object* v___y_6150_, lean_object* v___y_6151_, lean_object* v___y_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_, lean_object* v___y_6157_){
_start:
{
lean_object* v_res_6158_; 
v_res_6158_ = l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___lam__0(v___y_6149_, v___y_6150_, v___y_6151_, v___y_6152_, v___y_6153_, v___y_6154_, v___y_6155_, v___y_6156_);
lean_dec(v___y_6156_);
lean_dec_ref(v___y_6155_);
lean_dec(v___y_6154_);
lean_dec_ref(v___y_6153_);
lean_dec(v___y_6152_);
lean_dec_ref(v___y_6151_);
lean_dec(v___y_6150_);
lean_dec_ref(v___y_6149_);
return v_res_6158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg(lean_object* v_a_6160_, lean_object* v_a_6161_, lean_object* v_a_6162_, lean_object* v_a_6163_, lean_object* v_a_6164_, lean_object* v_a_6165_, lean_object* v_a_6166_, lean_object* v_a_6167_){
_start:
{
lean_object* v___f_6169_; lean_object* v___x_6170_; 
v___f_6169_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___closed__0));
v___x_6170_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_6169_, v_a_6160_, v_a_6161_, v_a_6162_, v_a_6163_, v_a_6164_, v_a_6165_, v_a_6166_, v_a_6167_);
return v___x_6170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___boxed(lean_object* v_a_6171_, lean_object* v_a_6172_, lean_object* v_a_6173_, lean_object* v_a_6174_, lean_object* v_a_6175_, lean_object* v_a_6176_, lean_object* v_a_6177_, lean_object* v_a_6178_, lean_object* v_a_6179_){
_start:
{
lean_object* v_res_6180_; 
v_res_6180_ = l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg(v_a_6171_, v_a_6172_, v_a_6173_, v_a_6174_, v_a_6175_, v_a_6176_, v_a_6177_, v_a_6178_);
lean_dec(v_a_6178_);
lean_dec_ref(v_a_6177_);
lean_dec(v_a_6176_);
lean_dec_ref(v_a_6175_);
lean_dec(v_a_6174_);
lean_dec_ref(v_a_6173_);
lean_dec(v_a_6172_);
lean_dec_ref(v_a_6171_);
return v_res_6180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast(lean_object* v_x_6181_, lean_object* v_a_6182_, lean_object* v_a_6183_, lean_object* v_a_6184_, lean_object* v_a_6185_, lean_object* v_a_6186_, lean_object* v_a_6187_, lean_object* v_a_6188_, lean_object* v_a_6189_){
_start:
{
lean_object* v___x_6191_; 
v___x_6191_ = l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg(v_a_6182_, v_a_6183_, v_a_6184_, v_a_6185_, v_a_6186_, v_a_6187_, v_a_6188_, v_a_6189_);
return v___x_6191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___boxed(lean_object* v_x_6192_, lean_object* v_a_6193_, lean_object* v_a_6194_, lean_object* v_a_6195_, lean_object* v_a_6196_, lean_object* v_a_6197_, lean_object* v_a_6198_, lean_object* v_a_6199_, lean_object* v_a_6200_, lean_object* v_a_6201_){
_start:
{
lean_object* v_res_6202_; 
v_res_6202_ = l_Lean_Elab_Tactic_NormCast_evalConvNormCast(v_x_6192_, v_a_6193_, v_a_6194_, v_a_6195_, v_a_6196_, v_a_6197_, v_a_6198_, v_a_6199_, v_a_6200_);
lean_dec(v_a_6200_);
lean_dec_ref(v_a_6199_);
lean_dec(v_a_6198_);
lean_dec_ref(v_a_6197_);
lean_dec(v_a_6196_);
lean_dec_ref(v_a_6195_);
lean_dec(v_a_6194_);
lean_dec_ref(v_a_6193_);
lean_dec(v_x_6192_);
return v_res_6202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1(){
_start:
{
lean_object* v___x_6219_; lean_object* v___x_6220_; lean_object* v___x_6221_; lean_object* v___x_6222_; lean_object* v___x_6223_; 
v___x_6219_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6220_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2));
v___x_6221_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4));
v___x_6222_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalConvNormCast___boxed), 10, 0);
v___x_6223_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6219_, v___x_6220_, v___x_6221_, v___x_6222_);
return v___x_6223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___boxed(lean_object* v_a_6224_){
_start:
{
lean_object* v_res_6225_; 
v_res_6225_ = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1();
return v_res_6225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3(){
_start:
{
lean_object* v___x_6252_; lean_object* v___x_6253_; lean_object* v___x_6254_; 
v___x_6252_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4));
v___x_6253_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__6));
v___x_6254_ = l_Lean_addBuiltinDeclarationRanges(v___x_6252_, v___x_6253_);
return v___x_6254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___boxed(lean_object* v_a_6255_){
_start:
{
lean_object* v_res_6256_; 
v_res_6256_ = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3();
return v_res_6256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0(lean_object* v_stx_6257_, lean_object* v___x_6258_, lean_object* v_simprocs_6259_, lean_object* v_discharge_x3f_6260_, lean_object* v___y_6261_, lean_object* v___y_6262_, lean_object* v___y_6263_, lean_object* v___y_6264_, lean_object* v___y_6265_, lean_object* v___y_6266_, lean_object* v___y_6267_, lean_object* v___y_6268_){
_start:
{
lean_object* v___x_6270_; lean_object* v___x_6271_; lean_object* v___x_6272_; lean_object* v___x_6273_; 
v___x_6270_ = lean_unsigned_to_nat(5u);
v___x_6271_ = l_Lean_Syntax_getArg(v_stx_6257_, v___x_6270_);
v___x_6272_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_6271_);
lean_dec(v___x_6271_);
v___x_6273_ = l_Lean_Elab_Tactic_simpLocation(v___x_6258_, v_simprocs_6259_, v_discharge_x3f_6260_, v___x_6272_, v___y_6261_, v___y_6262_, v___y_6263_, v___y_6264_, v___y_6265_, v___y_6266_, v___y_6267_, v___y_6268_);
if (lean_obj_tag(v___x_6273_) == 0)
{
lean_object* v___x_6275_; uint8_t v_isShared_6276_; uint8_t v_isSharedCheck_6281_; 
v_isSharedCheck_6281_ = !lean_is_exclusive(v___x_6273_);
if (v_isSharedCheck_6281_ == 0)
{
lean_object* v_unused_6282_; 
v_unused_6282_ = lean_ctor_get(v___x_6273_, 0);
lean_dec(v_unused_6282_);
v___x_6275_ = v___x_6273_;
v_isShared_6276_ = v_isSharedCheck_6281_;
goto v_resetjp_6274_;
}
else
{
lean_dec(v___x_6273_);
v___x_6275_ = lean_box(0);
v_isShared_6276_ = v_isSharedCheck_6281_;
goto v_resetjp_6274_;
}
v_resetjp_6274_:
{
lean_object* v___x_6277_; lean_object* v___x_6279_; 
v___x_6277_ = lean_box(0);
if (v_isShared_6276_ == 0)
{
lean_ctor_set(v___x_6275_, 0, v___x_6277_);
v___x_6279_ = v___x_6275_;
goto v_reusejp_6278_;
}
else
{
lean_object* v_reuseFailAlloc_6280_; 
v_reuseFailAlloc_6280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6280_, 0, v___x_6277_);
v___x_6279_ = v_reuseFailAlloc_6280_;
goto v_reusejp_6278_;
}
v_reusejp_6278_:
{
return v___x_6279_;
}
}
}
else
{
lean_object* v_a_6283_; lean_object* v___x_6285_; uint8_t v_isShared_6286_; uint8_t v_isSharedCheck_6290_; 
v_a_6283_ = lean_ctor_get(v___x_6273_, 0);
v_isSharedCheck_6290_ = !lean_is_exclusive(v___x_6273_);
if (v_isSharedCheck_6290_ == 0)
{
v___x_6285_ = v___x_6273_;
v_isShared_6286_ = v_isSharedCheck_6290_;
goto v_resetjp_6284_;
}
else
{
lean_inc(v_a_6283_);
lean_dec(v___x_6273_);
v___x_6285_ = lean_box(0);
v_isShared_6286_ = v_isSharedCheck_6290_;
goto v_resetjp_6284_;
}
v_resetjp_6284_:
{
lean_object* v___x_6288_; 
if (v_isShared_6286_ == 0)
{
v___x_6288_ = v___x_6285_;
goto v_reusejp_6287_;
}
else
{
lean_object* v_reuseFailAlloc_6289_; 
v_reuseFailAlloc_6289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6289_, 0, v_a_6283_);
v___x_6288_ = v_reuseFailAlloc_6289_;
goto v_reusejp_6287_;
}
v_reusejp_6287_:
{
return v___x_6288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0___boxed(lean_object* v_stx_6291_, lean_object* v___x_6292_, lean_object* v_simprocs_6293_, lean_object* v_discharge_x3f_6294_, lean_object* v___y_6295_, lean_object* v___y_6296_, lean_object* v___y_6297_, lean_object* v___y_6298_, lean_object* v___y_6299_, lean_object* v___y_6300_, lean_object* v___y_6301_, lean_object* v___y_6302_, lean_object* v___y_6303_){
_start:
{
lean_object* v_res_6304_; 
v_res_6304_ = l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0(v_stx_6291_, v___x_6292_, v_simprocs_6293_, v_discharge_x3f_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_, v___y_6299_, v___y_6300_, v___y_6301_, v___y_6302_);
lean_dec(v___y_6302_);
lean_dec_ref(v___y_6301_);
lean_dec(v___y_6300_);
lean_dec_ref(v___y_6299_);
lean_dec(v___y_6298_);
lean_dec_ref(v___y_6297_);
lean_dec(v___y_6296_);
lean_dec_ref(v___y_6295_);
lean_dec(v_stx_6291_);
return v_res_6304_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__0(void){
_start:
{
lean_object* v___x_6305_; lean_object* v___x_6306_; 
v___x_6305_ = l_Lean_Meta_NormCast_pushCastExt;
v___x_6306_ = lean_alloc_closure((void*)(l_Lean_Meta_SimpExtension_getTheorems___boxed), 4, 1);
lean_closure_set(v___x_6306_, 0, v___x_6305_);
return v___x_6306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast(lean_object* v_stx_6307_, lean_object* v_a_6308_, lean_object* v_a_6309_, lean_object* v_a_6310_, lean_object* v_a_6311_, lean_object* v_a_6312_, lean_object* v_a_6313_, lean_object* v_a_6314_, lean_object* v_a_6315_){
_start:
{
uint8_t v___x_6317_; uint8_t v___x_6318_; lean_object* v___x_6319_; lean_object* v___x_6320_; lean_object* v___x_6321_; lean_object* v___x_6322_; lean_object* v___x_6323_; lean_object* v___x_6324_; 
v___x_6317_ = 0;
v___x_6318_ = 0;
v___x_6319_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__0, &l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__0_once, _init_l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__0);
v___x_6320_ = lean_box(v___x_6317_);
v___x_6321_ = lean_box(v___x_6318_);
v___x_6322_ = lean_box(v___x_6317_);
lean_inc(v_stx_6307_);
v___x_6323_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_6323_, 0, v_stx_6307_);
lean_closure_set(v___x_6323_, 1, v___x_6320_);
lean_closure_set(v___x_6323_, 2, v___x_6321_);
lean_closure_set(v___x_6323_, 3, v___x_6322_);
lean_closure_set(v___x_6323_, 4, v___x_6319_);
v___x_6324_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_6323_, v_a_6308_, v_a_6309_, v_a_6310_, v_a_6311_, v_a_6312_, v_a_6313_, v_a_6314_, v_a_6315_);
if (lean_obj_tag(v___x_6324_) == 0)
{
lean_object* v_a_6325_; lean_object* v_ctx_6326_; lean_object* v_simprocs_6327_; lean_object* v_dischargeWrapper_6328_; lean_object* v___x_6329_; lean_object* v___f_6330_; lean_object* v___x_6331_; 
v_a_6325_ = lean_ctor_get(v___x_6324_, 0);
lean_inc(v_a_6325_);
lean_dec_ref(v___x_6324_);
v_ctx_6326_ = lean_ctor_get(v_a_6325_, 0);
lean_inc_ref(v_ctx_6326_);
v_simprocs_6327_ = lean_ctor_get(v_a_6325_, 1);
lean_inc_ref(v_simprocs_6327_);
v_dischargeWrapper_6328_ = lean_ctor_get(v_a_6325_, 2);
lean_inc(v_dischargeWrapper_6328_);
lean_dec(v_a_6325_);
v___x_6329_ = l_Lean_Meta_Simp_Context_setFailIfUnchanged(v_ctx_6326_, v___x_6317_);
v___f_6330_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0___boxed), 13, 3);
lean_closure_set(v___f_6330_, 0, v_stx_6307_);
lean_closure_set(v___f_6330_, 1, v___x_6329_);
lean_closure_set(v___f_6330_, 2, v_simprocs_6327_);
v___x_6331_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v_dischargeWrapper_6328_, v___f_6330_, v_a_6308_, v_a_6309_, v_a_6310_, v_a_6311_, v_a_6312_, v_a_6313_, v_a_6314_, v_a_6315_);
lean_dec(v_dischargeWrapper_6328_);
return v___x_6331_;
}
else
{
lean_object* v_a_6332_; lean_object* v___x_6334_; uint8_t v_isShared_6335_; uint8_t v_isSharedCheck_6339_; 
lean_dec(v_stx_6307_);
v_a_6332_ = lean_ctor_get(v___x_6324_, 0);
v_isSharedCheck_6339_ = !lean_is_exclusive(v___x_6324_);
if (v_isSharedCheck_6339_ == 0)
{
v___x_6334_ = v___x_6324_;
v_isShared_6335_ = v_isSharedCheck_6339_;
goto v_resetjp_6333_;
}
else
{
lean_inc(v_a_6332_);
lean_dec(v___x_6324_);
v___x_6334_ = lean_box(0);
v_isShared_6335_ = v_isSharedCheck_6339_;
goto v_resetjp_6333_;
}
v_resetjp_6333_:
{
lean_object* v___x_6337_; 
if (v_isShared_6335_ == 0)
{
v___x_6337_ = v___x_6334_;
goto v_reusejp_6336_;
}
else
{
lean_object* v_reuseFailAlloc_6338_; 
v_reuseFailAlloc_6338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6338_, 0, v_a_6332_);
v___x_6337_ = v_reuseFailAlloc_6338_;
goto v_reusejp_6336_;
}
v_reusejp_6336_:
{
return v___x_6337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___boxed(lean_object* v_stx_6340_, lean_object* v_a_6341_, lean_object* v_a_6342_, lean_object* v_a_6343_, lean_object* v_a_6344_, lean_object* v_a_6345_, lean_object* v_a_6346_, lean_object* v_a_6347_, lean_object* v_a_6348_, lean_object* v_a_6349_){
_start:
{
lean_object* v_res_6350_; 
v_res_6350_ = l_Lean_Elab_Tactic_NormCast_evalPushCast(v_stx_6340_, v_a_6341_, v_a_6342_, v_a_6343_, v_a_6344_, v_a_6345_, v_a_6346_, v_a_6347_, v_a_6348_);
lean_dec(v_a_6348_);
lean_dec_ref(v_a_6347_);
lean_dec(v_a_6346_);
lean_dec_ref(v_a_6345_);
lean_dec(v_a_6344_);
lean_dec_ref(v_a_6343_);
lean_dec(v_a_6342_);
lean_dec_ref(v_a_6341_);
return v_res_6350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1(){
_start:
{
lean_object* v___x_6365_; lean_object* v___x_6366_; lean_object* v___x_6367_; lean_object* v___x_6368_; lean_object* v___x_6369_; 
v___x_6365_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6366_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1));
v___x_6367_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3));
v___x_6368_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalPushCast___boxed), 10, 0);
v___x_6369_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6365_, v___x_6366_, v___x_6367_, v___x_6368_);
return v___x_6369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___boxed(lean_object* v_a_6370_){
_start:
{
lean_object* v_res_6371_; 
v_res_6371_ = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1();
return v_res_6371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3(){
_start:
{
lean_object* v___x_6398_; lean_object* v___x_6399_; lean_object* v___x_6400_; 
v___x_6398_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3));
v___x_6399_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__6));
v___x_6400_ = l_Lean_addBuiltinDeclarationRanges(v___x_6398_, v___x_6399_);
return v___x_6400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___boxed(lean_object* v_a_6401_){
_start:
{
lean_object* v_res_6402_; 
v_res_6402_ = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3();
return v_res_6402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg(){
_start:
{
lean_object* v___x_6404_; lean_object* v___x_6405_; 
v___x_6404_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0);
v___x_6405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6405_, 0, v___x_6404_);
return v___x_6405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg___boxed(lean_object* v___y_6406_){
_start:
{
lean_object* v_res_6407_; 
v_res_6407_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg();
return v_res_6407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0(lean_object* v_00_u03b1_6408_, lean_object* v___y_6409_, lean_object* v___y_6410_){
_start:
{
lean_object* v___x_6412_; 
v___x_6412_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg();
return v___x_6412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___boxed(lean_object* v_00_u03b1_6413_, lean_object* v___y_6414_, lean_object* v___y_6415_, lean_object* v___y_6416_){
_start:
{
lean_object* v_res_6417_; 
v_res_6417_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0(v_00_u03b1_6413_, v___y_6414_, v___y_6415_);
lean_dec(v___y_6415_);
lean_dec_ref(v___y_6414_);
return v_res_6417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___lam__0(lean_object* v___x_6418_, lean_object* v___x_6419_, lean_object* v___x_6420_, lean_object* v___y_6421_, lean_object* v___y_6422_){
_start:
{
lean_object* v___x_6424_; lean_object* v___x_6425_; 
v___x_6424_ = lean_st_mk_ref(v___x_6418_);
v___x_6425_ = l_Lean_realizeGlobalConstNoOverload(v___x_6419_, v___y_6421_, v___y_6422_);
if (lean_obj_tag(v___x_6425_) == 0)
{
lean_object* v_a_6426_; uint8_t v___x_6427_; lean_object* v___x_6428_; lean_object* v___x_6429_; 
v_a_6426_ = lean_ctor_get(v___x_6425_, 0);
lean_inc(v_a_6426_);
lean_dec_ref(v___x_6425_);
v___x_6427_ = 0;
v___x_6428_ = lean_unsigned_to_nat(1000u);
v___x_6429_ = l_Lean_Meta_NormCast_addElim(v_a_6426_, v___x_6427_, v___x_6428_, v___x_6420_, v___x_6424_, v___y_6421_, v___y_6422_);
if (lean_obj_tag(v___x_6429_) == 0)
{
lean_object* v_a_6430_; lean_object* v___x_6432_; uint8_t v_isShared_6433_; uint8_t v_isSharedCheck_6438_; 
v_a_6430_ = lean_ctor_get(v___x_6429_, 0);
v_isSharedCheck_6438_ = !lean_is_exclusive(v___x_6429_);
if (v_isSharedCheck_6438_ == 0)
{
v___x_6432_ = v___x_6429_;
v_isShared_6433_ = v_isSharedCheck_6438_;
goto v_resetjp_6431_;
}
else
{
lean_inc(v_a_6430_);
lean_dec(v___x_6429_);
v___x_6432_ = lean_box(0);
v_isShared_6433_ = v_isSharedCheck_6438_;
goto v_resetjp_6431_;
}
v_resetjp_6431_:
{
lean_object* v___x_6434_; lean_object* v___x_6436_; 
v___x_6434_ = lean_st_ref_get(v___x_6424_);
lean_dec(v___x_6424_);
lean_dec(v___x_6434_);
if (v_isShared_6433_ == 0)
{
v___x_6436_ = v___x_6432_;
goto v_reusejp_6435_;
}
else
{
lean_object* v_reuseFailAlloc_6437_; 
v_reuseFailAlloc_6437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6437_, 0, v_a_6430_);
v___x_6436_ = v_reuseFailAlloc_6437_;
goto v_reusejp_6435_;
}
v_reusejp_6435_:
{
return v___x_6436_;
}
}
}
else
{
lean_dec(v___x_6424_);
return v___x_6429_;
}
}
else
{
lean_object* v_a_6439_; lean_object* v___x_6441_; uint8_t v_isShared_6442_; uint8_t v_isSharedCheck_6446_; 
lean_dec(v___x_6424_);
v_a_6439_ = lean_ctor_get(v___x_6425_, 0);
v_isSharedCheck_6446_ = !lean_is_exclusive(v___x_6425_);
if (v_isSharedCheck_6446_ == 0)
{
v___x_6441_ = v___x_6425_;
v_isShared_6442_ = v_isSharedCheck_6446_;
goto v_resetjp_6440_;
}
else
{
lean_inc(v_a_6439_);
lean_dec(v___x_6425_);
v___x_6441_ = lean_box(0);
v_isShared_6442_ = v_isSharedCheck_6446_;
goto v_resetjp_6440_;
}
v_resetjp_6440_:
{
lean_object* v___x_6444_; 
if (v_isShared_6442_ == 0)
{
v___x_6444_ = v___x_6441_;
goto v_reusejp_6443_;
}
else
{
lean_object* v_reuseFailAlloc_6445_; 
v_reuseFailAlloc_6445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6445_, 0, v_a_6439_);
v___x_6444_ = v_reuseFailAlloc_6445_;
goto v_reusejp_6443_;
}
v_reusejp_6443_:
{
return v___x_6444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___lam__0___boxed(lean_object* v___x_6447_, lean_object* v___x_6448_, lean_object* v___x_6449_, lean_object* v___y_6450_, lean_object* v___y_6451_, lean_object* v___y_6452_){
_start:
{
lean_object* v_res_6453_; 
v_res_6453_ = l_Lean_Elab_Tactic_NormCast_elabAddElim___lam__0(v___x_6447_, v___x_6448_, v___x_6449_, v___y_6450_, v___y_6451_);
lean_dec(v___y_6451_);
lean_dec_ref(v___y_6450_);
lean_dec_ref(v___x_6449_);
return v_res_6453_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__4(void){
_start:
{
lean_object* v___x_6463_; 
v___x_6463_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_6463_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5(void){
_start:
{
lean_object* v___x_6464_; lean_object* v___x_6465_; 
v___x_6464_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__4, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__4_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__4);
v___x_6465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6465_, 0, v___x_6464_);
return v___x_6465_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__6(void){
_start:
{
lean_object* v___x_6466_; lean_object* v___x_6467_; lean_object* v___x_6468_; 
v___x_6466_ = lean_unsigned_to_nat(32u);
v___x_6467_ = lean_mk_empty_array_with_capacity(v___x_6466_);
v___x_6468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6468_, 0, v___x_6467_);
return v___x_6468_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7(void){
_start:
{
size_t v___x_6469_; lean_object* v___x_6470_; lean_object* v___x_6471_; lean_object* v___x_6472_; lean_object* v___x_6473_; lean_object* v___x_6474_; 
v___x_6469_ = ((size_t)5ULL);
v___x_6470_ = lean_unsigned_to_nat(0u);
v___x_6471_ = lean_unsigned_to_nat(32u);
v___x_6472_ = lean_mk_empty_array_with_capacity(v___x_6471_);
v___x_6473_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__6, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__6_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__6);
v___x_6474_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6474_, 0, v___x_6473_);
lean_ctor_set(v___x_6474_, 1, v___x_6472_);
lean_ctor_set(v___x_6474_, 2, v___x_6470_);
lean_ctor_set(v___x_6474_, 3, v___x_6470_);
lean_ctor_set_usize(v___x_6474_, 4, v___x_6469_);
return v___x_6474_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__8(void){
_start:
{
lean_object* v___x_6475_; lean_object* v___x_6476_; lean_object* v___x_6477_; lean_object* v___x_6478_; 
v___x_6475_ = lean_box(1);
v___x_6476_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7);
v___x_6477_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5);
v___x_6478_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6478_, 0, v___x_6477_);
lean_ctor_set(v___x_6478_, 1, v___x_6476_);
lean_ctor_set(v___x_6478_, 2, v___x_6475_);
return v___x_6478_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__10(void){
_start:
{
lean_object* v___x_6481_; lean_object* v___x_6482_; lean_object* v___x_6483_; 
v___x_6481_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5);
v___x_6482_ = lean_unsigned_to_nat(0u);
v___x_6483_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_6483_, 0, v___x_6482_);
lean_ctor_set(v___x_6483_, 1, v___x_6482_);
lean_ctor_set(v___x_6483_, 2, v___x_6482_);
lean_ctor_set(v___x_6483_, 3, v___x_6482_);
lean_ctor_set(v___x_6483_, 4, v___x_6481_);
lean_ctor_set(v___x_6483_, 5, v___x_6481_);
lean_ctor_set(v___x_6483_, 6, v___x_6481_);
lean_ctor_set(v___x_6483_, 7, v___x_6481_);
lean_ctor_set(v___x_6483_, 8, v___x_6481_);
lean_ctor_set(v___x_6483_, 9, v___x_6481_);
return v___x_6483_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__11(void){
_start:
{
lean_object* v___x_6484_; lean_object* v___x_6485_; 
v___x_6484_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5);
v___x_6485_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6485_, 0, v___x_6484_);
lean_ctor_set(v___x_6485_, 1, v___x_6484_);
lean_ctor_set(v___x_6485_, 2, v___x_6484_);
lean_ctor_set(v___x_6485_, 3, v___x_6484_);
lean_ctor_set(v___x_6485_, 4, v___x_6484_);
lean_ctor_set(v___x_6485_, 5, v___x_6484_);
return v___x_6485_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__12(void){
_start:
{
lean_object* v___x_6486_; lean_object* v___x_6487_; 
v___x_6486_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5);
v___x_6487_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6487_, 0, v___x_6486_);
lean_ctor_set(v___x_6487_, 1, v___x_6486_);
lean_ctor_set(v___x_6487_, 2, v___x_6486_);
lean_ctor_set(v___x_6487_, 3, v___x_6486_);
lean_ctor_set(v___x_6487_, 4, v___x_6486_);
return v___x_6487_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__13(void){
_start:
{
lean_object* v___x_6488_; lean_object* v___x_6489_; lean_object* v___x_6490_; lean_object* v___x_6491_; lean_object* v___x_6492_; lean_object* v___x_6493_; 
v___x_6488_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__12, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__12_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__12);
v___x_6489_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7);
v___x_6490_ = lean_box(1);
v___x_6491_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__11, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__11_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__11);
v___x_6492_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__10, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__10_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__10);
v___x_6493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6493_, 0, v___x_6492_);
lean_ctor_set(v___x_6493_, 1, v___x_6491_);
lean_ctor_set(v___x_6493_, 2, v___x_6490_);
lean_ctor_set(v___x_6493_, 3, v___x_6489_);
lean_ctor_set(v___x_6493_, 4, v___x_6488_);
return v___x_6493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim(lean_object* v_stx_6494_, lean_object* v_a_6495_, lean_object* v_a_6496_){
_start:
{
lean_object* v___x_6498_; uint8_t v___x_6499_; 
v___x_6498_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__1));
lean_inc(v_stx_6494_);
v___x_6499_ = l_Lean_Syntax_isOfKind(v_stx_6494_, v___x_6498_);
if (v___x_6499_ == 0)
{
lean_object* v___x_6500_; 
lean_dec(v_stx_6494_);
v___x_6500_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg();
return v___x_6500_;
}
else
{
lean_object* v___x_6501_; lean_object* v___x_6502_; lean_object* v___x_6503_; uint8_t v___x_6504_; 
v___x_6501_ = lean_unsigned_to_nat(1u);
v___x_6502_ = l_Lean_Syntax_getArg(v_stx_6494_, v___x_6501_);
lean_dec(v_stx_6494_);
v___x_6503_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__3));
lean_inc(v___x_6502_);
v___x_6504_ = l_Lean_Syntax_isOfKind(v___x_6502_, v___x_6503_);
if (v___x_6504_ == 0)
{
lean_object* v___x_6505_; 
lean_dec(v___x_6502_);
v___x_6505_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg();
return v___x_6505_;
}
else
{
lean_object* v___x_6506_; uint8_t v___x_6507_; uint8_t v___x_6508_; uint8_t v___x_6509_; uint8_t v___x_6510_; lean_object* v___x_6511_; uint64_t v___x_6512_; lean_object* v___x_6513_; lean_object* v___x_6514_; lean_object* v___x_6515_; lean_object* v___x_6516_; lean_object* v___x_6517_; lean_object* v___x_6518_; lean_object* v___x_6519_; lean_object* v___f_6520_; lean_object* v___x_6521_; 
v___x_6506_ = lean_unsigned_to_nat(0u);
v___x_6507_ = 0;
v___x_6508_ = 1;
v___x_6509_ = 0;
v___x_6510_ = 2;
v___x_6511_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_6511_, 0, v___x_6507_);
lean_ctor_set_uint8(v___x_6511_, 1, v___x_6507_);
lean_ctor_set_uint8(v___x_6511_, 2, v___x_6507_);
lean_ctor_set_uint8(v___x_6511_, 3, v___x_6507_);
lean_ctor_set_uint8(v___x_6511_, 4, v___x_6507_);
lean_ctor_set_uint8(v___x_6511_, 5, v___x_6504_);
lean_ctor_set_uint8(v___x_6511_, 6, v___x_6504_);
lean_ctor_set_uint8(v___x_6511_, 7, v___x_6507_);
lean_ctor_set_uint8(v___x_6511_, 8, v___x_6504_);
lean_ctor_set_uint8(v___x_6511_, 9, v___x_6508_);
lean_ctor_set_uint8(v___x_6511_, 10, v___x_6509_);
lean_ctor_set_uint8(v___x_6511_, 11, v___x_6504_);
lean_ctor_set_uint8(v___x_6511_, 12, v___x_6504_);
lean_ctor_set_uint8(v___x_6511_, 13, v___x_6504_);
lean_ctor_set_uint8(v___x_6511_, 14, v___x_6510_);
lean_ctor_set_uint8(v___x_6511_, 15, v___x_6504_);
lean_ctor_set_uint8(v___x_6511_, 16, v___x_6504_);
lean_ctor_set_uint8(v___x_6511_, 17, v___x_6504_);
lean_ctor_set_uint8(v___x_6511_, 18, v___x_6504_);
v___x_6512_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6511_);
v___x_6513_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_6513_, 0, v___x_6511_);
lean_ctor_set_uint64(v___x_6513_, sizeof(void*)*1, v___x_6512_);
v___x_6514_ = lean_box(1);
v___x_6515_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__8, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__8);
v___x_6516_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__9));
v___x_6517_ = lean_box(0);
v___x_6518_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6518_, 0, v___x_6513_);
lean_ctor_set(v___x_6518_, 1, v___x_6514_);
lean_ctor_set(v___x_6518_, 2, v___x_6515_);
lean_ctor_set(v___x_6518_, 3, v___x_6516_);
lean_ctor_set(v___x_6518_, 4, v___x_6517_);
lean_ctor_set(v___x_6518_, 5, v___x_6506_);
lean_ctor_set(v___x_6518_, 6, v___x_6517_);
lean_ctor_set_uint8(v___x_6518_, sizeof(void*)*7, v___x_6507_);
lean_ctor_set_uint8(v___x_6518_, sizeof(void*)*7 + 1, v___x_6507_);
lean_ctor_set_uint8(v___x_6518_, sizeof(void*)*7 + 2, v___x_6507_);
lean_ctor_set_uint8(v___x_6518_, sizeof(void*)*7 + 3, v___x_6504_);
v___x_6519_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__13, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__13_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__13);
v___f_6520_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___lam__0___boxed), 6, 3);
lean_closure_set(v___f_6520_, 0, v___x_6519_);
lean_closure_set(v___f_6520_, 1, v___x_6502_);
lean_closure_set(v___f_6520_, 2, v___x_6518_);
v___x_6521_ = l_Lean_Elab_Command_liftCoreM___redArg(v___f_6520_, v_a_6495_, v_a_6496_);
return v___x_6521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___boxed(lean_object* v_stx_6522_, lean_object* v_a_6523_, lean_object* v_a_6524_, lean_object* v_a_6525_){
_start:
{
lean_object* v_res_6526_; 
v_res_6526_ = l_Lean_Elab_Tactic_NormCast_elabAddElim(v_stx_6522_, v_a_6523_, v_a_6524_);
lean_dec(v_a_6524_);
lean_dec_ref(v_a_6523_);
return v_res_6526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1(){
_start:
{
lean_object* v___x_6535_; lean_object* v___x_6536_; lean_object* v___x_6537_; lean_object* v___x_6538_; lean_object* v___x_6539_; 
v___x_6535_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_6536_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__1));
v___x_6537_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1));
v___x_6538_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___boxed), 4, 0);
v___x_6539_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6535_, v___x_6536_, v___x_6537_, v___x_6538_);
return v___x_6539_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___boxed(lean_object* v_a_6540_){
_start:
{
lean_object* v_res_6541_; 
v_res_6541_ = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1();
return v_res_6541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3(){
_start:
{
lean_object* v___x_6568_; lean_object* v___x_6569_; lean_object* v___x_6570_; 
v___x_6568_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1));
v___x_6569_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__6));
v___x_6570_ = l_Lean_addBuiltinDeclarationRanges(v___x_6568_, v___x_6569_);
return v___x_6570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___boxed(lean_object* v_a_6571_){
_start:
{
lean_object* v_res_6572_; 
v_res_6572_ = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3();
return v_res_6572_;
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
res = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3();
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

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
lean_object* v___x_299_; lean_object* v_traceState_300_; lean_object* v_traces_301_; lean_object* v___x_302_; lean_object* v_traceState_303_; lean_object* v_env_304_; lean_object* v_nextMacroScope_305_; lean_object* v_ngen_306_; lean_object* v_auxDeclNGen_307_; lean_object* v_cache_308_; lean_object* v_messages_309_; lean_object* v_infoState_310_; lean_object* v_snapshotTasks_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_330_; 
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
v_isSharedCheck_330_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_330_ == 0)
{
v___x_313_ = v___x_302_;
v_isShared_314_ = v_isSharedCheck_330_;
goto v_resetjp_312_;
}
else
{
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
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_330_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
uint64_t v_tid_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_328_; 
v_tid_315_ = lean_ctor_get_uint64(v_traceState_303_, sizeof(void*)*1);
v_isSharedCheck_328_ = !lean_is_exclusive(v_traceState_303_);
if (v_isSharedCheck_328_ == 0)
{
lean_object* v_unused_329_; 
v_unused_329_ = lean_ctor_get(v_traceState_303_, 0);
lean_dec(v_unused_329_);
v___x_317_ = v_traceState_303_;
v_isShared_318_ = v_isSharedCheck_328_;
goto v_resetjp_316_;
}
else
{
lean_dec(v_traceState_303_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_328_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; lean_object* v___x_321_; 
v___x_319_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__1);
if (v_isShared_318_ == 0)
{
lean_ctor_set(v___x_317_, 0, v___x_319_);
v___x_321_ = v___x_317_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v___x_319_);
lean_ctor_set_uint64(v_reuseFailAlloc_327_, sizeof(void*)*1, v_tid_315_);
v___x_321_ = v_reuseFailAlloc_327_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_323_; 
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 4, v___x_321_);
v___x_323_ = v___x_313_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_env_304_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_nextMacroScope_305_);
lean_ctor_set(v_reuseFailAlloc_326_, 2, v_ngen_306_);
lean_ctor_set(v_reuseFailAlloc_326_, 3, v_auxDeclNGen_307_);
lean_ctor_set(v_reuseFailAlloc_326_, 4, v___x_321_);
lean_ctor_set(v_reuseFailAlloc_326_, 5, v_cache_308_);
lean_ctor_set(v_reuseFailAlloc_326_, 6, v_messages_309_);
lean_ctor_set(v_reuseFailAlloc_326_, 7, v_infoState_310_);
lean_ctor_set(v_reuseFailAlloc_326_, 8, v_snapshotTasks_311_);
v___x_323_ = v_reuseFailAlloc_326_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_st_ref_set(v___y_297_, v___x_323_);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v_traces_301_);
return v___x_325_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___boxed(lean_object* v___y_331_, lean_object* v___y_332_){
_start:
{
lean_object* v_res_333_; 
v_res_333_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___y_331_);
lean_dec(v___y_331_);
return v_res_333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0(lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___y_337_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___boxed(lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0(v___y_340_, v___y_341_, v___y_342_, v___y_343_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
return v_res_345_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(lean_object* v_opts_346_, lean_object* v_opt_347_){
_start:
{
lean_object* v_name_348_; lean_object* v_defValue_349_; lean_object* v_map_350_; lean_object* v___x_351_; 
v_name_348_ = lean_ctor_get(v_opt_347_, 0);
v_defValue_349_ = lean_ctor_get(v_opt_347_, 1);
v_map_350_ = lean_ctor_get(v_opts_346_, 0);
v___x_351_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_350_, v_name_348_);
if (lean_obj_tag(v___x_351_) == 0)
{
uint8_t v___x_352_; 
v___x_352_ = lean_unbox(v_defValue_349_);
return v___x_352_;
}
else
{
lean_object* v_val_353_; 
v_val_353_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_val_353_);
lean_dec_ref(v___x_351_);
if (lean_obj_tag(v_val_353_) == 1)
{
uint8_t v_v_354_; 
v_v_354_ = lean_ctor_get_uint8(v_val_353_, 0);
lean_dec_ref(v_val_353_);
return v_v_354_;
}
else
{
uint8_t v___x_355_; 
lean_dec(v_val_353_);
v___x_355_ = lean_unbox(v_defValue_349_);
return v___x_355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1___boxed(lean_object* v_opts_356_, lean_object* v_opt_357_){
_start:
{
uint8_t v_res_358_; lean_object* v_r_359_; 
v_res_358_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_opts_356_, v_opt_357_);
lean_dec_ref(v_opt_357_);
lean_dec_ref(v_opts_356_);
v_r_359_ = lean_box(v_res_358_);
return v_r_359_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__1(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__0));
v___x_362_ = l_Lean_stringToMessageData(v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0(lean_object* v_a_363_, lean_object* v_b_364_, lean_object* v_x_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_Meta_mkEq(v_a_363_, v_b_364_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_382_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_382_ == 0)
{
v___x_374_ = v___x_371_;
v_isShared_375_ = v_isSharedCheck_382_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_371_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_382_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_380_; 
v___x_376_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__1, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___closed__1);
v___x_377_ = l_Lean_MessageData_ofExpr(v_a_372_);
v___x_378_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_376_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_378_);
v___x_380_ = v___x_374_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
v_a_383_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_371_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_371_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___boxed(lean_object* v_a_391_, lean_object* v_b_392_, lean_object* v_x_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0(v_a_391_, v_b_392_, v_x_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec_ref(v_x_393_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__4(size_t v_sz_400_, size_t v_i_401_, lean_object* v_bs_402_){
_start:
{
uint8_t v___x_403_; 
v___x_403_ = lean_usize_dec_lt(v_i_401_, v_sz_400_);
if (v___x_403_ == 0)
{
return v_bs_402_;
}
else
{
lean_object* v_v_404_; lean_object* v_msg_405_; lean_object* v___x_406_; lean_object* v_bs_x27_407_; size_t v___x_408_; size_t v___x_409_; lean_object* v___x_410_; 
v_v_404_ = lean_array_uget_borrowed(v_bs_402_, v_i_401_);
v_msg_405_ = lean_ctor_get(v_v_404_, 1);
lean_inc_ref(v_msg_405_);
v___x_406_ = lean_unsigned_to_nat(0u);
v_bs_x27_407_ = lean_array_uset(v_bs_402_, v_i_401_, v___x_406_);
v___x_408_ = ((size_t)1ULL);
v___x_409_ = lean_usize_add(v_i_401_, v___x_408_);
v___x_410_ = lean_array_uset(v_bs_x27_407_, v_i_401_, v_msg_405_);
v_i_401_ = v___x_409_;
v_bs_402_ = v___x_410_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__4___boxed(lean_object* v_sz_412_, lean_object* v_i_413_, lean_object* v_bs_414_){
_start:
{
size_t v_sz_boxed_415_; size_t v_i_boxed_416_; lean_object* v_res_417_; 
v_sz_boxed_415_ = lean_unbox_usize(v_sz_412_);
lean_dec(v_sz_412_);
v_i_boxed_416_ = lean_unbox_usize(v_i_413_);
lean_dec(v_i_413_);
v_res_417_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__4(v_sz_boxed_415_, v_i_boxed_416_, v_bs_414_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__5(lean_object* v_msgData_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_){
_start:
{
lean_object* v___x_424_; lean_object* v_env_425_; lean_object* v___x_426_; lean_object* v_mctx_427_; lean_object* v_lctx_428_; lean_object* v_options_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_424_ = lean_st_ref_get(v___y_422_);
v_env_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc_ref(v_env_425_);
lean_dec(v___x_424_);
v___x_426_ = lean_st_ref_get(v___y_420_);
v_mctx_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc_ref(v_mctx_427_);
lean_dec(v___x_426_);
v_lctx_428_ = lean_ctor_get(v___y_419_, 2);
v_options_429_ = lean_ctor_get(v___y_421_, 2);
lean_inc_ref(v_options_429_);
lean_inc_ref(v_lctx_428_);
v___x_430_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_430_, 0, v_env_425_);
lean_ctor_set(v___x_430_, 1, v_mctx_427_);
lean_ctor_set(v___x_430_, 2, v_lctx_428_);
lean_ctor_set(v___x_430_, 3, v_options_429_);
v___x_431_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_431_, 0, v___x_430_);
lean_ctor_set(v___x_431_, 1, v_msgData_418_);
v___x_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__5___boxed(lean_object* v_msgData_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__5(v_msgData_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3(lean_object* v_oldTraces_440_, lean_object* v_data_441_, lean_object* v_ref_442_, lean_object* v_msg_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_fileName_449_; lean_object* v_fileMap_450_; lean_object* v_options_451_; lean_object* v_currRecDepth_452_; lean_object* v_maxRecDepth_453_; lean_object* v_ref_454_; lean_object* v_currNamespace_455_; lean_object* v_openDecls_456_; lean_object* v_initHeartbeats_457_; lean_object* v_maxHeartbeats_458_; lean_object* v_quotContext_459_; lean_object* v_currMacroScope_460_; uint8_t v_diag_461_; lean_object* v_cancelTk_x3f_462_; uint8_t v_suppressElabErrors_463_; lean_object* v_inheritedTraceOptions_464_; lean_object* v___x_465_; lean_object* v_traceState_466_; lean_object* v_traces_467_; lean_object* v_ref_468_; lean_object* v___x_469_; lean_object* v___x_470_; size_t v_sz_471_; size_t v___x_472_; lean_object* v___x_473_; lean_object* v_msg_474_; lean_object* v___x_475_; lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_513_; 
v_fileName_449_ = lean_ctor_get(v___y_446_, 0);
v_fileMap_450_ = lean_ctor_get(v___y_446_, 1);
v_options_451_ = lean_ctor_get(v___y_446_, 2);
v_currRecDepth_452_ = lean_ctor_get(v___y_446_, 3);
v_maxRecDepth_453_ = lean_ctor_get(v___y_446_, 4);
v_ref_454_ = lean_ctor_get(v___y_446_, 5);
v_currNamespace_455_ = lean_ctor_get(v___y_446_, 6);
v_openDecls_456_ = lean_ctor_get(v___y_446_, 7);
v_initHeartbeats_457_ = lean_ctor_get(v___y_446_, 8);
v_maxHeartbeats_458_ = lean_ctor_get(v___y_446_, 9);
v_quotContext_459_ = lean_ctor_get(v___y_446_, 10);
v_currMacroScope_460_ = lean_ctor_get(v___y_446_, 11);
v_diag_461_ = lean_ctor_get_uint8(v___y_446_, sizeof(void*)*14);
v_cancelTk_x3f_462_ = lean_ctor_get(v___y_446_, 12);
v_suppressElabErrors_463_ = lean_ctor_get_uint8(v___y_446_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_464_ = lean_ctor_get(v___y_446_, 13);
v___x_465_ = lean_st_ref_get(v___y_447_);
v_traceState_466_ = lean_ctor_get(v___x_465_, 4);
lean_inc_ref(v_traceState_466_);
lean_dec(v___x_465_);
v_traces_467_ = lean_ctor_get(v_traceState_466_, 0);
lean_inc_ref(v_traces_467_);
lean_dec_ref(v_traceState_466_);
v_ref_468_ = l_Lean_replaceRef(v_ref_442_, v_ref_454_);
lean_inc_ref(v_inheritedTraceOptions_464_);
lean_inc(v_cancelTk_x3f_462_);
lean_inc(v_currMacroScope_460_);
lean_inc(v_quotContext_459_);
lean_inc(v_maxHeartbeats_458_);
lean_inc(v_initHeartbeats_457_);
lean_inc(v_openDecls_456_);
lean_inc(v_currNamespace_455_);
lean_inc(v_maxRecDepth_453_);
lean_inc(v_currRecDepth_452_);
lean_inc_ref(v_options_451_);
lean_inc_ref(v_fileMap_450_);
lean_inc_ref(v_fileName_449_);
v___x_469_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_469_, 0, v_fileName_449_);
lean_ctor_set(v___x_469_, 1, v_fileMap_450_);
lean_ctor_set(v___x_469_, 2, v_options_451_);
lean_ctor_set(v___x_469_, 3, v_currRecDepth_452_);
lean_ctor_set(v___x_469_, 4, v_maxRecDepth_453_);
lean_ctor_set(v___x_469_, 5, v_ref_468_);
lean_ctor_set(v___x_469_, 6, v_currNamespace_455_);
lean_ctor_set(v___x_469_, 7, v_openDecls_456_);
lean_ctor_set(v___x_469_, 8, v_initHeartbeats_457_);
lean_ctor_set(v___x_469_, 9, v_maxHeartbeats_458_);
lean_ctor_set(v___x_469_, 10, v_quotContext_459_);
lean_ctor_set(v___x_469_, 11, v_currMacroScope_460_);
lean_ctor_set(v___x_469_, 12, v_cancelTk_x3f_462_);
lean_ctor_set(v___x_469_, 13, v_inheritedTraceOptions_464_);
lean_ctor_set_uint8(v___x_469_, sizeof(void*)*14, v_diag_461_);
lean_ctor_set_uint8(v___x_469_, sizeof(void*)*14 + 1, v_suppressElabErrors_463_);
v___x_470_ = l_Lean_PersistentArray_toArray___redArg(v_traces_467_);
lean_dec_ref(v_traces_467_);
v_sz_471_ = lean_array_size(v___x_470_);
v___x_472_ = ((size_t)0ULL);
v___x_473_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__4(v_sz_471_, v___x_472_, v___x_470_);
v_msg_474_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_474_, 0, v_data_441_);
lean_ctor_set(v_msg_474_, 1, v_msg_443_);
lean_ctor_set(v_msg_474_, 2, v___x_473_);
v___x_475_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__5(v_msg_474_, v___y_444_, v___y_445_, v___x_469_, v___y_447_);
lean_dec_ref(v___x_469_);
v_a_476_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_513_ == 0)
{
v___x_478_ = v___x_475_;
v_isShared_479_ = v_isSharedCheck_513_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_475_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_513_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; lean_object* v_traceState_481_; lean_object* v_env_482_; lean_object* v_nextMacroScope_483_; lean_object* v_ngen_484_; lean_object* v_auxDeclNGen_485_; lean_object* v_cache_486_; lean_object* v_messages_487_; lean_object* v_infoState_488_; lean_object* v_snapshotTasks_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_512_; 
v___x_480_ = lean_st_ref_take(v___y_447_);
v_traceState_481_ = lean_ctor_get(v___x_480_, 4);
v_env_482_ = lean_ctor_get(v___x_480_, 0);
v_nextMacroScope_483_ = lean_ctor_get(v___x_480_, 1);
v_ngen_484_ = lean_ctor_get(v___x_480_, 2);
v_auxDeclNGen_485_ = lean_ctor_get(v___x_480_, 3);
v_cache_486_ = lean_ctor_get(v___x_480_, 5);
v_messages_487_ = lean_ctor_get(v___x_480_, 6);
v_infoState_488_ = lean_ctor_get(v___x_480_, 7);
v_snapshotTasks_489_ = lean_ctor_get(v___x_480_, 8);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_512_ == 0)
{
v___x_491_ = v___x_480_;
v_isShared_492_ = v_isSharedCheck_512_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_snapshotTasks_489_);
lean_inc(v_infoState_488_);
lean_inc(v_messages_487_);
lean_inc(v_cache_486_);
lean_inc(v_traceState_481_);
lean_inc(v_auxDeclNGen_485_);
lean_inc(v_ngen_484_);
lean_inc(v_nextMacroScope_483_);
lean_inc(v_env_482_);
lean_dec(v___x_480_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_512_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
uint64_t v_tid_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_510_; 
v_tid_493_ = lean_ctor_get_uint64(v_traceState_481_, sizeof(void*)*1);
v_isSharedCheck_510_ = !lean_is_exclusive(v_traceState_481_);
if (v_isSharedCheck_510_ == 0)
{
lean_object* v_unused_511_; 
v_unused_511_ = lean_ctor_get(v_traceState_481_, 0);
lean_dec(v_unused_511_);
v___x_495_ = v_traceState_481_;
v_isShared_496_ = v_isSharedCheck_510_;
goto v_resetjp_494_;
}
else
{
lean_dec(v_traceState_481_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_510_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_497_, 0, v_ref_442_);
lean_ctor_set(v___x_497_, 1, v_a_476_);
v___x_498_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_440_, v___x_497_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_498_);
v___x_500_ = v___x_495_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_498_);
lean_ctor_set_uint64(v_reuseFailAlloc_509_, sizeof(void*)*1, v_tid_493_);
v___x_500_ = v_reuseFailAlloc_509_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_502_; 
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 4, v___x_500_);
v___x_502_ = v___x_491_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_env_482_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v_nextMacroScope_483_);
lean_ctor_set(v_reuseFailAlloc_508_, 2, v_ngen_484_);
lean_ctor_set(v_reuseFailAlloc_508_, 3, v_auxDeclNGen_485_);
lean_ctor_set(v_reuseFailAlloc_508_, 4, v___x_500_);
lean_ctor_set(v_reuseFailAlloc_508_, 5, v_cache_486_);
lean_ctor_set(v_reuseFailAlloc_508_, 6, v_messages_487_);
lean_ctor_set(v_reuseFailAlloc_508_, 7, v_infoState_488_);
lean_ctor_set(v_reuseFailAlloc_508_, 8, v_snapshotTasks_489_);
v___x_502_ = v_reuseFailAlloc_508_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_503_ = lean_st_ref_set(v___y_447_, v___x_502_);
v___x_504_ = lean_box(0);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 0, v___x_504_);
v___x_506_ = v___x_478_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3___boxed(lean_object* v_oldTraces_514_, lean_object* v_data_515_, lean_object* v_ref_516_, lean_object* v_msg_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3(v_oldTraces_514_, v_data_515_, v_ref_516_, v_msg_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
return v_res_523_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__2(lean_object* v_e_524_){
_start:
{
if (lean_obj_tag(v_e_524_) == 0)
{
uint8_t v___x_525_; 
v___x_525_ = 2;
return v___x_525_;
}
else
{
lean_object* v_a_526_; 
v_a_526_ = lean_ctor_get(v_e_524_, 0);
if (lean_obj_tag(v_a_526_) == 0)
{
uint8_t v___x_527_; 
v___x_527_ = 1;
return v___x_527_;
}
else
{
uint8_t v___x_528_; 
v___x_528_ = 0;
return v___x_528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__2___boxed(lean_object* v_e_529_){
_start:
{
uint8_t v_res_530_; lean_object* v_r_531_; 
v_res_530_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__2(v_e_529_);
lean_dec_ref(v_e_529_);
v_r_531_ = lean_box(v_res_530_);
return v_r_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__5(lean_object* v_opts_532_, lean_object* v_opt_533_){
_start:
{
lean_object* v_name_534_; lean_object* v_defValue_535_; lean_object* v_map_536_; lean_object* v___x_537_; 
v_name_534_ = lean_ctor_get(v_opt_533_, 0);
v_defValue_535_ = lean_ctor_get(v_opt_533_, 1);
v_map_536_ = lean_ctor_get(v_opts_532_, 0);
v___x_537_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_536_, v_name_534_);
if (lean_obj_tag(v___x_537_) == 0)
{
lean_inc(v_defValue_535_);
return v_defValue_535_;
}
else
{
lean_object* v_val_538_; 
v_val_538_ = lean_ctor_get(v___x_537_, 0);
lean_inc(v_val_538_);
lean_dec_ref(v___x_537_);
if (lean_obj_tag(v_val_538_) == 3)
{
lean_object* v_v_539_; 
v_v_539_ = lean_ctor_get(v_val_538_, 0);
lean_inc(v_v_539_);
lean_dec_ref(v_val_538_);
return v_v_539_;
}
else
{
lean_dec(v_val_538_);
lean_inc(v_defValue_535_);
return v_defValue_535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__5___boxed(lean_object* v_opts_540_, lean_object* v_opt_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__5(v_opts_540_, v_opt_541_);
lean_dec_ref(v_opt_541_);
lean_dec_ref(v_opts_540_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4___redArg(lean_object* v_x_543_){
_start:
{
if (lean_obj_tag(v_x_543_) == 0)
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
v_a_545_ = lean_ctor_get(v_x_543_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v_x_543_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v_x_543_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v_x_543_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
lean_ctor_set_tag(v___x_547_, 1);
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
else
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
v_a_553_ = lean_ctor_get(v_x_543_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v_x_543_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v_x_543_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v_x_543_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
lean_ctor_set_tag(v___x_555_, 0);
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4___redArg___boxed(lean_object* v_x_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4___redArg(v_x_561_);
return v_res_563_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1(void){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_565_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__0));
v___x_566_ = l_Lean_stringToMessageData(v___x_565_);
return v___x_566_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2(void){
_start:
{
lean_object* v___x_567_; double v___x_568_; 
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_float_of_nat(v___x_567_);
return v___x_568_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__4(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__3));
v___x_571_ = l_Lean_stringToMessageData(v___x_570_);
return v___x_571_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__5(void){
_start:
{
lean_object* v___x_572_; double v___x_573_; 
v___x_572_ = lean_unsigned_to_nat(1000u);
v___x_573_ = lean_float_of_nat(v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(lean_object* v_cls_574_, uint8_t v_collapsed_575_, lean_object* v_tag_576_, lean_object* v_opts_577_, uint8_t v_clsEnabled_578_, lean_object* v_oldTraces_579_, lean_object* v_msg_580_, lean_object* v_resStartStop_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v_fst_587_; lean_object* v_snd_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_686_; 
v_fst_587_ = lean_ctor_get(v_resStartStop_581_, 0);
v_snd_588_ = lean_ctor_get(v_resStartStop_581_, 1);
v_isSharedCheck_686_ = !lean_is_exclusive(v_resStartStop_581_);
if (v_isSharedCheck_686_ == 0)
{
v___x_590_ = v_resStartStop_581_;
v_isShared_591_ = v_isSharedCheck_686_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_snd_588_);
lean_inc(v_fst_587_);
lean_dec(v_resStartStop_581_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_686_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v_data_595_; lean_object* v_fst_606_; lean_object* v_snd_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_685_; 
v_fst_606_ = lean_ctor_get(v_snd_588_, 0);
v_snd_607_ = lean_ctor_get(v_snd_588_, 1);
v_isSharedCheck_685_ = !lean_is_exclusive(v_snd_588_);
if (v_isSharedCheck_685_ == 0)
{
v___x_609_ = v_snd_588_;
v_isShared_610_ = v_isSharedCheck_685_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_snd_607_);
lean_inc(v_fst_606_);
lean_dec(v_snd_588_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_685_;
goto v_resetjp_608_;
}
v___jp_592_:
{
lean_object* v___x_596_; 
lean_inc(v___y_593_);
v___x_596_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3(v_oldTraces_579_, v_data_595_, v___y_593_, v___y_594_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
if (lean_obj_tag(v___x_596_) == 0)
{
lean_object* v___x_597_; 
lean_dec_ref(v___x_596_);
v___x_597_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4___redArg(v_fst_587_);
return v___x_597_;
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec(v_fst_587_);
v_a_598_ = lean_ctor_get(v___x_596_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_596_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_596_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_596_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
v_resetjp_608_:
{
lean_object* v___x_611_; uint8_t v___x_612_; lean_object* v___y_614_; lean_object* v_a_615_; uint8_t v___y_639_; double v___y_670_; 
v___x_611_ = l_Lean_trace_profiler;
v___x_612_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_opts_577_, v___x_611_);
if (v___x_612_ == 0)
{
v___y_639_ = v___x_612_;
goto v___jp_638_;
}
else
{
lean_object* v___x_675_; uint8_t v___x_676_; 
v___x_675_ = l_Lean_trace_profiler_useHeartbeats;
v___x_676_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_opts_577_, v___x_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; double v___x_679_; double v___x_680_; double v___x_681_; 
v___x_677_ = l_Lean_trace_profiler_threshold;
v___x_678_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__5(v_opts_577_, v___x_677_);
v___x_679_ = lean_float_of_nat(v___x_678_);
v___x_680_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__5);
v___x_681_ = lean_float_div(v___x_679_, v___x_680_);
v___y_670_ = v___x_681_;
goto v___jp_669_;
}
else
{
lean_object* v___x_682_; lean_object* v___x_683_; double v___x_684_; 
v___x_682_ = l_Lean_trace_profiler_threshold;
v___x_683_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__5(v_opts_577_, v___x_682_);
v___x_684_ = lean_float_of_nat(v___x_683_);
v___y_670_ = v___x_684_;
goto v___jp_669_;
}
}
v___jp_613_:
{
uint8_t v_result_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_621_; 
v_result_616_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__2(v_fst_587_);
v___x_617_ = l_Lean_TraceResult_toEmoji(v_result_616_);
v___x_618_ = l_Lean_stringToMessageData(v___x_617_);
v___x_619_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1);
if (v_isShared_610_ == 0)
{
lean_ctor_set_tag(v___x_609_, 7);
lean_ctor_set(v___x_609_, 1, v___x_619_);
lean_ctor_set(v___x_609_, 0, v___x_618_);
v___x_621_ = v___x_609_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_618_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v___x_619_);
v___x_621_ = v_reuseFailAlloc_632_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v_m_623_; 
if (v_isShared_591_ == 0)
{
lean_ctor_set_tag(v___x_590_, 7);
lean_ctor_set(v___x_590_, 1, v_a_615_);
lean_ctor_set(v___x_590_, 0, v___x_621_);
v_m_623_ = v___x_590_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_621_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_a_615_);
v_m_623_ = v_reuseFailAlloc_631_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_624_; lean_object* v___x_625_; double v___x_626_; lean_object* v_data_627_; 
v___x_624_ = lean_box(v_result_616_);
v___x_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
v___x_626_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2);
lean_inc_ref(v_tag_576_);
lean_inc_ref(v___x_625_);
lean_inc(v_cls_574_);
v_data_627_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_627_, 0, v_cls_574_);
lean_ctor_set(v_data_627_, 1, v___x_625_);
lean_ctor_set(v_data_627_, 2, v_tag_576_);
lean_ctor_set_float(v_data_627_, sizeof(void*)*3, v___x_626_);
lean_ctor_set_float(v_data_627_, sizeof(void*)*3 + 8, v___x_626_);
lean_ctor_set_uint8(v_data_627_, sizeof(void*)*3 + 16, v_collapsed_575_);
if (v___x_612_ == 0)
{
lean_dec_ref(v___x_625_);
lean_dec(v_snd_607_);
lean_dec(v_fst_606_);
lean_dec_ref(v_tag_576_);
lean_dec(v_cls_574_);
v___y_593_ = v___y_614_;
v___y_594_ = v_m_623_;
v_data_595_ = v_data_627_;
goto v___jp_592_;
}
else
{
lean_object* v_data_628_; double v___x_629_; double v___x_630_; 
lean_dec_ref(v_data_627_);
v_data_628_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_628_, 0, v_cls_574_);
lean_ctor_set(v_data_628_, 1, v___x_625_);
lean_ctor_set(v_data_628_, 2, v_tag_576_);
v___x_629_ = lean_unbox_float(v_fst_606_);
lean_dec(v_fst_606_);
lean_ctor_set_float(v_data_628_, sizeof(void*)*3, v___x_629_);
v___x_630_ = lean_unbox_float(v_snd_607_);
lean_dec(v_snd_607_);
lean_ctor_set_float(v_data_628_, sizeof(void*)*3 + 8, v___x_630_);
lean_ctor_set_uint8(v_data_628_, sizeof(void*)*3 + 16, v_collapsed_575_);
v___y_593_ = v___y_614_;
v___y_594_ = v_m_623_;
v_data_595_ = v_data_628_;
goto v___jp_592_;
}
}
}
}
v___jp_633_:
{
lean_object* v_ref_634_; lean_object* v___x_635_; 
v_ref_634_ = lean_ctor_get(v___y_584_, 5);
lean_inc(v___y_585_);
lean_inc_ref(v___y_584_);
lean_inc(v___y_583_);
lean_inc_ref(v___y_582_);
lean_inc(v_fst_587_);
v___x_635_ = lean_apply_6(v_msg_580_, v_fst_587_, v___y_582_, v___y_583_, v___y_584_, v___y_585_, lean_box(0));
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_a_636_);
lean_dec_ref(v___x_635_);
v___y_614_ = v_ref_634_;
v_a_615_ = v_a_636_;
goto v___jp_613_;
}
else
{
lean_object* v___x_637_; 
lean_dec_ref(v___x_635_);
v___x_637_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__4);
v___y_614_ = v_ref_634_;
v_a_615_ = v___x_637_;
goto v___jp_613_;
}
}
v___jp_638_:
{
if (v_clsEnabled_578_ == 0)
{
if (v___y_639_ == 0)
{
lean_object* v___x_640_; lean_object* v_traceState_641_; lean_object* v_env_642_; lean_object* v_nextMacroScope_643_; lean_object* v_ngen_644_; lean_object* v_auxDeclNGen_645_; lean_object* v_cache_646_; lean_object* v_messages_647_; lean_object* v_infoState_648_; lean_object* v_snapshotTasks_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_668_; 
lean_del_object(v___x_609_);
lean_dec(v_snd_607_);
lean_dec(v_fst_606_);
lean_del_object(v___x_590_);
lean_dec_ref(v_msg_580_);
lean_dec_ref(v_tag_576_);
lean_dec(v_cls_574_);
v___x_640_ = lean_st_ref_take(v___y_585_);
v_traceState_641_ = lean_ctor_get(v___x_640_, 4);
v_env_642_ = lean_ctor_get(v___x_640_, 0);
v_nextMacroScope_643_ = lean_ctor_get(v___x_640_, 1);
v_ngen_644_ = lean_ctor_get(v___x_640_, 2);
v_auxDeclNGen_645_ = lean_ctor_get(v___x_640_, 3);
v_cache_646_ = lean_ctor_get(v___x_640_, 5);
v_messages_647_ = lean_ctor_get(v___x_640_, 6);
v_infoState_648_ = lean_ctor_get(v___x_640_, 7);
v_snapshotTasks_649_ = lean_ctor_get(v___x_640_, 8);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_640_);
if (v_isSharedCheck_668_ == 0)
{
v___x_651_ = v___x_640_;
v_isShared_652_ = v_isSharedCheck_668_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_snapshotTasks_649_);
lean_inc(v_infoState_648_);
lean_inc(v_messages_647_);
lean_inc(v_cache_646_);
lean_inc(v_traceState_641_);
lean_inc(v_auxDeclNGen_645_);
lean_inc(v_ngen_644_);
lean_inc(v_nextMacroScope_643_);
lean_inc(v_env_642_);
lean_dec(v___x_640_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_668_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
uint64_t v_tid_653_; lean_object* v_traces_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_667_; 
v_tid_653_ = lean_ctor_get_uint64(v_traceState_641_, sizeof(void*)*1);
v_traces_654_ = lean_ctor_get(v_traceState_641_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v_traceState_641_);
if (v_isSharedCheck_667_ == 0)
{
v___x_656_ = v_traceState_641_;
v_isShared_657_ = v_isSharedCheck_667_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_traces_654_);
lean_dec(v_traceState_641_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_667_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v___x_660_; 
v___x_658_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_579_, v_traces_654_);
lean_dec_ref(v_traces_654_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 0, v___x_658_);
v___x_660_ = v___x_656_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v___x_658_);
lean_ctor_set_uint64(v_reuseFailAlloc_666_, sizeof(void*)*1, v_tid_653_);
v___x_660_ = v_reuseFailAlloc_666_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v___x_662_; 
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 4, v___x_660_);
v___x_662_ = v___x_651_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_env_642_);
lean_ctor_set(v_reuseFailAlloc_665_, 1, v_nextMacroScope_643_);
lean_ctor_set(v_reuseFailAlloc_665_, 2, v_ngen_644_);
lean_ctor_set(v_reuseFailAlloc_665_, 3, v_auxDeclNGen_645_);
lean_ctor_set(v_reuseFailAlloc_665_, 4, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_665_, 5, v_cache_646_);
lean_ctor_set(v_reuseFailAlloc_665_, 6, v_messages_647_);
lean_ctor_set(v_reuseFailAlloc_665_, 7, v_infoState_648_);
lean_ctor_set(v_reuseFailAlloc_665_, 8, v_snapshotTasks_649_);
v___x_662_ = v_reuseFailAlloc_665_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = lean_st_ref_set(v___y_585_, v___x_662_);
v___x_664_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4___redArg(v_fst_587_);
return v___x_664_;
}
}
}
}
}
else
{
goto v___jp_633_;
}
}
else
{
goto v___jp_633_;
}
}
v___jp_669_:
{
double v___x_671_; double v___x_672_; double v___x_673_; uint8_t v___x_674_; 
v___x_671_ = lean_unbox_float(v_snd_607_);
v___x_672_ = lean_unbox_float(v_fst_606_);
v___x_673_ = lean_float_sub(v___x_671_, v___x_672_);
v___x_674_ = lean_float_decLt(v___y_670_, v___x_673_);
v___y_639_ = v___x_674_;
goto v___jp_638_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___boxed(lean_object* v_cls_687_, lean_object* v_collapsed_688_, lean_object* v_tag_689_, lean_object* v_opts_690_, lean_object* v_clsEnabled_691_, lean_object* v_oldTraces_692_, lean_object* v_msg_693_, lean_object* v_resStartStop_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
uint8_t v_collapsed_boxed_700_; uint8_t v_clsEnabled_boxed_701_; lean_object* v_res_702_; 
v_collapsed_boxed_700_ = lean_unbox(v_collapsed_688_);
v_clsEnabled_boxed_701_ = lean_unbox(v_clsEnabled_691_);
v_res_702_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v_cls_687_, v_collapsed_boxed_700_, v_tag_689_, v_opts_690_, v_clsEnabled_boxed_701_, v_oldTraces_692_, v_msg_693_, v_resStartStop_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_696_);
lean_dec_ref(v___y_695_);
lean_dec_ref(v_opts_690_);
return v_res_702_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3(void){
_start:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_707_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__2_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_));
v___x_708_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__2));
v___x_709_ = l_Lean_Name_append(v___x_708_, v___x_707_);
return v___x_709_;
}
}
static double _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4(void){
_start:
{
lean_object* v___x_710_; double v___x_711_; 
v___x_710_ = lean_unsigned_to_nat(1000000000u);
v___x_711_ = lean_float_of_nat(v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(lean_object* v_a_712_, lean_object* v_b_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v___x_719_; lean_object* v_options_720_; uint8_t v_hasTrace_721_; 
v___x_719_ = l_Lean_Meta_NormCast_normCastExt;
v_options_720_ = lean_ctor_get(v_a_716_, 2);
v_hasTrace_721_ = lean_ctor_get_uint8(v_options_720_, sizeof(void*)*1);
if (v_hasTrace_721_ == 0)
{
lean_object* v_down_722_; lean_object* v___x_723_; 
v_down_722_ = lean_ctor_get(v___x_719_, 1);
v___x_723_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_down_722_, v_a_717_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v_a_724_; lean_object* v___x_725_; 
v_a_724_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_a_724_);
lean_dec_ref(v___x_723_);
v___x_725_ = l_Lean_Elab_Tactic_NormCast_proveEqUsing(v_a_724_, v_a_712_, v_b_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_725_;
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
lean_dec_ref(v_b_713_);
lean_dec_ref(v_a_712_);
v_a_726_ = lean_ctor_get(v___x_723_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_723_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_723_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
}
}
}
}
else
{
lean_object* v_down_734_; lean_object* v_inheritedTraceOptions_735_; lean_object* v___f_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; lean_object* v___y_742_; lean_object* v___y_743_; lean_object* v_a_744_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v_a_759_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v_a_764_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v_a_776_; 
v_down_734_ = lean_ctor_get(v___x_719_, 1);
v_inheritedTraceOptions_735_ = lean_ctor_get(v_a_716_, 13);
lean_inc_ref(v_b_713_);
lean_inc_ref(v_a_712_);
v___f_736_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___lam__0___boxed), 8, 2);
lean_closure_set(v___f_736_, 0, v_a_712_);
lean_closure_set(v___f_736_, 1, v_b_713_);
v___x_737_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__2_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_));
v___x_738_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_739_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3);
v___x_740_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_735_, v_options_720_, v___x_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_811_; uint8_t v___x_812_; 
v___x_811_ = l_Lean_trace_profiler;
v___x_812_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_720_, v___x_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; 
lean_dec_ref(v___f_736_);
v___x_813_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_down_734_, v_a_717_);
if (lean_obj_tag(v___x_813_) == 0)
{
lean_object* v_a_814_; lean_object* v___x_815_; 
v_a_814_ = lean_ctor_get(v___x_813_, 0);
lean_inc(v_a_814_);
lean_dec_ref(v___x_813_);
v___x_815_ = l_Lean_Elab_Tactic_NormCast_proveEqUsing(v_a_814_, v_a_712_, v_b_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_815_;
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_dec_ref(v_b_713_);
lean_dec_ref(v_a_712_);
v_a_816_ = lean_ctor_get(v___x_813_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_813_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_813_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_813_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
else
{
goto v___jp_778_;
}
}
else
{
goto v___jp_778_;
}
v___jp_741_:
{
lean_object* v___x_745_; double v___x_746_; double v___x_747_; double v___x_748_; double v___x_749_; double v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_745_ = lean_io_mono_nanos_now();
v___x_746_ = lean_float_of_nat(v___y_743_);
v___x_747_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4);
v___x_748_ = lean_float_div(v___x_746_, v___x_747_);
v___x_749_ = lean_float_of_nat(v___x_745_);
v___x_750_ = lean_float_div(v___x_749_, v___x_747_);
v___x_751_ = lean_box_float(v___x_748_);
v___x_752_ = lean_box_float(v___x_750_);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_751_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v_a_744_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v___x_737_, v_hasTrace_721_, v___x_738_, v_options_720_, v___x_740_, v___y_742_, v___f_736_, v___x_754_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_755_;
}
v___jp_756_:
{
lean_object* v___x_760_; 
v___x_760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_760_, 0, v_a_759_);
v___y_742_ = v___y_757_;
v___y_743_ = v___y_758_;
v_a_744_ = v___x_760_;
goto v___jp_741_;
}
v___jp_761_:
{
lean_object* v___x_765_; double v___x_766_; double v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_765_ = lean_io_get_num_heartbeats();
v___x_766_ = lean_float_of_nat(v___y_762_);
v___x_767_ = lean_float_of_nat(v___x_765_);
v___x_768_ = lean_box_float(v___x_766_);
v___x_769_ = lean_box_float(v___x_767_);
v___x_770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_770_, 0, v___x_768_);
lean_ctor_set(v___x_770_, 1, v___x_769_);
v___x_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_771_, 0, v_a_764_);
lean_ctor_set(v___x_771_, 1, v___x_770_);
v___x_772_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2(v___x_737_, v_hasTrace_721_, v___x_738_, v_options_720_, v___x_740_, v___y_763_, v___f_736_, v___x_771_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
return v___x_772_;
}
v___jp_773_:
{
lean_object* v___x_777_; 
v___x_777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_777_, 0, v_a_776_);
v___y_762_ = v___y_774_;
v___y_763_ = v___y_775_;
v_a_764_ = v___x_777_;
goto v___jp_761_;
}
v___jp_778_:
{
lean_object* v___x_779_; lean_object* v_a_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v___x_779_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v_a_717_);
v_a_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_780_);
lean_dec_ref(v___x_779_);
v___x_781_ = l_Lean_trace_profiler_useHeartbeats;
v___x_782_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_720_, v___x_781_);
if (v___x_782_ == 0)
{
lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_783_ = lean_io_mono_nanos_now();
v___x_784_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_down_734_, v_a_717_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_786_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
lean_dec_ref(v___x_784_);
v___x_786_ = l_Lean_Elab_Tactic_NormCast_proveEqUsing(v_a_785_, v_a_712_, v_b_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_786_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_786_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
lean_ctor_set_tag(v___x_789_, 1);
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
v___y_742_ = v_a_780_;
v___y_743_ = v___x_783_;
v_a_744_ = v___x_792_;
goto v___jp_741_;
}
}
}
else
{
lean_object* v_a_795_; 
v_a_795_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_795_);
lean_dec_ref(v___x_786_);
v___y_757_ = v_a_780_;
v___y_758_ = v___x_783_;
v_a_759_ = v_a_795_;
goto v___jp_756_;
}
}
else
{
lean_object* v_a_796_; 
lean_dec_ref(v_b_713_);
lean_dec_ref(v_a_712_);
v_a_796_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_796_);
lean_dec_ref(v___x_784_);
v___y_757_ = v_a_780_;
v___y_758_ = v___x_783_;
v_a_759_ = v_a_796_;
goto v___jp_756_;
}
}
else
{
lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_797_ = lean_io_get_num_heartbeats();
v___x_798_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_down_734_, v_a_717_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v___x_800_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref(v___x_798_);
v___x_800_ = l_Lean_Elab_Tactic_NormCast_proveEqUsing(v_a_799_, v_a_712_, v_b_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
v_a_801_ = lean_ctor_get(v___x_800_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_800_);
if (v_isSharedCheck_808_ == 0)
{
v___x_803_ = v___x_800_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_800_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
lean_ctor_set_tag(v___x_803_, 1);
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_a_801_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
v___y_762_ = v___x_797_;
v___y_763_ = v_a_780_;
v_a_764_ = v___x_806_;
goto v___jp_761_;
}
}
}
else
{
lean_object* v_a_809_; 
v_a_809_ = lean_ctor_get(v___x_800_, 0);
lean_inc(v_a_809_);
lean_dec_ref(v___x_800_);
v___y_774_ = v___x_797_;
v___y_775_ = v_a_780_;
v_a_776_ = v_a_809_;
goto v___jp_773_;
}
}
else
{
lean_object* v_a_810_; 
lean_dec_ref(v_b_713_);
lean_dec_ref(v_a_712_);
v_a_810_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_810_);
lean_dec_ref(v___x_798_);
v___y_774_ = v___x_797_;
v___y_775_ = v_a_780_;
v_a_776_ = v_a_810_;
goto v___jp_773_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___boxed(lean_object* v_a_824_, lean_object* v_b_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_a_824_, v_b_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
lean_dec(v_a_829_);
lean_dec_ref(v_a_828_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4(lean_object* v_00_u03b1_832_, lean_object* v_x_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4___redArg(v_x_833_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4___boxed(lean_object* v_00_u03b1_840_, lean_object* v_x_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4(v_00_u03b1_840_, v_x_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
lean_dec(v___y_845_);
lean_dec_ref(v___y_844_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(lean_object* v_msg_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_ref_854_; lean_object* v___x_855_; lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_864_; 
v_ref_854_ = lean_ctor_get(v___y_851_, 5);
v___x_855_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__5(v_msg_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_864_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_864_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_864_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_860_; lean_object* v___x_862_; 
lean_inc(v_ref_854_);
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v_ref_854_);
lean_ctor_set(v___x_860_, 1, v_a_856_);
if (v_isShared_859_ == 0)
{
lean_ctor_set_tag(v___x_858_, 1);
lean_ctor_set(v___x_858_, 0, v___x_860_);
v___x_862_ = v___x_858_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg___boxed(lean_object* v_msg_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v_msg_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
return v_res_871_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_mkCoe___closed__0));
v___x_874_ = l_Lean_stringToMessageData(v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_mkCoe(lean_object* v_e_875_, lean_object* v_ty_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_){
_start:
{
lean_object* v___x_882_; 
v___x_882_ = l_Lean_Meta_coerce_x3f(v_e_875_, v_ty_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_893_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_893_ == 0)
{
v___x_885_ = v___x_882_;
v_isShared_886_ = v_isSharedCheck_893_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_882_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_893_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
if (lean_obj_tag(v_a_883_) == 1)
{
lean_object* v_a_887_; lean_object* v___x_889_; 
v_a_887_ = lean_ctor_get(v_a_883_, 0);
lean_inc(v_a_887_);
lean_dec_ref(v_a_883_);
if (v_isShared_886_ == 0)
{
lean_ctor_set(v___x_885_, 0, v_a_887_);
v___x_889_ = v___x_885_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
else
{
lean_object* v___x_891_; lean_object* v___x_892_; 
lean_del_object(v___x_885_);
lean_dec(v_a_883_);
v___x_891_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_892_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_891_, v_a_877_, v_a_878_, v_a_879_, v_a_880_);
return v___x_892_;
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
v_a_894_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_882_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_882_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_mkCoe___boxed(lean_object* v_e_902_, lean_object* v_ty_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_e_902_, v_ty_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_);
lean_dec(v_a_907_);
lean_dec_ref(v_a_906_);
lean_dec(v_a_905_);
lean_dec_ref(v_a_904_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0(lean_object* v_00_u03b1_910_, lean_object* v_msg_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v_msg_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___boxed(lean_object* v_00_u03b1_918_, lean_object* v_msg_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0(v_00_u03b1_918_, v_msg_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(lean_object* v_e_926_, lean_object* v_a_927_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = l_Lean_Expr_getAppFn(v_e_926_);
if (lean_obj_tag(v___x_932_) == 4)
{
lean_object* v_declName_933_; lean_object* v___x_934_; 
v_declName_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_declName_933_);
lean_dec_ref(v___x_932_);
v___x_934_ = l_Lean_Meta_getCoeFnInfo_x3f___redArg(v_declName_933_, v_a_927_);
lean_dec(v_declName_933_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_958_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_958_ == 0)
{
v___x_937_ = v___x_934_;
v_isShared_938_ = v_isSharedCheck_958_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_934_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_958_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
if (lean_obj_tag(v_a_935_) == 1)
{
lean_object* v_val_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_957_; 
v_val_939_ = lean_ctor_get(v_a_935_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v_a_935_);
if (v_isSharedCheck_957_ == 0)
{
v___x_941_ = v_a_935_;
v_isShared_942_ = v_isSharedCheck_957_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_val_939_);
lean_dec(v_a_935_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_957_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v_numArgs_943_; lean_object* v_coercee_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
v_numArgs_943_ = lean_ctor_get(v_val_939_, 0);
lean_inc(v_numArgs_943_);
v_coercee_944_ = lean_ctor_get(v_val_939_, 1);
lean_inc(v_coercee_944_);
lean_dec(v_val_939_);
v___x_945_ = l_Lean_Expr_getAppNumArgs(v_e_926_);
v___x_946_ = lean_nat_dec_eq(v___x_945_, v_numArgs_943_);
lean_dec(v_numArgs_943_);
if (v___x_946_ == 0)
{
lean_dec(v___x_945_);
lean_dec(v_coercee_944_);
lean_del_object(v___x_941_);
lean_del_object(v___x_937_);
goto v___jp_929_;
}
else
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_952_; 
v___x_947_ = lean_nat_sub(v___x_945_, v_coercee_944_);
lean_dec(v_coercee_944_);
lean_dec(v___x_945_);
v___x_948_ = lean_unsigned_to_nat(1u);
v___x_949_ = lean_nat_sub(v___x_947_, v___x_948_);
lean_dec(v___x_947_);
v___x_950_ = l_Lean_Expr_getRevArg_x21(v_e_926_, v___x_949_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_950_);
v___x_952_ = v___x_941_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_950_);
v___x_952_ = v_reuseFailAlloc_956_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
lean_object* v___x_954_; 
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_952_);
v___x_954_ = v___x_937_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v___x_952_);
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
else
{
lean_del_object(v___x_937_);
lean_dec(v_a_935_);
goto v___jp_929_;
}
}
}
else
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
v_a_959_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_934_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_934_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
else
{
lean_dec_ref(v___x_932_);
goto v___jp_929_;
}
v___jp_929_:
{
lean_object* v___x_930_; lean_object* v___x_931_; 
v___x_930_ = lean_box(0);
v___x_931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_931_, 0, v___x_930_);
return v___x_931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg___boxed(lean_object* v_e_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_e_967_, v_a_968_);
lean_dec(v_a_968_);
lean_dec_ref(v_e_967_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f(lean_object* v_e_971_, lean_object* v_a_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_){
_start:
{
lean_object* v___x_977_; 
v___x_977_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_e_971_, v_a_975_);
return v___x_977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___boxed(lean_object* v_e_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f(v_e_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec_ref(v_e_978_);
return v_res_984_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__6(void){
_start:
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_994_ = lean_box(0);
v___x_995_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__5));
v___x_996_ = l_Lean_mkConst(v___x_995_, v___x_994_);
return v___x_996_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__7(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_997_ = lean_unsigned_to_nat(0u);
v___x_998_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__6, &l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__6_once, _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__6);
v___x_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_998_);
lean_ctor_set(v___x_999_, 1, v___x_997_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__8(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__7, &l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__7_once, _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__7);
v___x_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(lean_object* v_e_1002_){
_start:
{
lean_object* v___x_1003_; uint8_t v___x_1004_; 
v___x_1003_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__2));
v___x_1004_ = l_Lean_Expr_isConstOf(v_e_1002_, v___x_1003_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_Expr_consumeMData(v_e_1002_);
if (lean_obj_tag(v___x_1005_) == 5)
{
lean_object* v_fn_1006_; 
v_fn_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc_ref(v_fn_1006_);
lean_dec_ref(v___x_1005_);
if (lean_obj_tag(v_fn_1006_) == 5)
{
lean_object* v_fn_1007_; 
v_fn_1007_ = lean_ctor_get(v_fn_1006_, 0);
lean_inc_ref(v_fn_1007_);
if (lean_obj_tag(v_fn_1007_) == 5)
{
lean_object* v_fn_1008_; 
v_fn_1008_ = lean_ctor_get(v_fn_1007_, 0);
if (lean_obj_tag(v_fn_1008_) == 4)
{
lean_object* v_declName_1009_; 
v_declName_1009_ = lean_ctor_get(v_fn_1008_, 0);
lean_inc(v_declName_1009_);
if (lean_obj_tag(v_declName_1009_) == 1)
{
lean_object* v_pre_1010_; 
v_pre_1010_ = lean_ctor_get(v_declName_1009_, 0);
lean_inc(v_pre_1010_);
if (lean_obj_tag(v_pre_1010_) == 1)
{
lean_object* v_pre_1011_; 
v_pre_1011_ = lean_ctor_get(v_pre_1010_, 0);
if (lean_obj_tag(v_pre_1011_) == 0)
{
lean_object* v_arg_1012_; lean_object* v_arg_1013_; lean_object* v_str_1014_; lean_object* v_str_1015_; lean_object* v___x_1016_; uint8_t v___x_1017_; 
v_arg_1012_ = lean_ctor_get(v_fn_1006_, 1);
lean_inc_ref(v_arg_1012_);
lean_dec_ref(v_fn_1006_);
v_arg_1013_ = lean_ctor_get(v_fn_1007_, 1);
lean_inc_ref(v_arg_1013_);
lean_dec_ref(v_fn_1007_);
v_str_1014_ = lean_ctor_get(v_declName_1009_, 1);
lean_inc_ref(v_str_1014_);
lean_dec_ref(v_declName_1009_);
v_str_1015_ = lean_ctor_get(v_pre_1010_, 1);
lean_inc_ref(v_str_1015_);
lean_dec_ref(v_pre_1010_);
v___x_1016_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__3));
v___x_1017_ = lean_string_dec_eq(v_str_1015_, v___x_1016_);
lean_dec_ref(v_str_1015_);
if (v___x_1017_ == 0)
{
lean_object* v___x_1018_; 
lean_dec_ref(v_str_1014_);
lean_dec_ref(v_arg_1013_);
lean_dec_ref(v_arg_1012_);
v___x_1018_ = lean_box(0);
return v___x_1018_;
}
else
{
lean_object* v___x_1019_; uint8_t v___x_1020_; 
v___x_1019_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__4));
v___x_1020_ = lean_string_dec_eq(v_str_1014_, v___x_1019_);
lean_dec_ref(v_str_1014_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; 
lean_dec_ref(v_arg_1013_);
lean_dec_ref(v_arg_1012_);
v___x_1021_ = lean_box(0);
return v___x_1021_;
}
else
{
if (lean_obj_tag(v_arg_1012_) == 9)
{
lean_object* v_a_1022_; 
v_a_1022_ = lean_ctor_get(v_arg_1012_, 0);
lean_inc_ref(v_a_1022_);
lean_dec_ref(v_arg_1012_);
if (lean_obj_tag(v_a_1022_) == 0)
{
lean_object* v_val_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1031_; 
v_val_1023_ = lean_ctor_get(v_a_1022_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_a_1022_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1025_ = v_a_1022_;
v_isShared_1026_ = v_isSharedCheck_1031_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_val_1023_);
lean_dec(v_a_1022_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1031_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1027_, 0, v_arg_1013_);
lean_ctor_set(v___x_1027_, 1, v_val_1023_);
if (v_isShared_1026_ == 0)
{
lean_ctor_set_tag(v___x_1025_, 1);
lean_ctor_set(v___x_1025_, 0, v___x_1027_);
v___x_1029_ = v___x_1025_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1027_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
else
{
lean_object* v___x_1032_; 
lean_dec_ref(v_a_1022_);
lean_dec_ref(v_arg_1013_);
v___x_1032_ = lean_box(0);
return v___x_1032_;
}
}
else
{
lean_object* v___x_1033_; 
lean_dec_ref(v_arg_1013_);
lean_dec_ref(v_arg_1012_);
v___x_1033_ = lean_box(0);
return v___x_1033_;
}
}
}
}
else
{
lean_object* v___x_1034_; 
lean_dec_ref(v_pre_1010_);
lean_dec_ref(v_declName_1009_);
lean_dec_ref(v_fn_1007_);
lean_dec_ref(v_fn_1006_);
v___x_1034_ = lean_box(0);
return v___x_1034_;
}
}
else
{
lean_object* v___x_1035_; 
lean_dec_ref(v_declName_1009_);
lean_dec(v_pre_1010_);
lean_dec_ref(v_fn_1007_);
lean_dec_ref(v_fn_1006_);
v___x_1035_ = lean_box(0);
return v___x_1035_;
}
}
else
{
lean_object* v___x_1036_; 
lean_dec(v_declName_1009_);
lean_dec_ref(v_fn_1007_);
lean_dec_ref(v_fn_1006_);
v___x_1036_ = lean_box(0);
return v___x_1036_;
}
}
else
{
lean_object* v___x_1037_; 
lean_dec_ref(v_fn_1007_);
lean_dec_ref(v_fn_1006_);
v___x_1037_ = lean_box(0);
return v___x_1037_;
}
}
else
{
lean_object* v___x_1038_; 
lean_dec_ref(v_fn_1007_);
lean_dec_ref(v_fn_1006_);
v___x_1038_ = lean_box(0);
return v___x_1038_;
}
}
else
{
lean_object* v___x_1039_; 
lean_dec_ref(v_fn_1006_);
v___x_1039_ = lean_box(0);
return v___x_1039_;
}
}
else
{
lean_object* v___x_1040_; 
lean_dec_ref(v___x_1005_);
v___x_1040_ = lean_box(0);
return v___x_1040_;
}
}
else
{
lean_object* v___x_1041_; 
v___x_1041_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__8, &l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__8);
return v___x_1041_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___boxed(lean_object* v_e_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_e_1042_);
lean_dec_ref(v_e_1042_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(lean_object* v_x_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
v___x_1050_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1051_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1050_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1051_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1051_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0___boxed(lean_object* v_x_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v_x_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v_x_1060_);
return v_res_1066_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___closed__1(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___closed__0));
v___x_1069_ = l_Lean_stringToMessageData(v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4(lean_object* v___x_1070_, lean_object* v_expr_1071_, lean_object* v_x_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
if (lean_obj_tag(v_x_1072_) == 0)
{
lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
v_isSharedCheck_1084_ = !lean_is_exclusive(v_x_1072_);
if (v_isSharedCheck_1084_ == 0)
{
lean_object* v_unused_1085_; 
v_unused_1085_ = lean_ctor_get(v_x_1072_, 0);
lean_dec(v_unused_1085_);
v___x_1079_ = v_x_1072_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_dec(v_x_1072_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
lean_ctor_set(v___x_1079_, 0, v___x_1070_);
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1070_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1102_; 
v_a_1086_ = lean_ctor_get(v_x_1072_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_x_1072_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1088_ = v_x_1072_;
v_isShared_1089_ = v_isSharedCheck_1102_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v_x_1072_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1102_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v_expr_1090_; uint8_t v___x_1091_; 
v_expr_1090_ = lean_ctor_get(v_a_1086_, 0);
lean_inc_ref(v_expr_1090_);
lean_dec(v_a_1086_);
v___x_1091_ = lean_expr_eqv(v_expr_1090_, v_expr_1071_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1092_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___closed__1, &l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___closed__1);
v___x_1093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1070_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = l_Lean_MessageData_ofExpr(v_expr_1090_);
v___x_1095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1093_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set_tag(v___x_1088_, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1095_);
v___x_1097_ = v___x_1088_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
else
{
lean_object* v___x_1100_; 
lean_dec_ref(v_expr_1090_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set_tag(v___x_1088_, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1070_);
v___x_1100_ = v___x_1088_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v___x_1070_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___boxed(lean_object* v___x_1103_, lean_object* v_expr_1104_, lean_object* v_x_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4(v___x_1103_, v_expr_1104_, v_x_1105_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_);
lean_dec(v___y_1109_);
lean_dec_ref(v___y_1108_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec_ref(v_expr_1104_);
return v_res_1111_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0_spec__0(lean_object* v_e_1112_){
_start:
{
if (lean_obj_tag(v_e_1112_) == 0)
{
uint8_t v___x_1113_; 
v___x_1113_ = 2;
return v___x_1113_;
}
else
{
uint8_t v___x_1114_; 
v___x_1114_ = 0;
return v___x_1114_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0_spec__0___boxed(lean_object* v_e_1115_){
_start:
{
uint8_t v_res_1116_; lean_object* v_r_1117_; 
v_res_1116_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0_spec__0(v_e_1115_);
lean_dec_ref(v_e_1115_);
v_r_1117_ = lean_box(v_res_1116_);
return v_r_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(lean_object* v_cls_1118_, uint8_t v_collapsed_1119_, lean_object* v_tag_1120_, lean_object* v_opts_1121_, uint8_t v_clsEnabled_1122_, lean_object* v_oldTraces_1123_, lean_object* v_msg_1124_, lean_object* v_resStartStop_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v_fst_1131_; lean_object* v_snd_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1230_; 
v_fst_1131_ = lean_ctor_get(v_resStartStop_1125_, 0);
v_snd_1132_ = lean_ctor_get(v_resStartStop_1125_, 1);
v_isSharedCheck_1230_ = !lean_is_exclusive(v_resStartStop_1125_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1134_ = v_resStartStop_1125_;
v_isShared_1135_ = v_isSharedCheck_1230_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_snd_1132_);
lean_inc(v_fst_1131_);
lean_dec(v_resStartStop_1125_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1230_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___y_1137_; lean_object* v___y_1138_; lean_object* v_data_1139_; lean_object* v_fst_1150_; lean_object* v_snd_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1229_; 
v_fst_1150_ = lean_ctor_get(v_snd_1132_, 0);
v_snd_1151_ = lean_ctor_get(v_snd_1132_, 1);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_snd_1132_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1153_ = v_snd_1132_;
v_isShared_1154_ = v_isSharedCheck_1229_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_snd_1151_);
lean_inc(v_fst_1150_);
lean_dec(v_snd_1132_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1229_;
goto v_resetjp_1152_;
}
v___jp_1136_:
{
lean_object* v___x_1140_; 
lean_inc(v___y_1137_);
v___x_1140_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3(v_oldTraces_1123_, v_data_1139_, v___y_1137_, v___y_1138_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v___x_1141_; 
lean_dec_ref(v___x_1140_);
v___x_1141_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4___redArg(v_fst_1131_);
return v___x_1141_;
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_dec(v_fst_1131_);
v_a_1142_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1140_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1140_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
v_resetjp_1152_:
{
lean_object* v___x_1155_; uint8_t v___x_1156_; lean_object* v___y_1158_; lean_object* v_a_1159_; uint8_t v___y_1183_; double v___y_1214_; 
v___x_1155_ = l_Lean_trace_profiler;
v___x_1156_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_opts_1121_, v___x_1155_);
if (v___x_1156_ == 0)
{
v___y_1183_ = v___x_1156_;
goto v___jp_1182_;
}
else
{
lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1219_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1220_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_opts_1121_, v___x_1219_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; lean_object* v___x_1222_; double v___x_1223_; double v___x_1224_; double v___x_1225_; 
v___x_1221_ = l_Lean_trace_profiler_threshold;
v___x_1222_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__5(v_opts_1121_, v___x_1221_);
v___x_1223_ = lean_float_of_nat(v___x_1222_);
v___x_1224_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__5);
v___x_1225_ = lean_float_div(v___x_1223_, v___x_1224_);
v___y_1214_ = v___x_1225_;
goto v___jp_1213_;
}
else
{
lean_object* v___x_1226_; lean_object* v___x_1227_; double v___x_1228_; 
v___x_1226_ = l_Lean_trace_profiler_threshold;
v___x_1227_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__5(v_opts_1121_, v___x_1226_);
v___x_1228_ = lean_float_of_nat(v___x_1227_);
v___y_1214_ = v___x_1228_;
goto v___jp_1213_;
}
}
v___jp_1157_:
{
uint8_t v_result_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
v_result_1160_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0_spec__0(v_fst_1131_);
v___x_1161_ = l_Lean_TraceResult_toEmoji(v_result_1160_);
v___x_1162_ = l_Lean_stringToMessageData(v___x_1161_);
v___x_1163_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1);
if (v_isShared_1154_ == 0)
{
lean_ctor_set_tag(v___x_1153_, 7);
lean_ctor_set(v___x_1153_, 1, v___x_1163_);
lean_ctor_set(v___x_1153_, 0, v___x_1162_);
v___x_1165_ = v___x_1153_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v___x_1163_);
v___x_1165_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v_m_1167_; 
if (v_isShared_1135_ == 0)
{
lean_ctor_set_tag(v___x_1134_, 7);
lean_ctor_set(v___x_1134_, 1, v_a_1159_);
lean_ctor_set(v___x_1134_, 0, v___x_1165_);
v_m_1167_ = v___x_1134_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v___x_1165_);
lean_ctor_set(v_reuseFailAlloc_1175_, 1, v_a_1159_);
v_m_1167_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; double v___x_1170_; lean_object* v_data_1171_; 
v___x_1168_ = lean_box(v_result_1160_);
v___x_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
v___x_1170_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2);
lean_inc_ref(v_tag_1120_);
lean_inc_ref(v___x_1169_);
lean_inc(v_cls_1118_);
v_data_1171_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1171_, 0, v_cls_1118_);
lean_ctor_set(v_data_1171_, 1, v___x_1169_);
lean_ctor_set(v_data_1171_, 2, v_tag_1120_);
lean_ctor_set_float(v_data_1171_, sizeof(void*)*3, v___x_1170_);
lean_ctor_set_float(v_data_1171_, sizeof(void*)*3 + 8, v___x_1170_);
lean_ctor_set_uint8(v_data_1171_, sizeof(void*)*3 + 16, v_collapsed_1119_);
if (v___x_1156_ == 0)
{
lean_dec_ref(v___x_1169_);
lean_dec(v_snd_1151_);
lean_dec(v_fst_1150_);
lean_dec_ref(v_tag_1120_);
lean_dec(v_cls_1118_);
v___y_1137_ = v___y_1158_;
v___y_1138_ = v_m_1167_;
v_data_1139_ = v_data_1171_;
goto v___jp_1136_;
}
else
{
lean_object* v_data_1172_; double v___x_1173_; double v___x_1174_; 
lean_dec_ref(v_data_1171_);
v_data_1172_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1172_, 0, v_cls_1118_);
lean_ctor_set(v_data_1172_, 1, v___x_1169_);
lean_ctor_set(v_data_1172_, 2, v_tag_1120_);
v___x_1173_ = lean_unbox_float(v_fst_1150_);
lean_dec(v_fst_1150_);
lean_ctor_set_float(v_data_1172_, sizeof(void*)*3, v___x_1173_);
v___x_1174_ = lean_unbox_float(v_snd_1151_);
lean_dec(v_snd_1151_);
lean_ctor_set_float(v_data_1172_, sizeof(void*)*3 + 8, v___x_1174_);
lean_ctor_set_uint8(v_data_1172_, sizeof(void*)*3 + 16, v_collapsed_1119_);
v___y_1137_ = v___y_1158_;
v___y_1138_ = v_m_1167_;
v_data_1139_ = v_data_1172_;
goto v___jp_1136_;
}
}
}
}
v___jp_1177_:
{
lean_object* v_ref_1178_; lean_object* v___x_1179_; 
v_ref_1178_ = lean_ctor_get(v___y_1128_, 5);
lean_inc(v___y_1129_);
lean_inc_ref(v___y_1128_);
lean_inc(v___y_1127_);
lean_inc_ref(v___y_1126_);
lean_inc(v_fst_1131_);
v___x_1179_ = lean_apply_6(v_msg_1124_, v_fst_1131_, v___y_1126_, v___y_1127_, v___y_1128_, v___y_1129_, lean_box(0));
if (lean_obj_tag(v___x_1179_) == 0)
{
lean_object* v_a_1180_; 
v_a_1180_ = lean_ctor_get(v___x_1179_, 0);
lean_inc(v_a_1180_);
lean_dec_ref(v___x_1179_);
v___y_1158_ = v_ref_1178_;
v_a_1159_ = v_a_1180_;
goto v___jp_1157_;
}
else
{
lean_object* v___x_1181_; 
lean_dec_ref(v___x_1179_);
v___x_1181_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__4);
v___y_1158_ = v_ref_1178_;
v_a_1159_ = v___x_1181_;
goto v___jp_1157_;
}
}
v___jp_1182_:
{
if (v_clsEnabled_1122_ == 0)
{
if (v___y_1183_ == 0)
{
lean_object* v___x_1184_; lean_object* v_traceState_1185_; lean_object* v_env_1186_; lean_object* v_nextMacroScope_1187_; lean_object* v_ngen_1188_; lean_object* v_auxDeclNGen_1189_; lean_object* v_cache_1190_; lean_object* v_messages_1191_; lean_object* v_infoState_1192_; lean_object* v_snapshotTasks_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1212_; 
lean_del_object(v___x_1153_);
lean_dec(v_snd_1151_);
lean_dec(v_fst_1150_);
lean_del_object(v___x_1134_);
lean_dec_ref(v_msg_1124_);
lean_dec_ref(v_tag_1120_);
lean_dec(v_cls_1118_);
v___x_1184_ = lean_st_ref_take(v___y_1129_);
v_traceState_1185_ = lean_ctor_get(v___x_1184_, 4);
v_env_1186_ = lean_ctor_get(v___x_1184_, 0);
v_nextMacroScope_1187_ = lean_ctor_get(v___x_1184_, 1);
v_ngen_1188_ = lean_ctor_get(v___x_1184_, 2);
v_auxDeclNGen_1189_ = lean_ctor_get(v___x_1184_, 3);
v_cache_1190_ = lean_ctor_get(v___x_1184_, 5);
v_messages_1191_ = lean_ctor_get(v___x_1184_, 6);
v_infoState_1192_ = lean_ctor_get(v___x_1184_, 7);
v_snapshotTasks_1193_ = lean_ctor_get(v___x_1184_, 8);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1195_ = v___x_1184_;
v_isShared_1196_ = v_isSharedCheck_1212_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_snapshotTasks_1193_);
lean_inc(v_infoState_1192_);
lean_inc(v_messages_1191_);
lean_inc(v_cache_1190_);
lean_inc(v_traceState_1185_);
lean_inc(v_auxDeclNGen_1189_);
lean_inc(v_ngen_1188_);
lean_inc(v_nextMacroScope_1187_);
lean_inc(v_env_1186_);
lean_dec(v___x_1184_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1212_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
uint64_t v_tid_1197_; lean_object* v_traces_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1211_; 
v_tid_1197_ = lean_ctor_get_uint64(v_traceState_1185_, sizeof(void*)*1);
v_traces_1198_ = lean_ctor_get(v_traceState_1185_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_traceState_1185_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1200_ = v_traceState_1185_;
v_isShared_1201_ = v_isSharedCheck_1211_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_traces_1198_);
lean_dec(v_traceState_1185_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1211_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1202_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1123_, v_traces_1198_);
lean_dec_ref(v_traces_1198_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1202_);
v___x_1204_ = v___x_1200_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1202_);
lean_ctor_set_uint64(v_reuseFailAlloc_1210_, sizeof(void*)*1, v_tid_1197_);
v___x_1204_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1206_; 
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 4, v___x_1204_);
v___x_1206_ = v___x_1195_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_env_1186_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_nextMacroScope_1187_);
lean_ctor_set(v_reuseFailAlloc_1209_, 2, v_ngen_1188_);
lean_ctor_set(v_reuseFailAlloc_1209_, 3, v_auxDeclNGen_1189_);
lean_ctor_set(v_reuseFailAlloc_1209_, 4, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1209_, 5, v_cache_1190_);
lean_ctor_set(v_reuseFailAlloc_1209_, 6, v_messages_1191_);
lean_ctor_set(v_reuseFailAlloc_1209_, 7, v_infoState_1192_);
lean_ctor_set(v_reuseFailAlloc_1209_, 8, v_snapshotTasks_1193_);
v___x_1206_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1207_ = lean_st_ref_set(v___y_1129_, v___x_1206_);
v___x_1208_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__4___redArg(v_fst_1131_);
return v___x_1208_;
}
}
}
}
}
else
{
goto v___jp_1177_;
}
}
else
{
goto v___jp_1177_;
}
}
v___jp_1213_:
{
double v___x_1215_; double v___x_1216_; double v___x_1217_; uint8_t v___x_1218_; 
v___x_1215_ = lean_unbox_float(v_snd_1151_);
v___x_1216_ = lean_unbox_float(v_fst_1150_);
v___x_1217_ = lean_float_sub(v___x_1215_, v___x_1216_);
v___x_1218_ = lean_float_decLt(v___y_1214_, v___x_1217_);
v___y_1183_ = v___x_1218_;
goto v___jp_1182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0___boxed(lean_object* v_cls_1231_, lean_object* v_collapsed_1232_, lean_object* v_tag_1233_, lean_object* v_opts_1234_, lean_object* v_clsEnabled_1235_, lean_object* v_oldTraces_1236_, lean_object* v_msg_1237_, lean_object* v_resStartStop_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_){
_start:
{
uint8_t v_collapsed_boxed_1244_; uint8_t v_clsEnabled_boxed_1245_; lean_object* v_res_1246_; 
v_collapsed_boxed_1244_ = lean_unbox(v_collapsed_1232_);
v_clsEnabled_boxed_1245_ = lean_unbox(v_clsEnabled_1235_);
v_res_1246_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v_cls_1231_, v_collapsed_boxed_1244_, v_tag_1233_, v_opts_1234_, v_clsEnabled_boxed_1245_, v_oldTraces_1236_, v_msg_1237_, v_resStartStop_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec_ref(v_opts_1234_);
return v_res_1246_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___closed__1(void){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; 
v___x_1248_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_splittingProcedure___closed__0));
v___x_1249_ = l_Lean_stringToMessageData(v___x_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure(lean_object* v_expr_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_){
_start:
{
lean_object* v_a_1262_; lean_object* v_a_1272_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1286_; uint8_t v___y_1287_; lean_object* v___y_1288_; uint8_t v___y_1289_; lean_object* v_a_1290_; lean_object* v___y_1300_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; uint8_t v___y_1305_; uint8_t v___y_1306_; lean_object* v___y_1307_; lean_object* v_a_1308_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; uint8_t v___y_1316_; lean_object* v___y_1317_; uint8_t v___y_1318_; lean_object* v_a_1319_; lean_object* v___y_1322_; lean_object* v___y_1323_; lean_object* v___y_1324_; lean_object* v___y_1325_; lean_object* v___y_1326_; uint8_t v___y_1327_; uint8_t v___y_1328_; lean_object* v___y_1329_; lean_object* v_a_1330_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; uint8_t v___y_1339_; lean_object* v___y_1340_; uint8_t v___y_1341_; uint8_t v___y_1342_; lean_object* v___y_1346_; lean_object* v___y_1347_; lean_object* v___y_1348_; lean_object* v___y_1349_; lean_object* v___y_1350_; uint8_t v___y_1351_; uint8_t v___y_1352_; lean_object* v___y_1353_; lean_object* v_a_1354_; lean_object* v___y_1358_; lean_object* v___y_1359_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; uint8_t v___y_1363_; lean_object* v___y_1364_; uint8_t v___y_1365_; lean_object* v_a_1366_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; uint8_t v___y_1384_; uint8_t v___y_1385_; lean_object* v___y_1386_; lean_object* v_a_1387_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; uint8_t v___y_1395_; lean_object* v___y_1396_; uint8_t v___y_1397_; lean_object* v_a_1398_; lean_object* v___y_1401_; lean_object* v___y_1402_; lean_object* v___y_1403_; lean_object* v___y_1404_; lean_object* v___y_1405_; uint8_t v___y_1406_; uint8_t v___y_1407_; lean_object* v___y_1408_; lean_object* v_a_1409_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1417_; uint8_t v___y_1418_; lean_object* v___y_1419_; uint8_t v___y_1420_; uint8_t v___y_1421_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1429_; uint8_t v___y_1430_; uint8_t v___y_1431_; lean_object* v___y_1432_; lean_object* v_a_1433_; lean_object* v___y_1437_; uint8_t v___y_1438_; uint8_t v___y_1439_; uint8_t v___y_1445_; lean_object* v_a_1446_; lean_object* v___y_1450_; uint8_t v___y_1451_; uint8_t v___y_1452_; uint8_t v___y_1458_; lean_object* v_a_1459_; 
if (lean_obj_tag(v_expr_1250_) == 5)
{
lean_object* v_fn_1462_; 
v_fn_1462_ = lean_ctor_get(v_expr_1250_, 0);
if (lean_obj_tag(v_fn_1462_) == 5)
{
lean_object* v_arg_1463_; lean_object* v_fn_1464_; lean_object* v_arg_1465_; lean_object* v___x_1466_; 
v_arg_1463_ = lean_ctor_get(v_expr_1250_, 1);
v_fn_1464_ = lean_ctor_get(v_fn_1462_, 0);
v_arg_1465_ = lean_ctor_get(v_fn_1462_, 1);
lean_inc(v_a_1254_);
lean_inc_ref(v_a_1253_);
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
lean_inc_ref(v_fn_1464_);
v___x_1466_ = lean_infer_type(v_fn_1464_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1466_) == 0)
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_2316_; 
v_a_1467_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_1469_ = v___x_1466_;
v_isShared_1470_ = v_isSharedCheck_2316_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1466_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_2316_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
if (lean_obj_tag(v_a_1467_) == 7)
{
lean_object* v_body_1478_; 
v_body_1478_ = lean_ctor_get(v_a_1467_, 2);
lean_inc_ref(v_body_1478_);
if (lean_obj_tag(v_body_1478_) == 7)
{
lean_object* v_binderType_1479_; lean_object* v_binderType_1480_; lean_object* v_body_1481_; lean_object* v___y_1483_; uint8_t v___y_1484_; uint8_t v___y_1485_; uint8_t v___y_1524_; lean_object* v_a_1525_; lean_object* v___y_1529_; uint8_t v___y_1530_; uint8_t v___y_1531_; uint8_t v___y_1568_; lean_object* v_a_1569_; uint8_t v___y_1573_; lean_object* v___y_1574_; lean_object* v___y_1577_; lean_object* v___y_1578_; lean_object* v___y_1579_; uint8_t v___y_1580_; uint8_t v___y_1581_; lean_object* v___y_1599_; lean_object* v___y_1600_; uint8_t v___y_1601_; lean_object* v_a_1602_; lean_object* v___y_1606_; lean_object* v___y_1607_; uint8_t v___y_1608_; lean_object* v___y_1609_; lean_object* v___y_1612_; uint8_t v___y_1613_; uint8_t v___y_1614_; uint8_t v___y_1653_; lean_object* v_a_1654_; lean_object* v___y_1658_; uint8_t v___y_1659_; uint8_t v___y_1660_; uint8_t v___y_1697_; lean_object* v_a_1698_; uint8_t v___y_1702_; lean_object* v___y_1703_; lean_object* v___y_1706_; lean_object* v___y_1707_; lean_object* v___y_1708_; uint8_t v___y_1709_; uint8_t v___y_1710_; lean_object* v___y_1728_; lean_object* v___y_1729_; uint8_t v___y_1730_; lean_object* v_a_1731_; lean_object* v___y_1735_; lean_object* v___y_1736_; uint8_t v___y_1737_; lean_object* v___y_1738_; lean_object* v___y_1741_; lean_object* v___y_1742_; lean_object* v___y_1743_; lean_object* v___y_1744_; lean_object* v___y_1745_; lean_object* v___y_1746_; uint8_t v___y_1747_; lean_object* v___y_1748_; uint8_t v___y_1749_; uint8_t v___y_1750_; lean_object* v___y_1789_; lean_object* v___y_1790_; lean_object* v___y_1791_; lean_object* v___y_1792_; lean_object* v___y_1793_; uint8_t v___y_1794_; uint8_t v___y_1795_; lean_object* v___y_1796_; lean_object* v_a_1797_; lean_object* v___y_1801_; lean_object* v___y_1802_; lean_object* v___y_1803_; lean_object* v___y_1804_; lean_object* v___y_1805_; lean_object* v___y_1806_; uint8_t v___y_1807_; lean_object* v___y_1808_; uint8_t v___y_1809_; uint8_t v___y_1810_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; uint8_t v___y_1852_; uint8_t v___y_1853_; lean_object* v___y_1854_; lean_object* v_a_1855_; lean_object* v___y_1859_; lean_object* v___y_1860_; lean_object* v___y_1861_; lean_object* v___y_1862_; lean_object* v___y_1863_; uint8_t v___y_1864_; lean_object* v___y_1865_; uint8_t v___y_1866_; lean_object* v___y_1867_; lean_object* v___y_1871_; lean_object* v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; lean_object* v___y_1878_; uint8_t v___y_1879_; lean_object* v___y_1880_; uint8_t v___y_1881_; uint8_t v___y_1882_; lean_object* v___y_1900_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; uint8_t v___y_1907_; uint8_t v___y_1908_; lean_object* v___y_1909_; lean_object* v_a_1910_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; uint8_t v___y_1921_; lean_object* v___y_1922_; uint8_t v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; uint8_t v___y_1934_; lean_object* v___y_1935_; uint8_t v___y_1936_; uint8_t v___y_1937_; lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_1980_; uint8_t v___y_1981_; uint8_t v___y_1982_; lean_object* v___y_1983_; lean_object* v_a_1984_; lean_object* v___y_1988_; lean_object* v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_1991_; lean_object* v___y_1992_; lean_object* v___y_1993_; uint8_t v___y_1994_; lean_object* v___y_1995_; uint8_t v___y_1996_; uint8_t v___y_1997_; lean_object* v___y_2034_; lean_object* v___y_2035_; lean_object* v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; uint8_t v___y_2039_; uint8_t v___y_2040_; lean_object* v___y_2041_; lean_object* v_a_2042_; lean_object* v___y_2046_; lean_object* v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; lean_object* v___y_2050_; uint8_t v___y_2051_; lean_object* v___y_2052_; uint8_t v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2058_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v___y_2064_; lean_object* v___y_2065_; uint8_t v___y_2066_; lean_object* v___y_2067_; uint8_t v___y_2068_; uint8_t v___y_2069_; lean_object* v___y_2087_; lean_object* v___y_2088_; lean_object* v___y_2089_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; uint8_t v___y_2094_; uint8_t v___y_2095_; lean_object* v___y_2096_; lean_object* v_a_2097_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; lean_object* v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; uint8_t v___y_2108_; lean_object* v___y_2109_; uint8_t v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2115_; lean_object* v___y_2116_; lean_object* v___y_2117_; uint8_t v___y_2118_; uint8_t v___y_2119_; lean_object* v___y_2120_; uint8_t v___y_2202_; uint8_t v___x_2314_; 
lean_del_object(v___x_1469_);
v_binderType_1479_ = lean_ctor_get(v_a_1467_, 1);
lean_inc_ref(v_binderType_1479_);
lean_dec_ref(v_a_1467_);
v_binderType_1480_ = lean_ctor_get(v_body_1478_, 1);
lean_inc_ref(v_binderType_1480_);
v_body_1481_ = lean_ctor_get(v_body_1478_, 2);
lean_inc_ref(v_body_1481_);
lean_dec_ref(v_body_1478_);
v___x_2314_ = l_Lean_Expr_hasLooseBVars(v_binderType_1480_);
if (v___x_2314_ == 0)
{
uint8_t v___x_2315_; 
v___x_2315_ = l_Lean_Expr_hasLooseBVars(v_body_1481_);
lean_dec_ref(v_body_1481_);
v___y_2202_ = v___x_2315_;
goto v___jp_2201_;
}
else
{
lean_dec_ref(v_body_1481_);
v___y_2202_ = v___x_2314_;
goto v___jp_2201_;
}
v___jp_1482_:
{
if (v___y_1485_ == 0)
{
lean_object* v___x_1486_; 
lean_dec_ref(v___y_1483_);
v___x_1486_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1465_);
if (lean_obj_tag(v___x_1486_) == 1)
{
lean_object* v_val_1487_; lean_object* v_snd_1488_; lean_object* v___x_1489_; 
v_val_1487_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_val_1487_);
lean_dec_ref(v___x_1486_);
v_snd_1488_ = lean_ctor_get(v_val_1487_, 1);
lean_inc(v_snd_1488_);
lean_dec(v_val_1487_);
v___x_1489_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1463_, v_a_1254_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v_a_1490_; 
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1490_);
lean_dec_ref(v___x_1489_);
if (lean_obj_tag(v_a_1490_) == 1)
{
lean_object* v_val_1491_; lean_object* v___x_1492_; 
v_val_1491_ = lean_ctor_get(v_a_1490_, 0);
lean_inc(v_val_1491_);
lean_dec_ref(v_a_1490_);
lean_inc(v_a_1254_);
lean_inc_ref(v_a_1253_);
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
v___x_1492_ = lean_infer_type(v_val_1491_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1492_) == 0)
{
lean_object* v_a_1493_; lean_object* v___x_1494_; 
v_a_1493_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_a_1493_);
lean_dec_ref(v___x_1492_);
v___x_1494_ = l_Lean_Meta_mkNumeral(v_a_1493_, v_snd_1488_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1496_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1495_);
lean_dec_ref(v___x_1494_);
v___x_1496_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1495_, v_binderType_1479_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_object* v_a_1497_; lean_object* v___x_1498_; 
v_a_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1497_);
lean_dec_ref(v___x_1496_);
lean_inc_ref(v_arg_1465_);
v___x_1498_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1465_, v_a_1497_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v_a_1499_; 
v_a_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_a_1499_);
lean_dec_ref(v___x_1498_);
if (lean_obj_tag(v_a_1499_) == 1)
{
lean_object* v_val_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v_val_1500_ = lean_ctor_get(v_a_1499_, 0);
lean_inc(v_val_1500_);
lean_dec_ref(v_a_1499_);
v___x_1501_ = lean_box(0);
lean_inc_ref(v_fn_1464_);
v___x_1502_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1502_, 0, v_fn_1464_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
lean_ctor_set_uint8(v___x_1502_, sizeof(void*)*2, v___y_1484_);
v___x_1503_ = l_Lean_Meta_Simp_mkCongr(v___x_1502_, v_val_1500_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1505_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1504_);
lean_dec_ref(v___x_1503_);
lean_inc_ref(v_arg_1463_);
v___x_1505_ = l_Lean_Meta_Simp_mkCongrFun(v_a_1504_, v_arg_1463_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1505_) == 0)
{
lean_dec_ref(v_expr_1250_);
return v___x_1505_;
}
else
{
lean_object* v_a_1506_; 
v_a_1506_ = lean_ctor_get(v___x_1505_, 0);
lean_inc(v_a_1506_);
lean_dec_ref(v___x_1505_);
v___y_1445_ = v___y_1484_;
v_a_1446_ = v_a_1506_;
goto v___jp_1444_;
}
}
else
{
lean_object* v_a_1507_; 
v_a_1507_ = lean_ctor_get(v___x_1503_, 0);
lean_inc(v_a_1507_);
lean_dec_ref(v___x_1503_);
v___y_1445_ = v___y_1484_;
v_a_1446_ = v_a_1507_;
goto v___jp_1444_;
}
}
else
{
lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v_a_1510_; 
lean_dec(v_a_1499_);
v___x_1508_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1509_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1508_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_a_1510_);
lean_dec_ref(v___x_1509_);
v___y_1445_ = v___y_1484_;
v_a_1446_ = v_a_1510_;
goto v___jp_1444_;
}
}
else
{
lean_object* v_a_1511_; 
v_a_1511_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_a_1511_);
lean_dec_ref(v___x_1498_);
v___y_1445_ = v___y_1484_;
v_a_1446_ = v_a_1511_;
goto v___jp_1444_;
}
}
else
{
lean_object* v_a_1512_; 
v_a_1512_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_a_1512_);
lean_dec_ref(v___x_1496_);
v___y_1445_ = v___y_1484_;
v_a_1446_ = v_a_1512_;
goto v___jp_1444_;
}
}
else
{
lean_object* v_a_1513_; 
lean_dec_ref(v_binderType_1479_);
v_a_1513_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_a_1513_);
lean_dec_ref(v___x_1494_);
v___y_1445_ = v___y_1484_;
v_a_1446_ = v_a_1513_;
goto v___jp_1444_;
}
}
else
{
lean_object* v_a_1514_; 
lean_dec(v_snd_1488_);
lean_dec_ref(v_binderType_1479_);
v_a_1514_ = lean_ctor_get(v___x_1492_, 0);
lean_inc(v_a_1514_);
lean_dec_ref(v___x_1492_);
v___y_1445_ = v___y_1484_;
v_a_1446_ = v_a_1514_;
goto v___jp_1444_;
}
}
else
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v_a_1517_; 
lean_dec(v_a_1490_);
lean_dec(v_snd_1488_);
lean_dec_ref(v_binderType_1479_);
v___x_1515_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1516_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1515_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_a_1517_);
lean_dec_ref(v___x_1516_);
v___y_1445_ = v___y_1484_;
v_a_1446_ = v_a_1517_;
goto v___jp_1444_;
}
}
else
{
lean_object* v_a_1518_; 
lean_dec(v_snd_1488_);
lean_dec_ref(v_binderType_1479_);
v_a_1518_ = lean_ctor_get(v___x_1489_, 0);
lean_inc(v_a_1518_);
lean_dec_ref(v___x_1489_);
v___y_1445_ = v___y_1484_;
v_a_1446_ = v_a_1518_;
goto v___jp_1444_;
}
}
else
{
lean_object* v___x_1519_; 
lean_dec_ref(v_binderType_1479_);
v___x_1519_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1486_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
lean_dec(v___x_1486_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v_a_1520_; 
lean_dec_ref(v_expr_1250_);
v_a_1520_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1520_);
lean_dec_ref(v___x_1519_);
v_a_1262_ = v_a_1520_;
goto v___jp_1261_;
}
else
{
lean_object* v_a_1521_; 
v_a_1521_ = lean_ctor_get(v___x_1519_, 0);
lean_inc(v_a_1521_);
lean_dec_ref(v___x_1519_);
v___y_1445_ = v___y_1484_;
v_a_1446_ = v_a_1521_;
goto v___jp_1444_;
}
}
}
else
{
lean_object* v___x_1522_; 
lean_dec_ref(v_binderType_1479_);
lean_dec_ref(v_expr_1250_);
v___x_1522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1522_, 0, v___y_1483_);
return v___x_1522_;
}
}
v___jp_1523_:
{
uint8_t v___x_1526_; 
v___x_1526_ = l_Lean_Exception_isInterrupt(v_a_1525_);
if (v___x_1526_ == 0)
{
uint8_t v___x_1527_; 
lean_inc_ref(v_a_1525_);
v___x_1527_ = l_Lean_Exception_isRuntime(v_a_1525_);
v___y_1483_ = v_a_1525_;
v___y_1484_ = v___y_1524_;
v___y_1485_ = v___x_1527_;
goto v___jp_1482_;
}
else
{
v___y_1483_ = v_a_1525_;
v___y_1484_ = v___y_1524_;
v___y_1485_ = v___x_1526_;
goto v___jp_1482_;
}
}
v___jp_1528_:
{
if (v___y_1531_ == 0)
{
lean_object* v___x_1532_; 
lean_dec_ref(v___y_1529_);
v___x_1532_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1463_);
if (lean_obj_tag(v___x_1532_) == 1)
{
lean_object* v_val_1533_; lean_object* v_snd_1534_; lean_object* v___x_1535_; 
v_val_1533_ = lean_ctor_get(v___x_1532_, 0);
lean_inc(v_val_1533_);
lean_dec_ref(v___x_1532_);
v_snd_1534_ = lean_ctor_get(v_val_1533_, 1);
lean_inc(v_snd_1534_);
lean_dec(v_val_1533_);
v___x_1535_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1465_, v_a_1254_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref(v___x_1535_);
if (lean_obj_tag(v_a_1536_) == 1)
{
lean_object* v_val_1537_; lean_object* v___x_1538_; 
v_val_1537_ = lean_ctor_get(v_a_1536_, 0);
lean_inc(v_val_1537_);
lean_dec_ref(v_a_1536_);
lean_inc(v_a_1254_);
lean_inc_ref(v_a_1253_);
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
v___x_1538_ = lean_infer_type(v_val_1537_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v___x_1540_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1539_);
lean_dec_ref(v___x_1538_);
v___x_1540_ = l_Lean_Meta_mkNumeral(v_a_1539_, v_snd_1534_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1542_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1541_);
lean_dec_ref(v___x_1540_);
lean_inc_ref(v_binderType_1479_);
v___x_1542_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1541_, v_binderType_1479_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_a_1543_; lean_object* v___x_1544_; 
v_a_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1543_);
lean_dec_ref(v___x_1542_);
lean_inc_ref(v_arg_1463_);
v___x_1544_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1463_, v_a_1543_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref(v___x_1544_);
if (lean_obj_tag(v_a_1545_) == 1)
{
lean_object* v_val_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v_val_1546_ = lean_ctor_get(v_a_1545_, 0);
lean_inc(v_val_1546_);
lean_dec_ref(v_a_1545_);
lean_inc_ref(v_arg_1465_);
lean_inc_ref(v_fn_1464_);
v___x_1547_ = l_Lean_Expr_app___override(v_fn_1464_, v_arg_1465_);
v___x_1548_ = lean_box(0);
v___x_1549_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1549_, 0, v___x_1547_);
lean_ctor_set(v___x_1549_, 1, v___x_1548_);
lean_ctor_set_uint8(v___x_1549_, sizeof(void*)*2, v___y_1530_);
v___x_1550_ = l_Lean_Meta_Simp_mkCongr(v___x_1549_, v_val_1546_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_dec_ref(v_binderType_1479_);
lean_dec_ref(v_expr_1250_);
return v___x_1550_;
}
else
{
lean_object* v_a_1551_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_a_1551_);
lean_dec_ref(v___x_1550_);
v___y_1524_ = v___y_1530_;
v_a_1525_ = v_a_1551_;
goto v___jp_1523_;
}
}
else
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v_a_1554_; 
lean_dec(v_a_1545_);
v___x_1552_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1553_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1552_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
lean_inc(v_a_1554_);
lean_dec_ref(v___x_1553_);
v___y_1524_ = v___y_1530_;
v_a_1525_ = v_a_1554_;
goto v___jp_1523_;
}
}
else
{
lean_object* v_a_1555_; 
v_a_1555_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1555_);
lean_dec_ref(v___x_1544_);
v___y_1524_ = v___y_1530_;
v_a_1525_ = v_a_1555_;
goto v___jp_1523_;
}
}
else
{
lean_object* v_a_1556_; 
v_a_1556_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_a_1556_);
lean_dec_ref(v___x_1542_);
v___y_1524_ = v___y_1530_;
v_a_1525_ = v_a_1556_;
goto v___jp_1523_;
}
}
else
{
lean_object* v_a_1557_; 
v_a_1557_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_a_1557_);
lean_dec_ref(v___x_1540_);
v___y_1524_ = v___y_1530_;
v_a_1525_ = v_a_1557_;
goto v___jp_1523_;
}
}
else
{
lean_object* v_a_1558_; 
lean_dec(v_snd_1534_);
v_a_1558_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1558_);
lean_dec_ref(v___x_1538_);
v___y_1524_ = v___y_1530_;
v_a_1525_ = v_a_1558_;
goto v___jp_1523_;
}
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v_a_1561_; 
lean_dec(v_a_1536_);
lean_dec(v_snd_1534_);
v___x_1559_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1560_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1559_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v_a_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_a_1561_);
lean_dec_ref(v___x_1560_);
v___y_1524_ = v___y_1530_;
v_a_1525_ = v_a_1561_;
goto v___jp_1523_;
}
}
else
{
lean_object* v_a_1562_; 
lean_dec(v_snd_1534_);
v_a_1562_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1562_);
lean_dec_ref(v___x_1535_);
v___y_1524_ = v___y_1530_;
v_a_1525_ = v_a_1562_;
goto v___jp_1523_;
}
}
else
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1532_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
lean_dec(v___x_1532_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; 
lean_dec_ref(v_binderType_1479_);
lean_dec_ref(v_expr_1250_);
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1564_);
lean_dec_ref(v___x_1563_);
v_a_1262_ = v_a_1564_;
goto v___jp_1261_;
}
else
{
lean_object* v_a_1565_; 
v_a_1565_ = lean_ctor_get(v___x_1563_, 0);
lean_inc(v_a_1565_);
lean_dec_ref(v___x_1563_);
v___y_1524_ = v___y_1530_;
v_a_1525_ = v_a_1565_;
goto v___jp_1523_;
}
}
}
else
{
lean_object* v___x_1566_; 
lean_dec_ref(v_binderType_1479_);
lean_dec_ref(v_expr_1250_);
v___x_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___y_1529_);
return v___x_1566_;
}
}
v___jp_1567_:
{
uint8_t v___x_1570_; 
v___x_1570_ = l_Lean_Exception_isInterrupt(v_a_1569_);
if (v___x_1570_ == 0)
{
uint8_t v___x_1571_; 
lean_inc_ref(v_a_1569_);
v___x_1571_ = l_Lean_Exception_isRuntime(v_a_1569_);
v___y_1529_ = v_a_1569_;
v___y_1530_ = v___y_1568_;
v___y_1531_ = v___x_1571_;
goto v___jp_1528_;
}
else
{
v___y_1529_ = v_a_1569_;
v___y_1530_ = v___y_1568_;
v___y_1531_ = v___x_1570_;
goto v___jp_1528_;
}
}
v___jp_1572_:
{
if (lean_obj_tag(v___y_1574_) == 0)
{
lean_dec_ref(v_binderType_1479_);
lean_dec_ref(v_expr_1250_);
return v___y_1574_;
}
else
{
lean_object* v_a_1575_; 
v_a_1575_ = lean_ctor_get(v___y_1574_, 0);
lean_inc(v_a_1575_);
lean_dec_ref(v___y_1574_);
v___y_1568_ = v___y_1573_;
v_a_1569_ = v_a_1575_;
goto v___jp_1567_;
}
}
v___jp_1576_:
{
if (v___y_1581_ == 0)
{
lean_object* v___x_1582_; 
lean_dec_ref(v___y_1577_);
v___x_1582_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v___y_1578_, v___y_1579_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1582_) == 0)
{
lean_object* v_a_1583_; lean_object* v___x_1584_; 
v_a_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1583_);
lean_dec_ref(v___x_1582_);
lean_inc_ref(v_binderType_1479_);
v___x_1584_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1583_, v_binderType_1479_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1584_) == 0)
{
lean_object* v_a_1585_; lean_object* v___x_1586_; 
v_a_1585_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1585_);
lean_dec_ref(v___x_1584_);
lean_inc_ref(v_arg_1463_);
v___x_1586_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1463_, v_a_1585_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_a_1587_; 
v_a_1587_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1587_);
lean_dec_ref(v___x_1586_);
if (lean_obj_tag(v_a_1587_) == 1)
{
lean_object* v_val_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v_val_1588_ = lean_ctor_get(v_a_1587_, 0);
lean_inc(v_val_1588_);
lean_dec_ref(v_a_1587_);
lean_inc_ref(v_arg_1465_);
lean_inc_ref(v_fn_1464_);
v___x_1589_ = l_Lean_Expr_app___override(v_fn_1464_, v_arg_1465_);
v___x_1590_ = lean_box(0);
v___x_1591_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1591_, 0, v___x_1589_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
lean_ctor_set_uint8(v___x_1591_, sizeof(void*)*2, v___y_1580_);
v___x_1592_ = l_Lean_Meta_Simp_mkCongr(v___x_1591_, v_val_1588_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v___y_1573_ = v___y_1580_;
v___y_1574_ = v___x_1592_;
goto v___jp_1572_;
}
else
{
lean_object* v___x_1593_; lean_object* v___x_1594_; 
lean_dec(v_a_1587_);
v___x_1593_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1594_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1593_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v___y_1573_ = v___y_1580_;
v___y_1574_ = v___x_1594_;
goto v___jp_1572_;
}
}
else
{
lean_object* v_a_1595_; 
v_a_1595_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_a_1595_);
lean_dec_ref(v___x_1586_);
v___y_1568_ = v___y_1580_;
v_a_1569_ = v_a_1595_;
goto v___jp_1567_;
}
}
else
{
lean_object* v_a_1596_; 
v_a_1596_ = lean_ctor_get(v___x_1584_, 0);
lean_inc(v_a_1596_);
lean_dec_ref(v___x_1584_);
v___y_1568_ = v___y_1580_;
v_a_1569_ = v_a_1596_;
goto v___jp_1567_;
}
}
else
{
lean_object* v_a_1597_; 
v_a_1597_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_a_1597_);
lean_dec_ref(v___x_1582_);
v___y_1568_ = v___y_1580_;
v_a_1569_ = v_a_1597_;
goto v___jp_1567_;
}
}
else
{
lean_dec_ref(v___y_1579_);
lean_dec_ref(v___y_1578_);
v___y_1568_ = v___y_1580_;
v_a_1569_ = v___y_1577_;
goto v___jp_1567_;
}
}
v___jp_1598_:
{
uint8_t v___x_1603_; 
v___x_1603_ = l_Lean_Exception_isInterrupt(v_a_1602_);
if (v___x_1603_ == 0)
{
uint8_t v___x_1604_; 
lean_inc_ref(v_a_1602_);
v___x_1604_ = l_Lean_Exception_isRuntime(v_a_1602_);
v___y_1577_ = v_a_1602_;
v___y_1578_ = v___y_1599_;
v___y_1579_ = v___y_1600_;
v___y_1580_ = v___y_1601_;
v___y_1581_ = v___x_1604_;
goto v___jp_1576_;
}
else
{
v___y_1577_ = v_a_1602_;
v___y_1578_ = v___y_1599_;
v___y_1579_ = v___y_1600_;
v___y_1580_ = v___y_1601_;
v___y_1581_ = v___x_1603_;
goto v___jp_1576_;
}
}
v___jp_1605_:
{
if (lean_obj_tag(v___y_1609_) == 0)
{
lean_dec_ref(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec_ref(v_binderType_1479_);
lean_dec_ref(v_expr_1250_);
return v___y_1609_;
}
else
{
lean_object* v_a_1610_; 
v_a_1610_ = lean_ctor_get(v___y_1609_, 0);
lean_inc(v_a_1610_);
lean_dec_ref(v___y_1609_);
v___y_1599_ = v___y_1606_;
v___y_1600_ = v___y_1607_;
v___y_1601_ = v___y_1608_;
v_a_1602_ = v_a_1610_;
goto v___jp_1598_;
}
}
v___jp_1611_:
{
if (v___y_1614_ == 0)
{
lean_object* v___x_1615_; 
lean_dec_ref(v___y_1612_);
v___x_1615_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1465_);
if (lean_obj_tag(v___x_1615_) == 1)
{
lean_object* v_val_1616_; lean_object* v_snd_1617_; lean_object* v___x_1618_; 
v_val_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_val_1616_);
lean_dec_ref(v___x_1615_);
v_snd_1617_ = lean_ctor_get(v_val_1616_, 1);
lean_inc(v_snd_1617_);
lean_dec(v_val_1616_);
v___x_1618_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1463_, v_a_1254_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1619_);
lean_dec_ref(v___x_1618_);
if (lean_obj_tag(v_a_1619_) == 1)
{
lean_object* v_val_1620_; lean_object* v___x_1621_; 
v_val_1620_ = lean_ctor_get(v_a_1619_, 0);
lean_inc(v_val_1620_);
lean_dec_ref(v_a_1619_);
lean_inc(v_a_1254_);
lean_inc_ref(v_a_1253_);
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
v___x_1621_ = lean_infer_type(v_val_1620_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1621_) == 0)
{
lean_object* v_a_1622_; lean_object* v___x_1623_; 
v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1622_);
lean_dec_ref(v___x_1621_);
v___x_1623_ = l_Lean_Meta_mkNumeral(v_a_1622_, v_snd_1617_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v___x_1625_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1624_);
lean_dec_ref(v___x_1623_);
v___x_1625_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1624_, v_binderType_1479_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___x_1627_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1626_);
lean_dec_ref(v___x_1625_);
lean_inc_ref(v_arg_1465_);
v___x_1627_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1465_, v_a_1626_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_a_1628_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1628_);
lean_dec_ref(v___x_1627_);
if (lean_obj_tag(v_a_1628_) == 1)
{
lean_object* v_val_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; 
v_val_1629_ = lean_ctor_get(v_a_1628_, 0);
lean_inc(v_val_1629_);
lean_dec_ref(v_a_1628_);
v___x_1630_ = lean_box(0);
lean_inc_ref(v_fn_1464_);
v___x_1631_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1631_, 0, v_fn_1464_);
lean_ctor_set(v___x_1631_, 1, v___x_1630_);
lean_ctor_set_uint8(v___x_1631_, sizeof(void*)*2, v___y_1613_);
v___x_1632_ = l_Lean_Meta_Simp_mkCongr(v___x_1631_, v_val_1629_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1632_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1634_; 
v_a_1633_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1633_);
lean_dec_ref(v___x_1632_);
lean_inc_ref(v_arg_1463_);
v___x_1634_ = l_Lean_Meta_Simp_mkCongrFun(v_a_1633_, v_arg_1463_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_dec_ref(v_expr_1250_);
return v___x_1634_;
}
else
{
lean_object* v_a_1635_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1635_);
lean_dec_ref(v___x_1634_);
v___y_1458_ = v___y_1613_;
v_a_1459_ = v_a_1635_;
goto v___jp_1457_;
}
}
else
{
lean_object* v_a_1636_; 
v_a_1636_ = lean_ctor_get(v___x_1632_, 0);
lean_inc(v_a_1636_);
lean_dec_ref(v___x_1632_);
v___y_1458_ = v___y_1613_;
v_a_1459_ = v_a_1636_;
goto v___jp_1457_;
}
}
else
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v_a_1639_; 
lean_dec(v_a_1628_);
v___x_1637_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1638_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1637_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
lean_inc(v_a_1639_);
lean_dec_ref(v___x_1638_);
v___y_1458_ = v___y_1613_;
v_a_1459_ = v_a_1639_;
goto v___jp_1457_;
}
}
else
{
lean_object* v_a_1640_; 
v_a_1640_ = lean_ctor_get(v___x_1627_, 0);
lean_inc(v_a_1640_);
lean_dec_ref(v___x_1627_);
v___y_1458_ = v___y_1613_;
v_a_1459_ = v_a_1640_;
goto v___jp_1457_;
}
}
else
{
lean_object* v_a_1641_; 
v_a_1641_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1641_);
lean_dec_ref(v___x_1625_);
v___y_1458_ = v___y_1613_;
v_a_1459_ = v_a_1641_;
goto v___jp_1457_;
}
}
else
{
lean_object* v_a_1642_; 
lean_dec_ref(v_binderType_1479_);
v_a_1642_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1642_);
lean_dec_ref(v___x_1623_);
v___y_1458_ = v___y_1613_;
v_a_1459_ = v_a_1642_;
goto v___jp_1457_;
}
}
else
{
lean_object* v_a_1643_; 
lean_dec(v_snd_1617_);
lean_dec_ref(v_binderType_1479_);
v_a_1643_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_a_1643_);
lean_dec_ref(v___x_1621_);
v___y_1458_ = v___y_1613_;
v_a_1459_ = v_a_1643_;
goto v___jp_1457_;
}
}
else
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v_a_1646_; 
lean_dec(v_a_1619_);
lean_dec(v_snd_1617_);
lean_dec_ref(v_binderType_1479_);
v___x_1644_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1645_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1644_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_a_1646_);
lean_dec_ref(v___x_1645_);
v___y_1458_ = v___y_1613_;
v_a_1459_ = v_a_1646_;
goto v___jp_1457_;
}
}
else
{
lean_object* v_a_1647_; 
lean_dec(v_snd_1617_);
lean_dec_ref(v_binderType_1479_);
v_a_1647_ = lean_ctor_get(v___x_1618_, 0);
lean_inc(v_a_1647_);
lean_dec_ref(v___x_1618_);
v___y_1458_ = v___y_1613_;
v_a_1459_ = v_a_1647_;
goto v___jp_1457_;
}
}
else
{
lean_object* v___x_1648_; 
lean_dec_ref(v_binderType_1479_);
v___x_1648_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1615_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
lean_dec(v___x_1615_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; 
lean_dec_ref(v_expr_1250_);
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref(v___x_1648_);
v_a_1272_ = v_a_1649_;
goto v___jp_1271_;
}
else
{
lean_object* v_a_1650_; 
v_a_1650_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1650_);
lean_dec_ref(v___x_1648_);
v___y_1458_ = v___y_1613_;
v_a_1459_ = v_a_1650_;
goto v___jp_1457_;
}
}
}
else
{
lean_object* v___x_1651_; 
lean_dec_ref(v_binderType_1479_);
lean_dec_ref(v_expr_1250_);
v___x_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1651_, 0, v___y_1612_);
return v___x_1651_;
}
}
v___jp_1652_:
{
uint8_t v___x_1655_; 
v___x_1655_ = l_Lean_Exception_isInterrupt(v_a_1654_);
if (v___x_1655_ == 0)
{
uint8_t v___x_1656_; 
lean_inc_ref(v_a_1654_);
v___x_1656_ = l_Lean_Exception_isRuntime(v_a_1654_);
v___y_1612_ = v_a_1654_;
v___y_1613_ = v___y_1653_;
v___y_1614_ = v___x_1656_;
goto v___jp_1611_;
}
else
{
v___y_1612_ = v_a_1654_;
v___y_1613_ = v___y_1653_;
v___y_1614_ = v___x_1655_;
goto v___jp_1611_;
}
}
v___jp_1657_:
{
if (v___y_1660_ == 0)
{
lean_object* v___x_1661_; 
lean_dec_ref(v___y_1658_);
v___x_1661_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1463_);
if (lean_obj_tag(v___x_1661_) == 1)
{
lean_object* v_val_1662_; lean_object* v_snd_1663_; lean_object* v___x_1664_; 
v_val_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_val_1662_);
lean_dec_ref(v___x_1661_);
v_snd_1663_ = lean_ctor_get(v_val_1662_, 1);
lean_inc(v_snd_1663_);
lean_dec(v_val_1662_);
v___x_1664_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1465_, v_a_1254_);
if (lean_obj_tag(v___x_1664_) == 0)
{
lean_object* v_a_1665_; 
v_a_1665_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_a_1665_);
lean_dec_ref(v___x_1664_);
if (lean_obj_tag(v_a_1665_) == 1)
{
lean_object* v_val_1666_; lean_object* v___x_1667_; 
v_val_1666_ = lean_ctor_get(v_a_1665_, 0);
lean_inc(v_val_1666_);
lean_dec_ref(v_a_1665_);
lean_inc(v_a_1254_);
lean_inc_ref(v_a_1253_);
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
v___x_1667_ = lean_infer_type(v_val_1666_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1667_) == 0)
{
lean_object* v_a_1668_; lean_object* v___x_1669_; 
v_a_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1668_);
lean_dec_ref(v___x_1667_);
v___x_1669_ = l_Lean_Meta_mkNumeral(v_a_1668_, v_snd_1663_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1669_) == 0)
{
lean_object* v_a_1670_; lean_object* v___x_1671_; 
v_a_1670_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_a_1670_);
lean_dec_ref(v___x_1669_);
lean_inc_ref(v_binderType_1479_);
v___x_1671_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1670_, v_binderType_1479_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1671_) == 0)
{
lean_object* v_a_1672_; lean_object* v___x_1673_; 
v_a_1672_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_a_1672_);
lean_dec_ref(v___x_1671_);
lean_inc_ref(v_arg_1463_);
v___x_1673_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1463_, v_a_1672_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1673_) == 0)
{
lean_object* v_a_1674_; 
v_a_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1674_);
lean_dec_ref(v___x_1673_);
if (lean_obj_tag(v_a_1674_) == 1)
{
lean_object* v_val_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v_val_1675_ = lean_ctor_get(v_a_1674_, 0);
lean_inc(v_val_1675_);
lean_dec_ref(v_a_1674_);
lean_inc_ref(v_arg_1465_);
lean_inc_ref(v_fn_1464_);
v___x_1676_ = l_Lean_Expr_app___override(v_fn_1464_, v_arg_1465_);
v___x_1677_ = lean_box(0);
v___x_1678_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1678_, 0, v___x_1676_);
lean_ctor_set(v___x_1678_, 1, v___x_1677_);
lean_ctor_set_uint8(v___x_1678_, sizeof(void*)*2, v___y_1659_);
v___x_1679_ = l_Lean_Meta_Simp_mkCongr(v___x_1678_, v_val_1675_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1679_) == 0)
{
lean_dec_ref(v_binderType_1479_);
lean_dec_ref(v_expr_1250_);
return v___x_1679_;
}
else
{
lean_object* v_a_1680_; 
v_a_1680_ = lean_ctor_get(v___x_1679_, 0);
lean_inc(v_a_1680_);
lean_dec_ref(v___x_1679_);
v___y_1653_ = v___y_1659_;
v_a_1654_ = v_a_1680_;
goto v___jp_1652_;
}
}
else
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v_a_1683_; 
lean_dec(v_a_1674_);
v___x_1681_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1682_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1681_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
lean_inc(v_a_1683_);
lean_dec_ref(v___x_1682_);
v___y_1653_ = v___y_1659_;
v_a_1654_ = v_a_1683_;
goto v___jp_1652_;
}
}
else
{
lean_object* v_a_1684_; 
v_a_1684_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_a_1684_);
lean_dec_ref(v___x_1673_);
v___y_1653_ = v___y_1659_;
v_a_1654_ = v_a_1684_;
goto v___jp_1652_;
}
}
else
{
lean_object* v_a_1685_; 
v_a_1685_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_a_1685_);
lean_dec_ref(v___x_1671_);
v___y_1653_ = v___y_1659_;
v_a_1654_ = v_a_1685_;
goto v___jp_1652_;
}
}
else
{
lean_object* v_a_1686_; 
v_a_1686_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_a_1686_);
lean_dec_ref(v___x_1669_);
v___y_1653_ = v___y_1659_;
v_a_1654_ = v_a_1686_;
goto v___jp_1652_;
}
}
else
{
lean_object* v_a_1687_; 
lean_dec(v_snd_1663_);
v_a_1687_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_a_1687_);
lean_dec_ref(v___x_1667_);
v___y_1653_ = v___y_1659_;
v_a_1654_ = v_a_1687_;
goto v___jp_1652_;
}
}
else
{
lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v_a_1690_; 
lean_dec(v_a_1665_);
lean_dec(v_snd_1663_);
v___x_1688_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1689_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1688_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_a_1690_);
lean_dec_ref(v___x_1689_);
v___y_1653_ = v___y_1659_;
v_a_1654_ = v_a_1690_;
goto v___jp_1652_;
}
}
else
{
lean_object* v_a_1691_; 
lean_dec(v_snd_1663_);
v_a_1691_ = lean_ctor_get(v___x_1664_, 0);
lean_inc(v_a_1691_);
lean_dec_ref(v___x_1664_);
v___y_1653_ = v___y_1659_;
v_a_1654_ = v_a_1691_;
goto v___jp_1652_;
}
}
else
{
lean_object* v___x_1692_; 
v___x_1692_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1661_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
lean_dec(v___x_1661_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; 
lean_dec_ref(v_binderType_1479_);
lean_dec_ref(v_expr_1250_);
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1693_);
lean_dec_ref(v___x_1692_);
v_a_1272_ = v_a_1693_;
goto v___jp_1271_;
}
else
{
lean_object* v_a_1694_; 
v_a_1694_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1694_);
lean_dec_ref(v___x_1692_);
v___y_1653_ = v___y_1659_;
v_a_1654_ = v_a_1694_;
goto v___jp_1652_;
}
}
}
else
{
lean_object* v___x_1695_; 
lean_dec_ref(v_binderType_1479_);
lean_dec_ref(v_expr_1250_);
v___x_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1695_, 0, v___y_1658_);
return v___x_1695_;
}
}
v___jp_1696_:
{
uint8_t v___x_1699_; 
v___x_1699_ = l_Lean_Exception_isInterrupt(v_a_1698_);
if (v___x_1699_ == 0)
{
uint8_t v___x_1700_; 
lean_inc_ref(v_a_1698_);
v___x_1700_ = l_Lean_Exception_isRuntime(v_a_1698_);
v___y_1658_ = v_a_1698_;
v___y_1659_ = v___y_1697_;
v___y_1660_ = v___x_1700_;
goto v___jp_1657_;
}
else
{
v___y_1658_ = v_a_1698_;
v___y_1659_ = v___y_1697_;
v___y_1660_ = v___x_1699_;
goto v___jp_1657_;
}
}
v___jp_1701_:
{
if (lean_obj_tag(v___y_1703_) == 0)
{
lean_dec_ref(v_binderType_1479_);
lean_dec_ref(v_expr_1250_);
return v___y_1703_;
}
else
{
lean_object* v_a_1704_; 
v_a_1704_ = lean_ctor_get(v___y_1703_, 0);
lean_inc(v_a_1704_);
lean_dec_ref(v___y_1703_);
v___y_1697_ = v___y_1702_;
v_a_1698_ = v_a_1704_;
goto v___jp_1696_;
}
}
v___jp_1705_:
{
if (v___y_1710_ == 0)
{
lean_object* v___x_1711_; 
lean_dec_ref(v___y_1708_);
v___x_1711_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v___y_1706_, v___y_1707_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1711_) == 0)
{
lean_object* v_a_1712_; lean_object* v___x_1713_; 
v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_a_1712_);
lean_dec_ref(v___x_1711_);
lean_inc_ref(v_binderType_1479_);
v___x_1713_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1712_, v_binderType_1479_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; lean_object* v___x_1715_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_a_1714_);
lean_dec_ref(v___x_1713_);
lean_inc_ref(v_arg_1463_);
v___x_1715_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1463_, v_a_1714_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_a_1716_);
lean_dec_ref(v___x_1715_);
if (lean_obj_tag(v_a_1716_) == 1)
{
lean_object* v_val_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v_val_1717_ = lean_ctor_get(v_a_1716_, 0);
lean_inc(v_val_1717_);
lean_dec_ref(v_a_1716_);
lean_inc_ref(v_arg_1465_);
lean_inc_ref(v_fn_1464_);
v___x_1718_ = l_Lean_Expr_app___override(v_fn_1464_, v_arg_1465_);
v___x_1719_ = lean_box(0);
v___x_1720_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1720_, 0, v___x_1718_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
lean_ctor_set_uint8(v___x_1720_, sizeof(void*)*2, v___y_1709_);
v___x_1721_ = l_Lean_Meta_Simp_mkCongr(v___x_1720_, v_val_1717_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v___y_1702_ = v___y_1709_;
v___y_1703_ = v___x_1721_;
goto v___jp_1701_;
}
else
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
lean_dec(v_a_1716_);
v___x_1722_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1723_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1722_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v___y_1702_ = v___y_1709_;
v___y_1703_ = v___x_1723_;
goto v___jp_1701_;
}
}
else
{
lean_object* v_a_1724_; 
v_a_1724_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_a_1724_);
lean_dec_ref(v___x_1715_);
v___y_1697_ = v___y_1709_;
v_a_1698_ = v_a_1724_;
goto v___jp_1696_;
}
}
else
{
lean_object* v_a_1725_; 
v_a_1725_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_a_1725_);
lean_dec_ref(v___x_1713_);
v___y_1697_ = v___y_1709_;
v_a_1698_ = v_a_1725_;
goto v___jp_1696_;
}
}
else
{
lean_object* v_a_1726_; 
v_a_1726_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_a_1726_);
lean_dec_ref(v___x_1711_);
v___y_1697_ = v___y_1709_;
v_a_1698_ = v_a_1726_;
goto v___jp_1696_;
}
}
else
{
lean_dec_ref(v___y_1707_);
lean_dec_ref(v___y_1706_);
v___y_1697_ = v___y_1709_;
v_a_1698_ = v___y_1708_;
goto v___jp_1696_;
}
}
v___jp_1727_:
{
uint8_t v___x_1732_; 
v___x_1732_ = l_Lean_Exception_isInterrupt(v_a_1731_);
if (v___x_1732_ == 0)
{
uint8_t v___x_1733_; 
lean_inc_ref(v_a_1731_);
v___x_1733_ = l_Lean_Exception_isRuntime(v_a_1731_);
v___y_1706_ = v___y_1728_;
v___y_1707_ = v___y_1729_;
v___y_1708_ = v_a_1731_;
v___y_1709_ = v___y_1730_;
v___y_1710_ = v___x_1733_;
goto v___jp_1705_;
}
else
{
v___y_1706_ = v___y_1728_;
v___y_1707_ = v___y_1729_;
v___y_1708_ = v_a_1731_;
v___y_1709_ = v___y_1730_;
v___y_1710_ = v___x_1732_;
goto v___jp_1705_;
}
}
v___jp_1734_:
{
if (lean_obj_tag(v___y_1738_) == 0)
{
lean_dec_ref(v___y_1736_);
lean_dec_ref(v___y_1735_);
lean_dec_ref(v_binderType_1479_);
lean_dec_ref(v_expr_1250_);
return v___y_1738_;
}
else
{
lean_object* v_a_1739_; 
v_a_1739_ = lean_ctor_get(v___y_1738_, 0);
lean_inc(v_a_1739_);
lean_dec_ref(v___y_1738_);
v___y_1728_ = v___y_1735_;
v___y_1729_ = v___y_1736_;
v___y_1730_ = v___y_1737_;
v_a_1731_ = v_a_1739_;
goto v___jp_1727_;
}
}
v___jp_1740_:
{
if (v___y_1750_ == 0)
{
lean_object* v___x_1751_; 
lean_dec_ref(v___y_1741_);
v___x_1751_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1465_);
if (lean_obj_tag(v___x_1751_) == 1)
{
lean_object* v_val_1752_; lean_object* v_snd_1753_; lean_object* v___x_1754_; 
v_val_1752_ = lean_ctor_get(v___x_1751_, 0);
lean_inc(v_val_1752_);
lean_dec_ref(v___x_1751_);
v_snd_1753_ = lean_ctor_get(v_val_1752_, 1);
lean_inc(v_snd_1753_);
lean_dec(v_val_1752_);
v___x_1754_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1463_, v_a_1254_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref(v___x_1754_);
if (lean_obj_tag(v_a_1755_) == 1)
{
lean_object* v_val_1756_; lean_object* v___x_1757_; 
v_val_1756_ = lean_ctor_get(v_a_1755_, 0);
lean_inc(v_val_1756_);
lean_dec_ref(v_a_1755_);
lean_inc(v_a_1254_);
lean_inc_ref(v_a_1253_);
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
v___x_1757_ = lean_infer_type(v_val_1756_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1759_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
lean_dec_ref(v___x_1757_);
v___x_1759_ = l_Lean_Meta_mkNumeral(v_a_1758_, v_snd_1753_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v___x_1761_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1760_);
lean_dec_ref(v___x_1759_);
v___x_1761_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1760_, v_binderType_1479_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1763_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
lean_dec_ref(v___x_1761_);
lean_inc_ref(v_arg_1465_);
v___x_1763_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1465_, v_a_1762_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_a_1764_; 
v_a_1764_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1764_);
lean_dec_ref(v___x_1763_);
if (lean_obj_tag(v_a_1764_) == 1)
{
lean_object* v_val_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; 
v_val_1765_ = lean_ctor_get(v_a_1764_, 0);
lean_inc(v_val_1765_);
lean_dec_ref(v_a_1764_);
v___x_1766_ = lean_box(0);
lean_inc_ref(v_fn_1464_);
v___x_1767_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1767_, 0, v_fn_1464_);
lean_ctor_set(v___x_1767_, 1, v___x_1766_);
lean_ctor_set_uint8(v___x_1767_, sizeof(void*)*2, v___y_1749_);
v___x_1768_ = l_Lean_Meta_Simp_mkCongr(v___x_1767_, v_val_1765_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1768_) == 0)
{
lean_object* v_a_1769_; lean_object* v___x_1770_; 
v_a_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1769_);
lean_dec_ref(v___x_1768_);
lean_inc_ref(v_arg_1463_);
v___x_1770_ = l_Lean_Meta_Simp_mkCongrFun(v_a_1769_, v_arg_1463_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; 
lean_dec_ref(v_expr_1250_);
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref(v___x_1770_);
v___y_1379_ = v___y_1742_;
v___y_1380_ = v___y_1743_;
v___y_1381_ = v___y_1745_;
v___y_1382_ = v___y_1744_;
v___y_1383_ = v___y_1746_;
v___y_1384_ = v___y_1747_;
v___y_1385_ = v___y_1749_;
v___y_1386_ = v___y_1748_;
v_a_1387_ = v_a_1771_;
goto v___jp_1378_;
}
else
{
lean_object* v_a_1772_; 
v_a_1772_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1772_);
lean_dec_ref(v___x_1770_);
v___y_1425_ = v___y_1742_;
v___y_1426_ = v___y_1743_;
v___y_1427_ = v___y_1745_;
v___y_1428_ = v___y_1744_;
v___y_1429_ = v___y_1746_;
v___y_1430_ = v___y_1747_;
v___y_1431_ = v___y_1749_;
v___y_1432_ = v___y_1748_;
v_a_1433_ = v_a_1772_;
goto v___jp_1424_;
}
}
else
{
lean_object* v_a_1773_; 
v_a_1773_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_a_1773_);
lean_dec_ref(v___x_1768_);
v___y_1425_ = v___y_1742_;
v___y_1426_ = v___y_1743_;
v___y_1427_ = v___y_1745_;
v___y_1428_ = v___y_1744_;
v___y_1429_ = v___y_1746_;
v___y_1430_ = v___y_1747_;
v___y_1431_ = v___y_1749_;
v___y_1432_ = v___y_1748_;
v_a_1433_ = v_a_1773_;
goto v___jp_1424_;
}
}
else
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v_a_1776_; 
lean_dec(v_a_1764_);
v___x_1774_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1775_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1774_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1776_);
lean_dec_ref(v___x_1775_);
v___y_1425_ = v___y_1742_;
v___y_1426_ = v___y_1743_;
v___y_1427_ = v___y_1745_;
v___y_1428_ = v___y_1744_;
v___y_1429_ = v___y_1746_;
v___y_1430_ = v___y_1747_;
v___y_1431_ = v___y_1749_;
v___y_1432_ = v___y_1748_;
v_a_1433_ = v_a_1776_;
goto v___jp_1424_;
}
}
else
{
lean_object* v_a_1777_; 
v_a_1777_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_a_1777_);
lean_dec_ref(v___x_1763_);
v___y_1425_ = v___y_1742_;
v___y_1426_ = v___y_1743_;
v___y_1427_ = v___y_1745_;
v___y_1428_ = v___y_1744_;
v___y_1429_ = v___y_1746_;
v___y_1430_ = v___y_1747_;
v___y_1431_ = v___y_1749_;
v___y_1432_ = v___y_1748_;
v_a_1433_ = v_a_1777_;
goto v___jp_1424_;
}
}
else
{
lean_object* v_a_1778_; 
v_a_1778_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1778_);
lean_dec_ref(v___x_1761_);
v___y_1425_ = v___y_1742_;
v___y_1426_ = v___y_1743_;
v___y_1427_ = v___y_1745_;
v___y_1428_ = v___y_1744_;
v___y_1429_ = v___y_1746_;
v___y_1430_ = v___y_1747_;
v___y_1431_ = v___y_1749_;
v___y_1432_ = v___y_1748_;
v_a_1433_ = v_a_1778_;
goto v___jp_1424_;
}
}
else
{
lean_object* v_a_1779_; 
lean_dec_ref(v_binderType_1479_);
v_a_1779_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1779_);
lean_dec_ref(v___x_1759_);
v___y_1425_ = v___y_1742_;
v___y_1426_ = v___y_1743_;
v___y_1427_ = v___y_1745_;
v___y_1428_ = v___y_1744_;
v___y_1429_ = v___y_1746_;
v___y_1430_ = v___y_1747_;
v___y_1431_ = v___y_1749_;
v___y_1432_ = v___y_1748_;
v_a_1433_ = v_a_1779_;
goto v___jp_1424_;
}
}
else
{
lean_object* v_a_1780_; 
lean_dec(v_snd_1753_);
lean_dec_ref(v_binderType_1479_);
v_a_1780_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1780_);
lean_dec_ref(v___x_1757_);
v___y_1425_ = v___y_1742_;
v___y_1426_ = v___y_1743_;
v___y_1427_ = v___y_1745_;
v___y_1428_ = v___y_1744_;
v___y_1429_ = v___y_1746_;
v___y_1430_ = v___y_1747_;
v___y_1431_ = v___y_1749_;
v___y_1432_ = v___y_1748_;
v_a_1433_ = v_a_1780_;
goto v___jp_1424_;
}
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v_a_1783_; 
lean_dec(v_a_1755_);
lean_dec(v_snd_1753_);
lean_dec_ref(v_binderType_1479_);
v___x_1781_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1782_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1781_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref(v___x_1782_);
v___y_1425_ = v___y_1742_;
v___y_1426_ = v___y_1743_;
v___y_1427_ = v___y_1745_;
v___y_1428_ = v___y_1744_;
v___y_1429_ = v___y_1746_;
v___y_1430_ = v___y_1747_;
v___y_1431_ = v___y_1749_;
v___y_1432_ = v___y_1748_;
v_a_1433_ = v_a_1783_;
goto v___jp_1424_;
}
}
else
{
lean_object* v_a_1784_; 
lean_dec(v_snd_1753_);
lean_dec_ref(v_binderType_1479_);
v_a_1784_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1784_);
lean_dec_ref(v___x_1754_);
v___y_1425_ = v___y_1742_;
v___y_1426_ = v___y_1743_;
v___y_1427_ = v___y_1745_;
v___y_1428_ = v___y_1744_;
v___y_1429_ = v___y_1746_;
v___y_1430_ = v___y_1747_;
v___y_1431_ = v___y_1749_;
v___y_1432_ = v___y_1748_;
v_a_1433_ = v_a_1784_;
goto v___jp_1424_;
}
}
else
{
lean_object* v___x_1785_; 
lean_dec_ref(v_binderType_1479_);
v___x_1785_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1751_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
lean_dec(v___x_1751_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; 
lean_dec_ref(v_expr_1250_);
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_a_1786_);
lean_dec_ref(v___x_1785_);
v___y_1390_ = v___y_1742_;
v___y_1391_ = v___y_1743_;
v___y_1392_ = v___y_1744_;
v___y_1393_ = v___y_1745_;
v___y_1394_ = v___y_1746_;
v___y_1395_ = v___y_1747_;
v___y_1396_ = v___y_1748_;
v___y_1397_ = v___y_1749_;
v_a_1398_ = v_a_1786_;
goto v___jp_1389_;
}
else
{
lean_object* v_a_1787_; 
v_a_1787_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_a_1787_);
lean_dec_ref(v___x_1785_);
v___y_1425_ = v___y_1742_;
v___y_1426_ = v___y_1743_;
v___y_1427_ = v___y_1745_;
v___y_1428_ = v___y_1744_;
v___y_1429_ = v___y_1746_;
v___y_1430_ = v___y_1747_;
v___y_1431_ = v___y_1749_;
v___y_1432_ = v___y_1748_;
v_a_1433_ = v_a_1787_;
goto v___jp_1424_;
}
}
}
else
{
lean_dec_ref(v_binderType_1479_);
lean_dec_ref(v_expr_1250_);
v___y_1401_ = v___y_1742_;
v___y_1402_ = v___y_1743_;
v___y_1403_ = v___y_1745_;
v___y_1404_ = v___y_1744_;
v___y_1405_ = v___y_1746_;
v___y_1406_ = v___y_1747_;
v___y_1407_ = v___y_1749_;
v___y_1408_ = v___y_1748_;
v_a_1409_ = v___y_1741_;
goto v___jp_1400_;
}
}
v___jp_1788_:
{
uint8_t v___x_1798_; 
v___x_1798_ = l_Lean_Exception_isInterrupt(v_a_1797_);
if (v___x_1798_ == 0)
{
uint8_t v___x_1799_; 
lean_inc_ref(v_a_1797_);
v___x_1799_ = l_Lean_Exception_isRuntime(v_a_1797_);
v___y_1741_ = v_a_1797_;
v___y_1742_ = v___y_1789_;
v___y_1743_ = v___y_1790_;
v___y_1744_ = v___y_1792_;
v___y_1745_ = v___y_1791_;
v___y_1746_ = v___y_1793_;
v___y_1747_ = v___y_1794_;
v___y_1748_ = v___y_1796_;
v___y_1749_ = v___y_1795_;
v___y_1750_ = v___x_1799_;
goto v___jp_1740_;
}
else
{
v___y_1741_ = v_a_1797_;
v___y_1742_ = v___y_1789_;
v___y_1743_ = v___y_1790_;
v___y_1744_ = v___y_1792_;
v___y_1745_ = v___y_1791_;
v___y_1746_ = v___y_1793_;
v___y_1747_ = v___y_1794_;
v___y_1748_ = v___y_1796_;
v___y_1749_ = v___y_1795_;
v___y_1750_ = v___x_1798_;
goto v___jp_1740_;
}
}
v___jp_1800_:
{
if (v___y_1810_ == 0)
{
lean_object* v___x_1811_; 
lean_dec_ref(v___y_1802_);
v___x_1811_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1463_);
if (lean_obj_tag(v___x_1811_) == 1)
{
lean_object* v_val_1812_; lean_object* v_snd_1813_; lean_object* v___x_1814_; 
v_val_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_val_1812_);
lean_dec_ref(v___x_1811_);
v_snd_1813_ = lean_ctor_get(v_val_1812_, 1);
lean_inc(v_snd_1813_);
lean_dec(v_val_1812_);
v___x_1814_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1465_, v_a_1254_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1815_);
lean_dec_ref(v___x_1814_);
if (lean_obj_tag(v_a_1815_) == 1)
{
lean_object* v_val_1816_; lean_object* v___x_1817_; 
v_val_1816_ = lean_ctor_get(v_a_1815_, 0);
lean_inc(v_val_1816_);
lean_dec_ref(v_a_1815_);
lean_inc(v_a_1254_);
lean_inc_ref(v_a_1253_);
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
v___x_1817_ = lean_infer_type(v_val_1816_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1819_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_a_1818_);
lean_dec_ref(v___x_1817_);
v___x_1819_ = l_Lean_Meta_mkNumeral(v_a_1818_, v_snd_1813_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1819_) == 0)
{
lean_object* v_a_1820_; lean_object* v___x_1821_; 
v_a_1820_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1820_);
lean_dec_ref(v___x_1819_);
lean_inc_ref(v_binderType_1479_);
v___x_1821_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1820_, v_binderType_1479_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1821_) == 0)
{
lean_object* v_a_1822_; lean_object* v___x_1823_; 
v_a_1822_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1822_);
lean_dec_ref(v___x_1821_);
lean_inc_ref(v_arg_1463_);
v___x_1823_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1463_, v_a_1822_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1823_) == 0)
{
lean_object* v_a_1824_; 
v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_a_1824_);
lean_dec_ref(v___x_1823_);
if (lean_obj_tag(v_a_1824_) == 1)
{
lean_object* v_val_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; 
v_val_1825_ = lean_ctor_get(v_a_1824_, 0);
lean_inc(v_val_1825_);
lean_dec_ref(v_a_1824_);
lean_inc_ref(v_arg_1465_);
lean_inc_ref(v_fn_1464_);
v___x_1826_ = l_Lean_Expr_app___override(v_fn_1464_, v_arg_1465_);
v___x_1827_ = lean_box(0);
v___x_1828_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1828_, 0, v___x_1826_);
lean_ctor_set(v___x_1828_, 1, v___x_1827_);
lean_ctor_set_uint8(v___x_1828_, sizeof(void*)*2, v___y_1809_);
v___x_1829_ = l_Lean_Meta_Simp_mkCongr(v___x_1828_, v_val_1825_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_a_1830_; 
lean_dec_ref(v_binderType_1479_);
lean_dec_ref(v_expr_1250_);
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_a_1830_);
lean_dec_ref(v___x_1829_);
v___y_1379_ = v___y_1801_;
v___y_1380_ = v___y_1803_;
v___y_1381_ = v___y_1805_;
v___y_1382_ = v___y_1804_;
v___y_1383_ = v___y_1806_;
v___y_1384_ = v___y_1807_;
v___y_1385_ = v___y_1809_;
v___y_1386_ = v___y_1808_;
v_a_1387_ = v_a_1830_;
goto v___jp_1378_;
}
else
{
lean_object* v_a_1831_; 
v_a_1831_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_a_1831_);
lean_dec_ref(v___x_1829_);
v___y_1789_ = v___y_1801_;
v___y_1790_ = v___y_1803_;
v___y_1791_ = v___y_1805_;
v___y_1792_ = v___y_1804_;
v___y_1793_ = v___y_1806_;
v___y_1794_ = v___y_1807_;
v___y_1795_ = v___y_1809_;
v___y_1796_ = v___y_1808_;
v_a_1797_ = v_a_1831_;
goto v___jp_1788_;
}
}
else
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v_a_1834_; 
lean_dec(v_a_1824_);
v___x_1832_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1833_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1832_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
lean_dec_ref(v___x_1833_);
v___y_1789_ = v___y_1801_;
v___y_1790_ = v___y_1803_;
v___y_1791_ = v___y_1805_;
v___y_1792_ = v___y_1804_;
v___y_1793_ = v___y_1806_;
v___y_1794_ = v___y_1807_;
v___y_1795_ = v___y_1809_;
v___y_1796_ = v___y_1808_;
v_a_1797_ = v_a_1834_;
goto v___jp_1788_;
}
}
else
{
lean_object* v_a_1835_; 
v_a_1835_ = lean_ctor_get(v___x_1823_, 0);
lean_inc(v_a_1835_);
lean_dec_ref(v___x_1823_);
v___y_1789_ = v___y_1801_;
v___y_1790_ = v___y_1803_;
v___y_1791_ = v___y_1805_;
v___y_1792_ = v___y_1804_;
v___y_1793_ = v___y_1806_;
v___y_1794_ = v___y_1807_;
v___y_1795_ = v___y_1809_;
v___y_1796_ = v___y_1808_;
v_a_1797_ = v_a_1835_;
goto v___jp_1788_;
}
}
else
{
lean_object* v_a_1836_; 
v_a_1836_ = lean_ctor_get(v___x_1821_, 0);
lean_inc(v_a_1836_);
lean_dec_ref(v___x_1821_);
v___y_1789_ = v___y_1801_;
v___y_1790_ = v___y_1803_;
v___y_1791_ = v___y_1805_;
v___y_1792_ = v___y_1804_;
v___y_1793_ = v___y_1806_;
v___y_1794_ = v___y_1807_;
v___y_1795_ = v___y_1809_;
v___y_1796_ = v___y_1808_;
v_a_1797_ = v_a_1836_;
goto v___jp_1788_;
}
}
else
{
lean_object* v_a_1837_; 
v_a_1837_ = lean_ctor_get(v___x_1819_, 0);
lean_inc(v_a_1837_);
lean_dec_ref(v___x_1819_);
v___y_1789_ = v___y_1801_;
v___y_1790_ = v___y_1803_;
v___y_1791_ = v___y_1805_;
v___y_1792_ = v___y_1804_;
v___y_1793_ = v___y_1806_;
v___y_1794_ = v___y_1807_;
v___y_1795_ = v___y_1809_;
v___y_1796_ = v___y_1808_;
v_a_1797_ = v_a_1837_;
goto v___jp_1788_;
}
}
else
{
lean_object* v_a_1838_; 
lean_dec(v_snd_1813_);
v_a_1838_ = lean_ctor_get(v___x_1817_, 0);
lean_inc(v_a_1838_);
lean_dec_ref(v___x_1817_);
v___y_1789_ = v___y_1801_;
v___y_1790_ = v___y_1803_;
v___y_1791_ = v___y_1805_;
v___y_1792_ = v___y_1804_;
v___y_1793_ = v___y_1806_;
v___y_1794_ = v___y_1807_;
v___y_1795_ = v___y_1809_;
v___y_1796_ = v___y_1808_;
v_a_1797_ = v_a_1838_;
goto v___jp_1788_;
}
}
else
{
lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v_a_1841_; 
lean_dec(v_a_1815_);
lean_dec(v_snd_1813_);
v___x_1839_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1840_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1839_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
lean_inc(v_a_1841_);
lean_dec_ref(v___x_1840_);
v___y_1789_ = v___y_1801_;
v___y_1790_ = v___y_1803_;
v___y_1791_ = v___y_1805_;
v___y_1792_ = v___y_1804_;
v___y_1793_ = v___y_1806_;
v___y_1794_ = v___y_1807_;
v___y_1795_ = v___y_1809_;
v___y_1796_ = v___y_1808_;
v_a_1797_ = v_a_1841_;
goto v___jp_1788_;
}
}
else
{
lean_object* v_a_1842_; 
lean_dec(v_snd_1813_);
v_a_1842_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1842_);
lean_dec_ref(v___x_1814_);
v___y_1789_ = v___y_1801_;
v___y_1790_ = v___y_1803_;
v___y_1791_ = v___y_1805_;
v___y_1792_ = v___y_1804_;
v___y_1793_ = v___y_1806_;
v___y_1794_ = v___y_1807_;
v___y_1795_ = v___y_1809_;
v___y_1796_ = v___y_1808_;
v_a_1797_ = v_a_1842_;
goto v___jp_1788_;
}
}
else
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1811_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
lean_dec(v___x_1811_);
if (lean_obj_tag(v___x_1843_) == 0)
{
lean_object* v_a_1844_; 
lean_dec_ref(v_binderType_1479_);
lean_dec_ref(v_expr_1250_);
v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1844_);
lean_dec_ref(v___x_1843_);
v___y_1390_ = v___y_1801_;
v___y_1391_ = v___y_1803_;
v___y_1392_ = v___y_1804_;
v___y_1393_ = v___y_1805_;
v___y_1394_ = v___y_1806_;
v___y_1395_ = v___y_1807_;
v___y_1396_ = v___y_1808_;
v___y_1397_ = v___y_1809_;
v_a_1398_ = v_a_1844_;
goto v___jp_1389_;
}
else
{
lean_object* v_a_1845_; 
v_a_1845_ = lean_ctor_get(v___x_1843_, 0);
lean_inc(v_a_1845_);
lean_dec_ref(v___x_1843_);
v___y_1789_ = v___y_1801_;
v___y_1790_ = v___y_1803_;
v___y_1791_ = v___y_1805_;
v___y_1792_ = v___y_1804_;
v___y_1793_ = v___y_1806_;
v___y_1794_ = v___y_1807_;
v___y_1795_ = v___y_1809_;
v___y_1796_ = v___y_1808_;
v_a_1797_ = v_a_1845_;
goto v___jp_1788_;
}
}
}
else
{
lean_dec_ref(v_binderType_1479_);
lean_dec_ref(v_expr_1250_);
v___y_1401_ = v___y_1801_;
v___y_1402_ = v___y_1803_;
v___y_1403_ = v___y_1805_;
v___y_1404_ = v___y_1804_;
v___y_1405_ = v___y_1806_;
v___y_1406_ = v___y_1807_;
v___y_1407_ = v___y_1809_;
v___y_1408_ = v___y_1808_;
v_a_1409_ = v___y_1802_;
goto v___jp_1400_;
}
}
v___jp_1846_:
{
uint8_t v___x_1856_; 
v___x_1856_ = l_Lean_Exception_isInterrupt(v_a_1855_);
if (v___x_1856_ == 0)
{
uint8_t v___x_1857_; 
lean_inc_ref(v_a_1855_);
v___x_1857_ = l_Lean_Exception_isRuntime(v_a_1855_);
v___y_1801_ = v___y_1847_;
v___y_1802_ = v_a_1855_;
v___y_1803_ = v___y_1848_;
v___y_1804_ = v___y_1850_;
v___y_1805_ = v___y_1849_;
v___y_1806_ = v___y_1851_;
v___y_1807_ = v___y_1852_;
v___y_1808_ = v___y_1854_;
v___y_1809_ = v___y_1853_;
v___y_1810_ = v___x_1857_;
goto v___jp_1800_;
}
else
{
v___y_1801_ = v___y_1847_;
v___y_1802_ = v_a_1855_;
v___y_1803_ = v___y_1848_;
v___y_1804_ = v___y_1850_;
v___y_1805_ = v___y_1849_;
v___y_1806_ = v___y_1851_;
v___y_1807_ = v___y_1852_;
v___y_1808_ = v___y_1854_;
v___y_1809_ = v___y_1853_;
v___y_1810_ = v___x_1856_;
goto v___jp_1800_;
}
}
v___jp_1858_:
{
if (lean_obj_tag(v___y_1867_) == 0)
{
lean_object* v_a_1868_; 
lean_dec_ref(v_binderType_1479_);
lean_dec_ref(v_expr_1250_);
v_a_1868_ = lean_ctor_get(v___y_1867_, 0);
lean_inc(v_a_1868_);
lean_dec_ref(v___y_1867_);
v___y_1379_ = v___y_1859_;
v___y_1380_ = v___y_1860_;
v___y_1381_ = v___y_1862_;
v___y_1382_ = v___y_1861_;
v___y_1383_ = v___y_1863_;
v___y_1384_ = v___y_1864_;
v___y_1385_ = v___y_1866_;
v___y_1386_ = v___y_1865_;
v_a_1387_ = v_a_1868_;
goto v___jp_1378_;
}
else
{
lean_object* v_a_1869_; 
v_a_1869_ = lean_ctor_get(v___y_1867_, 0);
lean_inc(v_a_1869_);
lean_dec_ref(v___y_1867_);
v___y_1847_ = v___y_1859_;
v___y_1848_ = v___y_1860_;
v___y_1849_ = v___y_1862_;
v___y_1850_ = v___y_1861_;
v___y_1851_ = v___y_1863_;
v___y_1852_ = v___y_1864_;
v___y_1853_ = v___y_1866_;
v___y_1854_ = v___y_1865_;
v_a_1855_ = v_a_1869_;
goto v___jp_1846_;
}
}
v___jp_1870_:
{
if (v___y_1882_ == 0)
{
lean_object* v___x_1883_; 
lean_dec_ref(v___y_1878_);
v___x_1883_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v___y_1876_, v___y_1873_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; lean_object* v___x_1885_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref(v___x_1883_);
lean_inc_ref(v_binderType_1479_);
v___x_1885_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1884_, v_binderType_1479_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1887_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref(v___x_1885_);
lean_inc_ref(v_arg_1463_);
v___x_1887_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1463_, v_a_1886_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1888_);
lean_dec_ref(v___x_1887_);
if (lean_obj_tag(v_a_1888_) == 1)
{
lean_object* v_val_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v_val_1889_ = lean_ctor_get(v_a_1888_, 0);
lean_inc(v_val_1889_);
lean_dec_ref(v_a_1888_);
lean_inc_ref(v_arg_1465_);
lean_inc_ref(v_fn_1464_);
v___x_1890_ = l_Lean_Expr_app___override(v_fn_1464_, v_arg_1465_);
v___x_1891_ = lean_box(0);
v___x_1892_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1892_, 0, v___x_1890_);
lean_ctor_set(v___x_1892_, 1, v___x_1891_);
lean_ctor_set_uint8(v___x_1892_, sizeof(void*)*2, v___y_1881_);
v___x_1893_ = l_Lean_Meta_Simp_mkCongr(v___x_1892_, v_val_1889_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v___y_1859_ = v___y_1871_;
v___y_1860_ = v___y_1872_;
v___y_1861_ = v___y_1875_;
v___y_1862_ = v___y_1874_;
v___y_1863_ = v___y_1877_;
v___y_1864_ = v___y_1879_;
v___y_1865_ = v___y_1880_;
v___y_1866_ = v___y_1881_;
v___y_1867_ = v___x_1893_;
goto v___jp_1858_;
}
else
{
lean_object* v___x_1894_; lean_object* v___x_1895_; 
lean_dec(v_a_1888_);
v___x_1894_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1895_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1894_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v___y_1859_ = v___y_1871_;
v___y_1860_ = v___y_1872_;
v___y_1861_ = v___y_1875_;
v___y_1862_ = v___y_1874_;
v___y_1863_ = v___y_1877_;
v___y_1864_ = v___y_1879_;
v___y_1865_ = v___y_1880_;
v___y_1866_ = v___y_1881_;
v___y_1867_ = v___x_1895_;
goto v___jp_1858_;
}
}
else
{
lean_object* v_a_1896_; 
v_a_1896_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1896_);
lean_dec_ref(v___x_1887_);
v___y_1847_ = v___y_1871_;
v___y_1848_ = v___y_1872_;
v___y_1849_ = v___y_1874_;
v___y_1850_ = v___y_1875_;
v___y_1851_ = v___y_1877_;
v___y_1852_ = v___y_1879_;
v___y_1853_ = v___y_1881_;
v___y_1854_ = v___y_1880_;
v_a_1855_ = v_a_1896_;
goto v___jp_1846_;
}
}
else
{
lean_object* v_a_1897_; 
v_a_1897_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1897_);
lean_dec_ref(v___x_1885_);
v___y_1847_ = v___y_1871_;
v___y_1848_ = v___y_1872_;
v___y_1849_ = v___y_1874_;
v___y_1850_ = v___y_1875_;
v___y_1851_ = v___y_1877_;
v___y_1852_ = v___y_1879_;
v___y_1853_ = v___y_1881_;
v___y_1854_ = v___y_1880_;
v_a_1855_ = v_a_1897_;
goto v___jp_1846_;
}
}
else
{
lean_object* v_a_1898_; 
v_a_1898_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1898_);
lean_dec_ref(v___x_1883_);
v___y_1847_ = v___y_1871_;
v___y_1848_ = v___y_1872_;
v___y_1849_ = v___y_1874_;
v___y_1850_ = v___y_1875_;
v___y_1851_ = v___y_1877_;
v___y_1852_ = v___y_1879_;
v___y_1853_ = v___y_1881_;
v___y_1854_ = v___y_1880_;
v_a_1855_ = v_a_1898_;
goto v___jp_1846_;
}
}
else
{
lean_dec_ref(v___y_1876_);
lean_dec_ref(v___y_1873_);
v___y_1847_ = v___y_1871_;
v___y_1848_ = v___y_1872_;
v___y_1849_ = v___y_1874_;
v___y_1850_ = v___y_1875_;
v___y_1851_ = v___y_1877_;
v___y_1852_ = v___y_1879_;
v___y_1853_ = v___y_1881_;
v___y_1854_ = v___y_1880_;
v_a_1855_ = v___y_1878_;
goto v___jp_1846_;
}
}
v___jp_1899_:
{
uint8_t v___x_1911_; 
v___x_1911_ = l_Lean_Exception_isInterrupt(v_a_1910_);
if (v___x_1911_ == 0)
{
uint8_t v___x_1912_; 
lean_inc_ref(v_a_1910_);
v___x_1912_ = l_Lean_Exception_isRuntime(v_a_1910_);
v___y_1871_ = v___y_1900_;
v___y_1872_ = v___y_1902_;
v___y_1873_ = v___y_1901_;
v___y_1874_ = v___y_1905_;
v___y_1875_ = v___y_1904_;
v___y_1876_ = v___y_1903_;
v___y_1877_ = v___y_1906_;
v___y_1878_ = v_a_1910_;
v___y_1879_ = v___y_1907_;
v___y_1880_ = v___y_1909_;
v___y_1881_ = v___y_1908_;
v___y_1882_ = v___x_1912_;
goto v___jp_1870_;
}
else
{
v___y_1871_ = v___y_1900_;
v___y_1872_ = v___y_1902_;
v___y_1873_ = v___y_1901_;
v___y_1874_ = v___y_1905_;
v___y_1875_ = v___y_1904_;
v___y_1876_ = v___y_1903_;
v___y_1877_ = v___y_1906_;
v___y_1878_ = v_a_1910_;
v___y_1879_ = v___y_1907_;
v___y_1880_ = v___y_1909_;
v___y_1881_ = v___y_1908_;
v___y_1882_ = v___x_1911_;
goto v___jp_1870_;
}
}
v___jp_1913_:
{
if (lean_obj_tag(v___y_1924_) == 0)
{
lean_object* v_a_1925_; 
lean_dec_ref(v___y_1917_);
lean_dec_ref(v___y_1915_);
lean_dec_ref(v_binderType_1479_);
lean_dec_ref(v_expr_1250_);
v_a_1925_ = lean_ctor_get(v___y_1924_, 0);
lean_inc(v_a_1925_);
lean_dec_ref(v___y_1924_);
v___y_1379_ = v___y_1914_;
v___y_1380_ = v___y_1916_;
v___y_1381_ = v___y_1919_;
v___y_1382_ = v___y_1918_;
v___y_1383_ = v___y_1920_;
v___y_1384_ = v___y_1921_;
v___y_1385_ = v___y_1923_;
v___y_1386_ = v___y_1922_;
v_a_1387_ = v_a_1925_;
goto v___jp_1378_;
}
else
{
lean_object* v_a_1926_; 
v_a_1926_ = lean_ctor_get(v___y_1924_, 0);
lean_inc(v_a_1926_);
lean_dec_ref(v___y_1924_);
v___y_1900_ = v___y_1914_;
v___y_1901_ = v___y_1915_;
v___y_1902_ = v___y_1916_;
v___y_1903_ = v___y_1917_;
v___y_1904_ = v___y_1918_;
v___y_1905_ = v___y_1919_;
v___y_1906_ = v___y_1920_;
v___y_1907_ = v___y_1921_;
v___y_1908_ = v___y_1923_;
v___y_1909_ = v___y_1922_;
v_a_1910_ = v_a_1926_;
goto v___jp_1899_;
}
}
v___jp_1927_:
{
if (v___y_1937_ == 0)
{
lean_object* v___x_1938_; 
lean_dec_ref(v___y_1928_);
v___x_1938_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1465_);
if (lean_obj_tag(v___x_1938_) == 1)
{
lean_object* v_val_1939_; lean_object* v_snd_1940_; lean_object* v___x_1941_; 
v_val_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_val_1939_);
lean_dec_ref(v___x_1938_);
v_snd_1940_ = lean_ctor_get(v_val_1939_, 1);
lean_inc(v_snd_1940_);
lean_dec(v_val_1939_);
v___x_1941_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1463_, v_a_1254_);
if (lean_obj_tag(v___x_1941_) == 0)
{
lean_object* v_a_1942_; 
v_a_1942_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1942_);
lean_dec_ref(v___x_1941_);
if (lean_obj_tag(v_a_1942_) == 1)
{
lean_object* v_val_1943_; lean_object* v___x_1944_; 
v_val_1943_ = lean_ctor_get(v_a_1942_, 0);
lean_inc(v_val_1943_);
lean_dec_ref(v_a_1942_);
lean_inc(v_a_1254_);
lean_inc_ref(v_a_1253_);
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
v___x_1944_ = lean_infer_type(v_val_1943_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_a_1945_; lean_object* v___x_1946_; 
v_a_1945_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1945_);
lean_dec_ref(v___x_1944_);
v___x_1946_ = l_Lean_Meta_mkNumeral(v_a_1945_, v_snd_1940_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; lean_object* v___x_1948_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref(v___x_1946_);
v___x_1948_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_1947_, v_binderType_1479_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v___x_1950_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1949_);
lean_dec_ref(v___x_1948_);
lean_inc_ref(v_arg_1465_);
v___x_1950_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1465_, v_a_1949_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_object* v_a_1951_; 
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1951_);
lean_dec_ref(v___x_1950_);
if (lean_obj_tag(v_a_1951_) == 1)
{
lean_object* v_val_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v_val_1952_ = lean_ctor_get(v_a_1951_, 0);
lean_inc(v_val_1952_);
lean_dec_ref(v_a_1951_);
v___x_1953_ = lean_box(0);
lean_inc_ref(v_fn_1464_);
v___x_1954_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1954_, 0, v_fn_1464_);
lean_ctor_set(v___x_1954_, 1, v___x_1953_);
lean_ctor_set_uint8(v___x_1954_, sizeof(void*)*2, v___y_1936_);
v___x_1955_ = l_Lean_Meta_Simp_mkCongr(v___x_1954_, v_val_1952_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; lean_object* v___x_1957_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_a_1956_);
lean_dec_ref(v___x_1955_);
lean_inc_ref(v_arg_1463_);
v___x_1957_ = l_Lean_Meta_Simp_mkCongrFun(v_a_1956_, v_arg_1463_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; 
lean_dec_ref(v_expr_1250_);
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref(v___x_1957_);
v___y_1300_ = v___y_1929_;
v___y_1301_ = v___y_1932_;
v___y_1302_ = v___y_1931_;
v___y_1303_ = v___y_1930_;
v___y_1304_ = v___y_1933_;
v___y_1305_ = v___y_1934_;
v___y_1306_ = v___y_1936_;
v___y_1307_ = v___y_1935_;
v_a_1308_ = v_a_1958_;
goto v___jp_1299_;
}
else
{
lean_object* v_a_1959_; 
v_a_1959_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1959_);
lean_dec_ref(v___x_1957_);
v___y_1346_ = v___y_1929_;
v___y_1347_ = v___y_1932_;
v___y_1348_ = v___y_1931_;
v___y_1349_ = v___y_1930_;
v___y_1350_ = v___y_1933_;
v___y_1351_ = v___y_1934_;
v___y_1352_ = v___y_1936_;
v___y_1353_ = v___y_1935_;
v_a_1354_ = v_a_1959_;
goto v___jp_1345_;
}
}
else
{
lean_object* v_a_1960_; 
v_a_1960_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_a_1960_);
lean_dec_ref(v___x_1955_);
v___y_1346_ = v___y_1929_;
v___y_1347_ = v___y_1932_;
v___y_1348_ = v___y_1931_;
v___y_1349_ = v___y_1930_;
v___y_1350_ = v___y_1933_;
v___y_1351_ = v___y_1934_;
v___y_1352_ = v___y_1936_;
v___y_1353_ = v___y_1935_;
v_a_1354_ = v_a_1960_;
goto v___jp_1345_;
}
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v_a_1963_; 
lean_dec(v_a_1951_);
v___x_1961_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1962_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1961_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref(v___x_1962_);
v___y_1346_ = v___y_1929_;
v___y_1347_ = v___y_1932_;
v___y_1348_ = v___y_1931_;
v___y_1349_ = v___y_1930_;
v___y_1350_ = v___y_1933_;
v___y_1351_ = v___y_1934_;
v___y_1352_ = v___y_1936_;
v___y_1353_ = v___y_1935_;
v_a_1354_ = v_a_1963_;
goto v___jp_1345_;
}
}
else
{
lean_object* v_a_1964_; 
v_a_1964_ = lean_ctor_get(v___x_1950_, 0);
lean_inc(v_a_1964_);
lean_dec_ref(v___x_1950_);
v___y_1346_ = v___y_1929_;
v___y_1347_ = v___y_1932_;
v___y_1348_ = v___y_1931_;
v___y_1349_ = v___y_1930_;
v___y_1350_ = v___y_1933_;
v___y_1351_ = v___y_1934_;
v___y_1352_ = v___y_1936_;
v___y_1353_ = v___y_1935_;
v_a_1354_ = v_a_1964_;
goto v___jp_1345_;
}
}
else
{
lean_object* v_a_1965_; 
v_a_1965_ = lean_ctor_get(v___x_1948_, 0);
lean_inc(v_a_1965_);
lean_dec_ref(v___x_1948_);
v___y_1346_ = v___y_1929_;
v___y_1347_ = v___y_1932_;
v___y_1348_ = v___y_1931_;
v___y_1349_ = v___y_1930_;
v___y_1350_ = v___y_1933_;
v___y_1351_ = v___y_1934_;
v___y_1352_ = v___y_1936_;
v___y_1353_ = v___y_1935_;
v_a_1354_ = v_a_1965_;
goto v___jp_1345_;
}
}
else
{
lean_object* v_a_1966_; 
lean_dec_ref(v_binderType_1479_);
v_a_1966_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1966_);
lean_dec_ref(v___x_1946_);
v___y_1346_ = v___y_1929_;
v___y_1347_ = v___y_1932_;
v___y_1348_ = v___y_1931_;
v___y_1349_ = v___y_1930_;
v___y_1350_ = v___y_1933_;
v___y_1351_ = v___y_1934_;
v___y_1352_ = v___y_1936_;
v___y_1353_ = v___y_1935_;
v_a_1354_ = v_a_1966_;
goto v___jp_1345_;
}
}
else
{
lean_object* v_a_1967_; 
lean_dec(v_snd_1940_);
lean_dec_ref(v_binderType_1479_);
v_a_1967_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_a_1967_);
lean_dec_ref(v___x_1944_);
v___y_1346_ = v___y_1929_;
v___y_1347_ = v___y_1932_;
v___y_1348_ = v___y_1931_;
v___y_1349_ = v___y_1930_;
v___y_1350_ = v___y_1933_;
v___y_1351_ = v___y_1934_;
v___y_1352_ = v___y_1936_;
v___y_1353_ = v___y_1935_;
v_a_1354_ = v_a_1967_;
goto v___jp_1345_;
}
}
else
{
lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v_a_1970_; 
lean_dec(v_a_1942_);
lean_dec(v_snd_1940_);
lean_dec_ref(v_binderType_1479_);
v___x_1968_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_1969_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_1968_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1970_);
lean_dec_ref(v___x_1969_);
v___y_1346_ = v___y_1929_;
v___y_1347_ = v___y_1932_;
v___y_1348_ = v___y_1931_;
v___y_1349_ = v___y_1930_;
v___y_1350_ = v___y_1933_;
v___y_1351_ = v___y_1934_;
v___y_1352_ = v___y_1936_;
v___y_1353_ = v___y_1935_;
v_a_1354_ = v_a_1970_;
goto v___jp_1345_;
}
}
else
{
lean_object* v_a_1971_; 
lean_dec(v_snd_1940_);
lean_dec_ref(v_binderType_1479_);
v_a_1971_ = lean_ctor_get(v___x_1941_, 0);
lean_inc(v_a_1971_);
lean_dec_ref(v___x_1941_);
v___y_1346_ = v___y_1929_;
v___y_1347_ = v___y_1932_;
v___y_1348_ = v___y_1931_;
v___y_1349_ = v___y_1930_;
v___y_1350_ = v___y_1933_;
v___y_1351_ = v___y_1934_;
v___y_1352_ = v___y_1936_;
v___y_1353_ = v___y_1935_;
v_a_1354_ = v_a_1971_;
goto v___jp_1345_;
}
}
else
{
lean_object* v___x_1972_; 
lean_dec_ref(v_binderType_1479_);
v___x_1972_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1938_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
lean_dec(v___x_1938_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; 
lean_dec_ref(v_expr_1250_);
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1973_);
lean_dec_ref(v___x_1972_);
v___y_1311_ = v___y_1929_;
v___y_1312_ = v___y_1930_;
v___y_1313_ = v___y_1931_;
v___y_1314_ = v___y_1932_;
v___y_1315_ = v___y_1933_;
v___y_1316_ = v___y_1934_;
v___y_1317_ = v___y_1935_;
v___y_1318_ = v___y_1936_;
v_a_1319_ = v_a_1973_;
goto v___jp_1310_;
}
else
{
lean_object* v_a_1974_; 
v_a_1974_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1974_);
lean_dec_ref(v___x_1972_);
v___y_1346_ = v___y_1929_;
v___y_1347_ = v___y_1932_;
v___y_1348_ = v___y_1931_;
v___y_1349_ = v___y_1930_;
v___y_1350_ = v___y_1933_;
v___y_1351_ = v___y_1934_;
v___y_1352_ = v___y_1936_;
v___y_1353_ = v___y_1935_;
v_a_1354_ = v_a_1974_;
goto v___jp_1345_;
}
}
}
else
{
lean_dec_ref(v_binderType_1479_);
lean_dec_ref(v_expr_1250_);
v___y_1322_ = v___y_1929_;
v___y_1323_ = v___y_1932_;
v___y_1324_ = v___y_1931_;
v___y_1325_ = v___y_1930_;
v___y_1326_ = v___y_1933_;
v___y_1327_ = v___y_1934_;
v___y_1328_ = v___y_1936_;
v___y_1329_ = v___y_1935_;
v_a_1330_ = v___y_1928_;
goto v___jp_1321_;
}
}
v___jp_1975_:
{
uint8_t v___x_1985_; 
v___x_1985_ = l_Lean_Exception_isInterrupt(v_a_1984_);
if (v___x_1985_ == 0)
{
uint8_t v___x_1986_; 
lean_inc_ref(v_a_1984_);
v___x_1986_ = l_Lean_Exception_isRuntime(v_a_1984_);
v___y_1928_ = v_a_1984_;
v___y_1929_ = v___y_1976_;
v___y_1930_ = v___y_1979_;
v___y_1931_ = v___y_1978_;
v___y_1932_ = v___y_1977_;
v___y_1933_ = v___y_1980_;
v___y_1934_ = v___y_1981_;
v___y_1935_ = v___y_1983_;
v___y_1936_ = v___y_1982_;
v___y_1937_ = v___x_1986_;
goto v___jp_1927_;
}
else
{
v___y_1928_ = v_a_1984_;
v___y_1929_ = v___y_1976_;
v___y_1930_ = v___y_1979_;
v___y_1931_ = v___y_1978_;
v___y_1932_ = v___y_1977_;
v___y_1933_ = v___y_1980_;
v___y_1934_ = v___y_1981_;
v___y_1935_ = v___y_1983_;
v___y_1936_ = v___y_1982_;
v___y_1937_ = v___x_1985_;
goto v___jp_1927_;
}
}
v___jp_1987_:
{
if (v___y_1997_ == 0)
{
lean_object* v___x_1998_; 
lean_dec_ref(v___y_1992_);
v___x_1998_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_arg_1463_);
if (lean_obj_tag(v___x_1998_) == 1)
{
lean_object* v_val_1999_; lean_object* v_snd_2000_; lean_object* v___x_2001_; 
v_val_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_val_1999_);
lean_dec_ref(v___x_1998_);
v_snd_2000_ = lean_ctor_get(v_val_1999_, 1);
lean_inc(v_snd_2000_);
lean_dec(v_val_1999_);
v___x_2001_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1465_, v_a_1254_);
if (lean_obj_tag(v___x_2001_) == 0)
{
lean_object* v_a_2002_; 
v_a_2002_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2002_);
lean_dec_ref(v___x_2001_);
if (lean_obj_tag(v_a_2002_) == 1)
{
lean_object* v_val_2003_; lean_object* v___x_2004_; 
v_val_2003_ = lean_ctor_get(v_a_2002_, 0);
lean_inc(v_val_2003_);
lean_dec_ref(v_a_2002_);
lean_inc(v_a_1254_);
lean_inc_ref(v_a_1253_);
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
v___x_2004_ = lean_infer_type(v_val_2003_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v___x_2006_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref(v___x_2004_);
v___x_2006_ = l_Lean_Meta_mkNumeral(v_a_2005_, v_snd_2000_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v___x_2008_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref(v___x_2006_);
lean_inc_ref(v_binderType_1479_);
v___x_2008_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2007_, v_binderType_1479_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2010_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2009_);
lean_dec_ref(v___x_2008_);
lean_inc_ref(v_arg_1463_);
v___x_2010_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1463_, v_a_2009_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref(v___x_2010_);
if (lean_obj_tag(v_a_2011_) == 1)
{
lean_object* v_val_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v_val_2012_ = lean_ctor_get(v_a_2011_, 0);
lean_inc(v_val_2012_);
lean_dec_ref(v_a_2011_);
lean_inc_ref(v_arg_1465_);
lean_inc_ref(v_fn_1464_);
v___x_2013_ = l_Lean_Expr_app___override(v_fn_1464_, v_arg_1465_);
v___x_2014_ = lean_box(0);
v___x_2015_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2015_, 0, v___x_2013_);
lean_ctor_set(v___x_2015_, 1, v___x_2014_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*2, v___y_1996_);
v___x_2016_ = l_Lean_Meta_Simp_mkCongr(v___x_2015_, v_val_2012_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; 
lean_dec_ref(v_binderType_1479_);
lean_dec_ref(v_expr_1250_);
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2017_);
lean_dec_ref(v___x_2016_);
v___y_1300_ = v___y_1988_;
v___y_1301_ = v___y_1991_;
v___y_1302_ = v___y_1990_;
v___y_1303_ = v___y_1989_;
v___y_1304_ = v___y_1993_;
v___y_1305_ = v___y_1994_;
v___y_1306_ = v___y_1996_;
v___y_1307_ = v___y_1995_;
v_a_1308_ = v_a_2017_;
goto v___jp_1299_;
}
else
{
lean_object* v_a_2018_; 
v_a_2018_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2018_);
lean_dec_ref(v___x_2016_);
v___y_1976_ = v___y_1988_;
v___y_1977_ = v___y_1991_;
v___y_1978_ = v___y_1990_;
v___y_1979_ = v___y_1989_;
v___y_1980_ = v___y_1993_;
v___y_1981_ = v___y_1994_;
v___y_1982_ = v___y_1996_;
v___y_1983_ = v___y_1995_;
v_a_1984_ = v_a_2018_;
goto v___jp_1975_;
}
}
else
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v_a_2021_; 
lean_dec(v_a_2011_);
v___x_2019_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2020_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2019_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v_a_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_a_2021_);
lean_dec_ref(v___x_2020_);
v___y_1976_ = v___y_1988_;
v___y_1977_ = v___y_1991_;
v___y_1978_ = v___y_1990_;
v___y_1979_ = v___y_1989_;
v___y_1980_ = v___y_1993_;
v___y_1981_ = v___y_1994_;
v___y_1982_ = v___y_1996_;
v___y_1983_ = v___y_1995_;
v_a_1984_ = v_a_2021_;
goto v___jp_1975_;
}
}
else
{
lean_object* v_a_2022_; 
v_a_2022_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2022_);
lean_dec_ref(v___x_2010_);
v___y_1976_ = v___y_1988_;
v___y_1977_ = v___y_1991_;
v___y_1978_ = v___y_1990_;
v___y_1979_ = v___y_1989_;
v___y_1980_ = v___y_1993_;
v___y_1981_ = v___y_1994_;
v___y_1982_ = v___y_1996_;
v___y_1983_ = v___y_1995_;
v_a_1984_ = v_a_2022_;
goto v___jp_1975_;
}
}
else
{
lean_object* v_a_2023_; 
v_a_2023_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2023_);
lean_dec_ref(v___x_2008_);
v___y_1976_ = v___y_1988_;
v___y_1977_ = v___y_1991_;
v___y_1978_ = v___y_1990_;
v___y_1979_ = v___y_1989_;
v___y_1980_ = v___y_1993_;
v___y_1981_ = v___y_1994_;
v___y_1982_ = v___y_1996_;
v___y_1983_ = v___y_1995_;
v_a_1984_ = v_a_2023_;
goto v___jp_1975_;
}
}
else
{
lean_object* v_a_2024_; 
v_a_2024_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2024_);
lean_dec_ref(v___x_2006_);
v___y_1976_ = v___y_1988_;
v___y_1977_ = v___y_1991_;
v___y_1978_ = v___y_1990_;
v___y_1979_ = v___y_1989_;
v___y_1980_ = v___y_1993_;
v___y_1981_ = v___y_1994_;
v___y_1982_ = v___y_1996_;
v___y_1983_ = v___y_1995_;
v_a_1984_ = v_a_2024_;
goto v___jp_1975_;
}
}
else
{
lean_object* v_a_2025_; 
lean_dec(v_snd_2000_);
v_a_2025_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2025_);
lean_dec_ref(v___x_2004_);
v___y_1976_ = v___y_1988_;
v___y_1977_ = v___y_1991_;
v___y_1978_ = v___y_1990_;
v___y_1979_ = v___y_1989_;
v___y_1980_ = v___y_1993_;
v___y_1981_ = v___y_1994_;
v___y_1982_ = v___y_1996_;
v___y_1983_ = v___y_1995_;
v_a_1984_ = v_a_2025_;
goto v___jp_1975_;
}
}
else
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v_a_2028_; 
lean_dec(v_a_2002_);
lean_dec(v_snd_2000_);
v___x_2026_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2027_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2026_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref(v___x_2027_);
v___y_1976_ = v___y_1988_;
v___y_1977_ = v___y_1991_;
v___y_1978_ = v___y_1990_;
v___y_1979_ = v___y_1989_;
v___y_1980_ = v___y_1993_;
v___y_1981_ = v___y_1994_;
v___y_1982_ = v___y_1996_;
v___y_1983_ = v___y_1995_;
v_a_1984_ = v_a_2028_;
goto v___jp_1975_;
}
}
else
{
lean_object* v_a_2029_; 
lean_dec(v_snd_2000_);
v_a_2029_ = lean_ctor_get(v___x_2001_, 0);
lean_inc(v_a_2029_);
lean_dec_ref(v___x_2001_);
v___y_1976_ = v___y_1988_;
v___y_1977_ = v___y_1991_;
v___y_1978_ = v___y_1990_;
v___y_1979_ = v___y_1989_;
v___y_1980_ = v___y_1993_;
v___y_1981_ = v___y_1994_;
v___y_1982_ = v___y_1996_;
v___y_1983_ = v___y_1995_;
v_a_1984_ = v_a_2029_;
goto v___jp_1975_;
}
}
else
{
lean_object* v___x_2030_; 
v___x_2030_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__0(v___x_1998_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
lean_dec(v___x_1998_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; 
lean_dec_ref(v_binderType_1479_);
lean_dec_ref(v_expr_1250_);
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_a_2031_);
lean_dec_ref(v___x_2030_);
v___y_1311_ = v___y_1988_;
v___y_1312_ = v___y_1989_;
v___y_1313_ = v___y_1990_;
v___y_1314_ = v___y_1991_;
v___y_1315_ = v___y_1993_;
v___y_1316_ = v___y_1994_;
v___y_1317_ = v___y_1995_;
v___y_1318_ = v___y_1996_;
v_a_1319_ = v_a_2031_;
goto v___jp_1310_;
}
else
{
lean_object* v_a_2032_; 
v_a_2032_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_a_2032_);
lean_dec_ref(v___x_2030_);
v___y_1976_ = v___y_1988_;
v___y_1977_ = v___y_1991_;
v___y_1978_ = v___y_1990_;
v___y_1979_ = v___y_1989_;
v___y_1980_ = v___y_1993_;
v___y_1981_ = v___y_1994_;
v___y_1982_ = v___y_1996_;
v___y_1983_ = v___y_1995_;
v_a_1984_ = v_a_2032_;
goto v___jp_1975_;
}
}
}
else
{
lean_dec_ref(v_binderType_1479_);
lean_dec_ref(v_expr_1250_);
v___y_1322_ = v___y_1988_;
v___y_1323_ = v___y_1991_;
v___y_1324_ = v___y_1990_;
v___y_1325_ = v___y_1989_;
v___y_1326_ = v___y_1993_;
v___y_1327_ = v___y_1994_;
v___y_1328_ = v___y_1996_;
v___y_1329_ = v___y_1995_;
v_a_1330_ = v___y_1992_;
goto v___jp_1321_;
}
}
v___jp_2033_:
{
uint8_t v___x_2043_; 
v___x_2043_ = l_Lean_Exception_isInterrupt(v_a_2042_);
if (v___x_2043_ == 0)
{
uint8_t v___x_2044_; 
lean_inc_ref(v_a_2042_);
v___x_2044_ = l_Lean_Exception_isRuntime(v_a_2042_);
v___y_1988_ = v___y_2034_;
v___y_1989_ = v___y_2037_;
v___y_1990_ = v___y_2036_;
v___y_1991_ = v___y_2035_;
v___y_1992_ = v_a_2042_;
v___y_1993_ = v___y_2038_;
v___y_1994_ = v___y_2039_;
v___y_1995_ = v___y_2041_;
v___y_1996_ = v___y_2040_;
v___y_1997_ = v___x_2044_;
goto v___jp_1987_;
}
else
{
v___y_1988_ = v___y_2034_;
v___y_1989_ = v___y_2037_;
v___y_1990_ = v___y_2036_;
v___y_1991_ = v___y_2035_;
v___y_1992_ = v_a_2042_;
v___y_1993_ = v___y_2038_;
v___y_1994_ = v___y_2039_;
v___y_1995_ = v___y_2041_;
v___y_1996_ = v___y_2040_;
v___y_1997_ = v___x_2043_;
goto v___jp_1987_;
}
}
v___jp_2045_:
{
if (lean_obj_tag(v___y_2054_) == 0)
{
lean_object* v_a_2055_; 
lean_dec_ref(v_binderType_1479_);
lean_dec_ref(v_expr_1250_);
v_a_2055_ = lean_ctor_get(v___y_2054_, 0);
lean_inc(v_a_2055_);
lean_dec_ref(v___y_2054_);
v___y_1300_ = v___y_2046_;
v___y_1301_ = v___y_2049_;
v___y_1302_ = v___y_2048_;
v___y_1303_ = v___y_2047_;
v___y_1304_ = v___y_2050_;
v___y_1305_ = v___y_2051_;
v___y_1306_ = v___y_2053_;
v___y_1307_ = v___y_2052_;
v_a_1308_ = v_a_2055_;
goto v___jp_1299_;
}
else
{
lean_object* v_a_2056_; 
v_a_2056_ = lean_ctor_get(v___y_2054_, 0);
lean_inc(v_a_2056_);
lean_dec_ref(v___y_2054_);
v___y_2034_ = v___y_2046_;
v___y_2035_ = v___y_2049_;
v___y_2036_ = v___y_2048_;
v___y_2037_ = v___y_2047_;
v___y_2038_ = v___y_2050_;
v___y_2039_ = v___y_2051_;
v___y_2040_ = v___y_2053_;
v___y_2041_ = v___y_2052_;
v_a_2042_ = v_a_2056_;
goto v___jp_2033_;
}
}
v___jp_2057_:
{
if (v___y_2069_ == 0)
{
lean_object* v___x_2070_; 
lean_dec_ref(v___y_2058_);
v___x_2070_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v___y_2065_, v___y_2059_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; lean_object* v___x_2072_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2071_);
lean_dec_ref(v___x_2070_);
lean_inc_ref(v_binderType_1479_);
v___x_2072_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2071_, v_binderType_1479_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v___x_2074_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2073_);
lean_dec_ref(v___x_2072_);
lean_inc_ref(v_arg_1463_);
v___x_2074_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1463_, v_a_2073_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_object* v_a_2075_; 
v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2075_);
lean_dec_ref(v___x_2074_);
if (lean_obj_tag(v_a_2075_) == 1)
{
lean_object* v_val_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v_val_2076_ = lean_ctor_get(v_a_2075_, 0);
lean_inc(v_val_2076_);
lean_dec_ref(v_a_2075_);
lean_inc_ref(v_arg_1465_);
lean_inc_ref(v_fn_1464_);
v___x_2077_ = l_Lean_Expr_app___override(v_fn_1464_, v_arg_1465_);
v___x_2078_ = lean_box(0);
v___x_2079_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2079_, 0, v___x_2077_);
lean_ctor_set(v___x_2079_, 1, v___x_2078_);
lean_ctor_set_uint8(v___x_2079_, sizeof(void*)*2, v___y_2068_);
v___x_2080_ = l_Lean_Meta_Simp_mkCongr(v___x_2079_, v_val_2076_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v___y_2046_ = v___y_2060_;
v___y_2047_ = v___y_2063_;
v___y_2048_ = v___y_2062_;
v___y_2049_ = v___y_2061_;
v___y_2050_ = v___y_2064_;
v___y_2051_ = v___y_2066_;
v___y_2052_ = v___y_2067_;
v___y_2053_ = v___y_2068_;
v___y_2054_ = v___x_2080_;
goto v___jp_2045_;
}
else
{
lean_object* v___x_2081_; lean_object* v___x_2082_; 
lean_dec(v_a_2075_);
v___x_2081_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2082_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2081_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v___y_2046_ = v___y_2060_;
v___y_2047_ = v___y_2063_;
v___y_2048_ = v___y_2062_;
v___y_2049_ = v___y_2061_;
v___y_2050_ = v___y_2064_;
v___y_2051_ = v___y_2066_;
v___y_2052_ = v___y_2067_;
v___y_2053_ = v___y_2068_;
v___y_2054_ = v___x_2082_;
goto v___jp_2045_;
}
}
else
{
lean_object* v_a_2083_; 
v_a_2083_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_a_2083_);
lean_dec_ref(v___x_2074_);
v___y_2034_ = v___y_2060_;
v___y_2035_ = v___y_2061_;
v___y_2036_ = v___y_2062_;
v___y_2037_ = v___y_2063_;
v___y_2038_ = v___y_2064_;
v___y_2039_ = v___y_2066_;
v___y_2040_ = v___y_2068_;
v___y_2041_ = v___y_2067_;
v_a_2042_ = v_a_2083_;
goto v___jp_2033_;
}
}
else
{
lean_object* v_a_2084_; 
v_a_2084_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2084_);
lean_dec_ref(v___x_2072_);
v___y_2034_ = v___y_2060_;
v___y_2035_ = v___y_2061_;
v___y_2036_ = v___y_2062_;
v___y_2037_ = v___y_2063_;
v___y_2038_ = v___y_2064_;
v___y_2039_ = v___y_2066_;
v___y_2040_ = v___y_2068_;
v___y_2041_ = v___y_2067_;
v_a_2042_ = v_a_2084_;
goto v___jp_2033_;
}
}
else
{
lean_object* v_a_2085_; 
v_a_2085_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2085_);
lean_dec_ref(v___x_2070_);
v___y_2034_ = v___y_2060_;
v___y_2035_ = v___y_2061_;
v___y_2036_ = v___y_2062_;
v___y_2037_ = v___y_2063_;
v___y_2038_ = v___y_2064_;
v___y_2039_ = v___y_2066_;
v___y_2040_ = v___y_2068_;
v___y_2041_ = v___y_2067_;
v_a_2042_ = v_a_2085_;
goto v___jp_2033_;
}
}
else
{
lean_dec_ref(v___y_2065_);
lean_dec_ref(v___y_2059_);
v___y_2034_ = v___y_2060_;
v___y_2035_ = v___y_2061_;
v___y_2036_ = v___y_2062_;
v___y_2037_ = v___y_2063_;
v___y_2038_ = v___y_2064_;
v___y_2039_ = v___y_2066_;
v___y_2040_ = v___y_2068_;
v___y_2041_ = v___y_2067_;
v_a_2042_ = v___y_2058_;
goto v___jp_2033_;
}
}
v___jp_2086_:
{
uint8_t v___x_2098_; 
v___x_2098_ = l_Lean_Exception_isInterrupt(v_a_2097_);
if (v___x_2098_ == 0)
{
uint8_t v___x_2099_; 
lean_inc_ref(v_a_2097_);
v___x_2099_ = l_Lean_Exception_isRuntime(v_a_2097_);
v___y_2058_ = v_a_2097_;
v___y_2059_ = v___y_2087_;
v___y_2060_ = v___y_2088_;
v___y_2061_ = v___y_2091_;
v___y_2062_ = v___y_2090_;
v___y_2063_ = v___y_2089_;
v___y_2064_ = v___y_2093_;
v___y_2065_ = v___y_2092_;
v___y_2066_ = v___y_2094_;
v___y_2067_ = v___y_2096_;
v___y_2068_ = v___y_2095_;
v___y_2069_ = v___x_2099_;
goto v___jp_2057_;
}
else
{
v___y_2058_ = v_a_2097_;
v___y_2059_ = v___y_2087_;
v___y_2060_ = v___y_2088_;
v___y_2061_ = v___y_2091_;
v___y_2062_ = v___y_2090_;
v___y_2063_ = v___y_2089_;
v___y_2064_ = v___y_2093_;
v___y_2065_ = v___y_2092_;
v___y_2066_ = v___y_2094_;
v___y_2067_ = v___y_2096_;
v___y_2068_ = v___y_2095_;
v___y_2069_ = v___x_2098_;
goto v___jp_2057_;
}
}
v___jp_2100_:
{
if (lean_obj_tag(v___y_2111_) == 0)
{
lean_object* v_a_2112_; 
lean_dec_ref(v___y_2106_);
lean_dec_ref(v___y_2101_);
lean_dec_ref(v_binderType_1479_);
lean_dec_ref(v_expr_1250_);
v_a_2112_ = lean_ctor_get(v___y_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref(v___y_2111_);
v___y_1300_ = v___y_2102_;
v___y_1301_ = v___y_2105_;
v___y_1302_ = v___y_2104_;
v___y_1303_ = v___y_2103_;
v___y_1304_ = v___y_2107_;
v___y_1305_ = v___y_2108_;
v___y_1306_ = v___y_2110_;
v___y_1307_ = v___y_2109_;
v_a_1308_ = v_a_2112_;
goto v___jp_1299_;
}
else
{
lean_object* v_a_2113_; 
v_a_2113_ = lean_ctor_get(v___y_2111_, 0);
lean_inc(v_a_2113_);
lean_dec_ref(v___y_2111_);
v___y_2087_ = v___y_2101_;
v___y_2088_ = v___y_2102_;
v___y_2089_ = v___y_2103_;
v___y_2090_ = v___y_2104_;
v___y_2091_ = v___y_2105_;
v___y_2092_ = v___y_2106_;
v___y_2093_ = v___y_2107_;
v___y_2094_ = v___y_2108_;
v___y_2095_ = v___y_2110_;
v___y_2096_ = v___y_2109_;
v_a_2097_ = v_a_2113_;
goto v___jp_2086_;
}
}
v___jp_2114_:
{
lean_object* v___x_2121_; lean_object* v_a_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; 
v___x_2121_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v_a_1254_);
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
lean_dec_ref(v___x_2121_);
v___x_2123_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2124_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v___y_2116_, v___x_2123_);
if (v___x_2124_ == 0)
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = lean_io_mono_nanos_now();
v___x_2126_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1465_, v_a_1254_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref(v___x_2126_);
if (lean_obj_tag(v_a_2127_) == 1)
{
lean_object* v_val_2128_; lean_object* v___x_2129_; 
v_val_2128_ = lean_ctor_get(v_a_2127_, 0);
lean_inc(v_val_2128_);
lean_dec_ref(v_a_2127_);
v___x_2129_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1463_, v_a_1254_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref(v___x_2129_);
if (lean_obj_tag(v_a_2130_) == 1)
{
lean_object* v_val_2131_; lean_object* v___x_2132_; 
v_val_2131_ = lean_ctor_get(v_a_2130_, 0);
lean_inc(v_val_2131_);
lean_dec_ref(v_a_2130_);
lean_inc(v_a_1254_);
lean_inc_ref(v_a_1253_);
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
lean_inc(v_val_2128_);
v___x_2132_ = lean_infer_type(v_val_2128_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2134_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref(v___x_2132_);
lean_inc(v_a_1254_);
lean_inc_ref(v_a_1253_);
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
lean_inc(v_val_2131_);
v___x_2134_ = lean_infer_type(v_val_2131_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2136_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref(v___x_2134_);
v___x_2136_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_val_2128_, v_a_2135_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2138_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref(v___x_2136_);
lean_inc_ref(v_binderType_1479_);
v___x_2138_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2137_, v_binderType_1479_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2140_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2139_);
lean_dec_ref(v___x_2138_);
lean_inc_ref(v_arg_1465_);
v___x_2140_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1465_, v_a_2139_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref(v___x_2140_);
if (lean_obj_tag(v_a_2141_) == 1)
{
lean_object* v_val_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v_val_2142_ = lean_ctor_get(v_a_2141_, 0);
lean_inc(v_val_2142_);
lean_dec_ref(v_a_2141_);
v___x_2143_ = lean_box(0);
lean_inc_ref(v_fn_1464_);
v___x_2144_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2144_, 0, v_fn_1464_);
lean_ctor_set(v___x_2144_, 1, v___x_2143_);
lean_ctor_set_uint8(v___x_2144_, sizeof(void*)*2, v___y_2119_);
v___x_2145_ = l_Lean_Meta_Simp_mkCongr(v___x_2144_, v_val_2142_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; lean_object* v___x_2147_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_a_2146_);
lean_dec_ref(v___x_2145_);
lean_inc_ref(v_arg_1463_);
v___x_2147_ = l_Lean_Meta_Simp_mkCongrFun(v_a_2146_, v_arg_1463_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v___y_1914_ = v___x_2125_;
v___y_1915_ = v_a_2133_;
v___y_1916_ = v___y_2115_;
v___y_1917_ = v_val_2131_;
v___y_1918_ = v_a_2122_;
v___y_1919_ = v___y_2116_;
v___y_1920_ = v___y_2117_;
v___y_1921_ = v___y_2118_;
v___y_1922_ = v___y_2120_;
v___y_1923_ = v___y_2119_;
v___y_1924_ = v___x_2147_;
goto v___jp_1913_;
}
else
{
v___y_1914_ = v___x_2125_;
v___y_1915_ = v_a_2133_;
v___y_1916_ = v___y_2115_;
v___y_1917_ = v_val_2131_;
v___y_1918_ = v_a_2122_;
v___y_1919_ = v___y_2116_;
v___y_1920_ = v___y_2117_;
v___y_1921_ = v___y_2118_;
v___y_1922_ = v___y_2120_;
v___y_1923_ = v___y_2119_;
v___y_1924_ = v___x_2145_;
goto v___jp_1913_;
}
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
lean_dec(v_a_2141_);
v___x_2148_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2149_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2148_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v___y_1914_ = v___x_2125_;
v___y_1915_ = v_a_2133_;
v___y_1916_ = v___y_2115_;
v___y_1917_ = v_val_2131_;
v___y_1918_ = v_a_2122_;
v___y_1919_ = v___y_2116_;
v___y_1920_ = v___y_2117_;
v___y_1921_ = v___y_2118_;
v___y_1922_ = v___y_2120_;
v___y_1923_ = v___y_2119_;
v___y_1924_ = v___x_2149_;
goto v___jp_1913_;
}
}
else
{
lean_object* v_a_2150_; 
v_a_2150_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2150_);
lean_dec_ref(v___x_2140_);
v___y_1900_ = v___x_2125_;
v___y_1901_ = v_a_2133_;
v___y_1902_ = v___y_2115_;
v___y_1903_ = v_val_2131_;
v___y_1904_ = v_a_2122_;
v___y_1905_ = v___y_2116_;
v___y_1906_ = v___y_2117_;
v___y_1907_ = v___y_2118_;
v___y_1908_ = v___y_2119_;
v___y_1909_ = v___y_2120_;
v_a_1910_ = v_a_2150_;
goto v___jp_1899_;
}
}
else
{
lean_object* v_a_2151_; 
v_a_2151_ = lean_ctor_get(v___x_2138_, 0);
lean_inc(v_a_2151_);
lean_dec_ref(v___x_2138_);
v___y_1900_ = v___x_2125_;
v___y_1901_ = v_a_2133_;
v___y_1902_ = v___y_2115_;
v___y_1903_ = v_val_2131_;
v___y_1904_ = v_a_2122_;
v___y_1905_ = v___y_2116_;
v___y_1906_ = v___y_2117_;
v___y_1907_ = v___y_2118_;
v___y_1908_ = v___y_2119_;
v___y_1909_ = v___y_2120_;
v_a_1910_ = v_a_2151_;
goto v___jp_1899_;
}
}
else
{
lean_object* v_a_2152_; 
v_a_2152_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2152_);
lean_dec_ref(v___x_2136_);
v___y_1900_ = v___x_2125_;
v___y_1901_ = v_a_2133_;
v___y_1902_ = v___y_2115_;
v___y_1903_ = v_val_2131_;
v___y_1904_ = v_a_2122_;
v___y_1905_ = v___y_2116_;
v___y_1906_ = v___y_2117_;
v___y_1907_ = v___y_2118_;
v___y_1908_ = v___y_2119_;
v___y_1909_ = v___y_2120_;
v_a_1910_ = v_a_2152_;
goto v___jp_1899_;
}
}
else
{
lean_object* v_a_2153_; 
lean_dec(v_a_2133_);
lean_dec(v_val_2131_);
lean_dec(v_val_2128_);
v_a_2153_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2153_);
lean_dec_ref(v___x_2134_);
v___y_1847_ = v___x_2125_;
v___y_1848_ = v___y_2115_;
v___y_1849_ = v___y_2116_;
v___y_1850_ = v_a_2122_;
v___y_1851_ = v___y_2117_;
v___y_1852_ = v___y_2118_;
v___y_1853_ = v___y_2119_;
v___y_1854_ = v___y_2120_;
v_a_1855_ = v_a_2153_;
goto v___jp_1846_;
}
}
else
{
lean_object* v_a_2154_; 
lean_dec(v_val_2131_);
lean_dec(v_val_2128_);
v_a_2154_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2154_);
lean_dec_ref(v___x_2132_);
v___y_1847_ = v___x_2125_;
v___y_1848_ = v___y_2115_;
v___y_1849_ = v___y_2116_;
v___y_1850_ = v_a_2122_;
v___y_1851_ = v___y_2117_;
v___y_1852_ = v___y_2118_;
v___y_1853_ = v___y_2119_;
v___y_1854_ = v___y_2120_;
v_a_1855_ = v_a_2154_;
goto v___jp_1846_;
}
}
else
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v_a_2157_; 
lean_dec(v_a_2130_);
lean_dec(v_val_2128_);
v___x_2155_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2156_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2155_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_a_2157_);
lean_dec_ref(v___x_2156_);
v___y_1847_ = v___x_2125_;
v___y_1848_ = v___y_2115_;
v___y_1849_ = v___y_2116_;
v___y_1850_ = v_a_2122_;
v___y_1851_ = v___y_2117_;
v___y_1852_ = v___y_2118_;
v___y_1853_ = v___y_2119_;
v___y_1854_ = v___y_2120_;
v_a_1855_ = v_a_2157_;
goto v___jp_1846_;
}
}
else
{
lean_object* v_a_2158_; 
lean_dec(v_val_2128_);
v_a_2158_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2158_);
lean_dec_ref(v___x_2129_);
v___y_1847_ = v___x_2125_;
v___y_1848_ = v___y_2115_;
v___y_1849_ = v___y_2116_;
v___y_1850_ = v_a_2122_;
v___y_1851_ = v___y_2117_;
v___y_1852_ = v___y_2118_;
v___y_1853_ = v___y_2119_;
v___y_1854_ = v___y_2120_;
v_a_1855_ = v_a_2158_;
goto v___jp_1846_;
}
}
else
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v_a_2161_; 
lean_dec(v_a_2127_);
v___x_2159_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2160_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2159_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2161_);
lean_dec_ref(v___x_2160_);
v___y_1847_ = v___x_2125_;
v___y_1848_ = v___y_2115_;
v___y_1849_ = v___y_2116_;
v___y_1850_ = v_a_2122_;
v___y_1851_ = v___y_2117_;
v___y_1852_ = v___y_2118_;
v___y_1853_ = v___y_2119_;
v___y_1854_ = v___y_2120_;
v_a_1855_ = v_a_2161_;
goto v___jp_1846_;
}
}
else
{
lean_object* v_a_2162_; 
v_a_2162_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2162_);
lean_dec_ref(v___x_2126_);
v___y_1847_ = v___x_2125_;
v___y_1848_ = v___y_2115_;
v___y_1849_ = v___y_2116_;
v___y_1850_ = v_a_2122_;
v___y_1851_ = v___y_2117_;
v___y_1852_ = v___y_2118_;
v___y_1853_ = v___y_2119_;
v___y_1854_ = v___y_2120_;
v_a_1855_ = v_a_2162_;
goto v___jp_1846_;
}
}
else
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
v___x_2163_ = lean_io_get_num_heartbeats();
v___x_2164_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1465_, v_a_1254_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2165_);
lean_dec_ref(v___x_2164_);
if (lean_obj_tag(v_a_2165_) == 1)
{
lean_object* v_val_2166_; lean_object* v___x_2167_; 
v_val_2166_ = lean_ctor_get(v_a_2165_, 0);
lean_inc(v_val_2166_);
lean_dec_ref(v_a_2165_);
v___x_2167_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1463_, v_a_1254_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2168_);
lean_dec_ref(v___x_2167_);
if (lean_obj_tag(v_a_2168_) == 1)
{
lean_object* v_val_2169_; lean_object* v___x_2170_; 
v_val_2169_ = lean_ctor_get(v_a_2168_, 0);
lean_inc(v_val_2169_);
lean_dec_ref(v_a_2168_);
lean_inc(v_a_1254_);
lean_inc_ref(v_a_1253_);
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
lean_inc(v_val_2166_);
v___x_2170_ = lean_infer_type(v_val_2166_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2170_) == 0)
{
lean_object* v_a_2171_; lean_object* v___x_2172_; 
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2171_);
lean_dec_ref(v___x_2170_);
lean_inc(v_a_1254_);
lean_inc_ref(v_a_1253_);
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
lean_inc(v_val_2169_);
v___x_2172_ = lean_infer_type(v_val_2169_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2172_) == 0)
{
lean_object* v_a_2173_; lean_object* v___x_2174_; 
v_a_2173_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2173_);
lean_dec_ref(v___x_2172_);
v___x_2174_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_val_2166_, v_a_2173_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2176_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref(v___x_2174_);
lean_inc_ref(v_binderType_1479_);
v___x_2176_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2175_, v_binderType_1479_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___x_2178_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref(v___x_2176_);
lean_inc_ref(v_arg_1465_);
v___x_2178_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1465_, v_a_2177_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2179_);
lean_dec_ref(v___x_2178_);
if (lean_obj_tag(v_a_2179_) == 1)
{
lean_object* v_val_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v_val_2180_ = lean_ctor_get(v_a_2179_, 0);
lean_inc(v_val_2180_);
lean_dec_ref(v_a_2179_);
v___x_2181_ = lean_box(0);
lean_inc_ref(v_fn_1464_);
v___x_2182_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2182_, 0, v_fn_1464_);
lean_ctor_set(v___x_2182_, 1, v___x_2181_);
lean_ctor_set_uint8(v___x_2182_, sizeof(void*)*2, v___y_2119_);
v___x_2183_ = l_Lean_Meta_Simp_mkCongr(v___x_2182_, v_val_2180_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2183_) == 0)
{
lean_object* v_a_2184_; lean_object* v___x_2185_; 
v_a_2184_ = lean_ctor_get(v___x_2183_, 0);
lean_inc(v_a_2184_);
lean_dec_ref(v___x_2183_);
lean_inc_ref(v_arg_1463_);
v___x_2185_ = l_Lean_Meta_Simp_mkCongrFun(v_a_2184_, v_arg_1463_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v___y_2101_ = v_a_2171_;
v___y_2102_ = v___y_2115_;
v___y_2103_ = v_a_2122_;
v___y_2104_ = v___y_2116_;
v___y_2105_ = v___x_2163_;
v___y_2106_ = v_val_2169_;
v___y_2107_ = v___y_2117_;
v___y_2108_ = v___y_2118_;
v___y_2109_ = v___y_2120_;
v___y_2110_ = v___y_2119_;
v___y_2111_ = v___x_2185_;
goto v___jp_2100_;
}
else
{
v___y_2101_ = v_a_2171_;
v___y_2102_ = v___y_2115_;
v___y_2103_ = v_a_2122_;
v___y_2104_ = v___y_2116_;
v___y_2105_ = v___x_2163_;
v___y_2106_ = v_val_2169_;
v___y_2107_ = v___y_2117_;
v___y_2108_ = v___y_2118_;
v___y_2109_ = v___y_2120_;
v___y_2110_ = v___y_2119_;
v___y_2111_ = v___x_2183_;
goto v___jp_2100_;
}
}
else
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
lean_dec(v_a_2179_);
v___x_2186_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2187_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2186_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v___y_2101_ = v_a_2171_;
v___y_2102_ = v___y_2115_;
v___y_2103_ = v_a_2122_;
v___y_2104_ = v___y_2116_;
v___y_2105_ = v___x_2163_;
v___y_2106_ = v_val_2169_;
v___y_2107_ = v___y_2117_;
v___y_2108_ = v___y_2118_;
v___y_2109_ = v___y_2120_;
v___y_2110_ = v___y_2119_;
v___y_2111_ = v___x_2187_;
goto v___jp_2100_;
}
}
else
{
lean_object* v_a_2188_; 
v_a_2188_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2188_);
lean_dec_ref(v___x_2178_);
v___y_2087_ = v_a_2171_;
v___y_2088_ = v___y_2115_;
v___y_2089_ = v_a_2122_;
v___y_2090_ = v___y_2116_;
v___y_2091_ = v___x_2163_;
v___y_2092_ = v_val_2169_;
v___y_2093_ = v___y_2117_;
v___y_2094_ = v___y_2118_;
v___y_2095_ = v___y_2119_;
v___y_2096_ = v___y_2120_;
v_a_2097_ = v_a_2188_;
goto v___jp_2086_;
}
}
else
{
lean_object* v_a_2189_; 
v_a_2189_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2189_);
lean_dec_ref(v___x_2176_);
v___y_2087_ = v_a_2171_;
v___y_2088_ = v___y_2115_;
v___y_2089_ = v_a_2122_;
v___y_2090_ = v___y_2116_;
v___y_2091_ = v___x_2163_;
v___y_2092_ = v_val_2169_;
v___y_2093_ = v___y_2117_;
v___y_2094_ = v___y_2118_;
v___y_2095_ = v___y_2119_;
v___y_2096_ = v___y_2120_;
v_a_2097_ = v_a_2189_;
goto v___jp_2086_;
}
}
else
{
lean_object* v_a_2190_; 
v_a_2190_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2190_);
lean_dec_ref(v___x_2174_);
v___y_2087_ = v_a_2171_;
v___y_2088_ = v___y_2115_;
v___y_2089_ = v_a_2122_;
v___y_2090_ = v___y_2116_;
v___y_2091_ = v___x_2163_;
v___y_2092_ = v_val_2169_;
v___y_2093_ = v___y_2117_;
v___y_2094_ = v___y_2118_;
v___y_2095_ = v___y_2119_;
v___y_2096_ = v___y_2120_;
v_a_2097_ = v_a_2190_;
goto v___jp_2086_;
}
}
else
{
lean_object* v_a_2191_; 
lean_dec(v_a_2171_);
lean_dec(v_val_2169_);
lean_dec(v_val_2166_);
v_a_2191_ = lean_ctor_get(v___x_2172_, 0);
lean_inc(v_a_2191_);
lean_dec_ref(v___x_2172_);
v___y_2034_ = v___y_2115_;
v___y_2035_ = v___x_2163_;
v___y_2036_ = v___y_2116_;
v___y_2037_ = v_a_2122_;
v___y_2038_ = v___y_2117_;
v___y_2039_ = v___y_2118_;
v___y_2040_ = v___y_2119_;
v___y_2041_ = v___y_2120_;
v_a_2042_ = v_a_2191_;
goto v___jp_2033_;
}
}
else
{
lean_object* v_a_2192_; 
lean_dec(v_val_2169_);
lean_dec(v_val_2166_);
v_a_2192_ = lean_ctor_get(v___x_2170_, 0);
lean_inc(v_a_2192_);
lean_dec_ref(v___x_2170_);
v___y_2034_ = v___y_2115_;
v___y_2035_ = v___x_2163_;
v___y_2036_ = v___y_2116_;
v___y_2037_ = v_a_2122_;
v___y_2038_ = v___y_2117_;
v___y_2039_ = v___y_2118_;
v___y_2040_ = v___y_2119_;
v___y_2041_ = v___y_2120_;
v_a_2042_ = v_a_2192_;
goto v___jp_2033_;
}
}
else
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v_a_2195_; 
lean_dec(v_a_2168_);
lean_dec(v_val_2166_);
v___x_2193_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2194_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2193_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref(v___x_2194_);
v___y_2034_ = v___y_2115_;
v___y_2035_ = v___x_2163_;
v___y_2036_ = v___y_2116_;
v___y_2037_ = v_a_2122_;
v___y_2038_ = v___y_2117_;
v___y_2039_ = v___y_2118_;
v___y_2040_ = v___y_2119_;
v___y_2041_ = v___y_2120_;
v_a_2042_ = v_a_2195_;
goto v___jp_2033_;
}
}
else
{
lean_object* v_a_2196_; 
lean_dec(v_val_2166_);
v_a_2196_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_a_2196_);
lean_dec_ref(v___x_2167_);
v___y_2034_ = v___y_2115_;
v___y_2035_ = v___x_2163_;
v___y_2036_ = v___y_2116_;
v___y_2037_ = v_a_2122_;
v___y_2038_ = v___y_2117_;
v___y_2039_ = v___y_2118_;
v___y_2040_ = v___y_2119_;
v___y_2041_ = v___y_2120_;
v_a_2042_ = v_a_2196_;
goto v___jp_2033_;
}
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v_a_2199_; 
lean_dec(v_a_2165_);
v___x_2197_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2198_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2197_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref(v___x_2198_);
v___y_2034_ = v___y_2115_;
v___y_2035_ = v___x_2163_;
v___y_2036_ = v___y_2116_;
v___y_2037_ = v_a_2122_;
v___y_2038_ = v___y_2117_;
v___y_2039_ = v___y_2118_;
v___y_2040_ = v___y_2119_;
v___y_2041_ = v___y_2120_;
v_a_2042_ = v_a_2199_;
goto v___jp_2033_;
}
}
else
{
lean_object* v_a_2200_; 
v_a_2200_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2200_);
lean_dec_ref(v___x_2164_);
v___y_2034_ = v___y_2115_;
v___y_2035_ = v___x_2163_;
v___y_2036_ = v___y_2116_;
v___y_2037_ = v_a_2122_;
v___y_2038_ = v___y_2117_;
v___y_2039_ = v___y_2118_;
v___y_2040_ = v___y_2119_;
v___y_2041_ = v___y_2120_;
v_a_2042_ = v_a_2200_;
goto v___jp_2033_;
}
}
}
v___jp_2201_:
{
uint8_t v___x_2203_; 
v___x_2203_ = 1;
if (v___y_2202_ == 0)
{
lean_object* v___x_2204_; 
lean_inc_ref(v_binderType_1479_);
v___x_2204_ = l_Lean_Meta_isExprDefEq(v_binderType_1479_, v_binderType_1480_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2302_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2207_ = v___x_2204_;
v_isShared_2208_ = v_isSharedCheck_2302_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2204_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2302_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
uint8_t v___x_2209_; 
v___x_2209_ = lean_unbox(v_a_2205_);
lean_dec(v_a_2205_);
if (v___x_2209_ == 0)
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2213_; 
lean_dec_ref(v_binderType_1479_);
v___x_2210_ = lean_box(0);
v___x_2211_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2211_, 0, v_expr_1250_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
lean_ctor_set_uint8(v___x_2211_, sizeof(void*)*2, v___x_2203_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2211_);
v___x_2213_ = v___x_2207_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
else
{
lean_object* v_options_2215_; uint8_t v_hasTrace_2216_; 
lean_del_object(v___x_2207_);
v_options_2215_ = lean_ctor_get(v_a_1253_, 2);
v_hasTrace_2216_ = lean_ctor_get_uint8(v_options_2215_, sizeof(void*)*1);
if (v_hasTrace_2216_ == 0)
{
lean_object* v___x_2217_; 
v___x_2217_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1465_, v_a_1254_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_a_2218_; 
v_a_2218_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2218_);
lean_dec_ref(v___x_2217_);
if (lean_obj_tag(v_a_2218_) == 1)
{
lean_object* v_val_2219_; lean_object* v___x_2220_; 
v_val_2219_ = lean_ctor_get(v_a_2218_, 0);
lean_inc(v_val_2219_);
lean_dec_ref(v_a_2218_);
v___x_2220_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1463_, v_a_1254_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2221_);
lean_dec_ref(v___x_2220_);
if (lean_obj_tag(v_a_2221_) == 1)
{
lean_object* v_val_2222_; lean_object* v___x_2223_; 
v_val_2222_ = lean_ctor_get(v_a_2221_, 0);
lean_inc(v_val_2222_);
lean_dec_ref(v_a_2221_);
lean_inc(v_a_1254_);
lean_inc_ref(v_a_1253_);
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
lean_inc(v_val_2219_);
v___x_2223_ = lean_infer_type(v_val_2219_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v_a_2224_; lean_object* v___x_2225_; 
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_a_2224_);
lean_dec_ref(v___x_2223_);
lean_inc(v_a_1254_);
lean_inc_ref(v_a_1253_);
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
lean_inc(v_val_2222_);
v___x_2225_ = lean_infer_type(v_val_2222_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v_a_2226_; lean_object* v___x_2227_; 
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
lean_inc(v_a_2226_);
lean_dec_ref(v___x_2225_);
v___x_2227_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_val_2219_, v_a_2226_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v___x_2229_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2228_);
lean_dec_ref(v___x_2227_);
lean_inc_ref(v_binderType_1479_);
v___x_2229_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2228_, v_binderType_1479_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2231_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2230_);
lean_dec_ref(v___x_2229_);
lean_inc_ref(v_arg_1465_);
v___x_2231_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1465_, v_a_2230_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2231_) == 0)
{
lean_object* v_a_2232_; 
v_a_2232_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2232_);
lean_dec_ref(v___x_2231_);
if (lean_obj_tag(v_a_2232_) == 1)
{
lean_object* v_val_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v_val_2233_ = lean_ctor_get(v_a_2232_, 0);
lean_inc(v_val_2233_);
lean_dec_ref(v_a_2232_);
v___x_2234_ = lean_box(0);
lean_inc_ref(v_fn_1464_);
v___x_2235_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2235_, 0, v_fn_1464_);
lean_ctor_set(v___x_2235_, 1, v___x_2234_);
lean_ctor_set_uint8(v___x_2235_, sizeof(void*)*2, v___x_2203_);
v___x_2236_ = l_Lean_Meta_Simp_mkCongr(v___x_2235_, v_val_2233_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; lean_object* v___x_2238_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
lean_inc(v_a_2237_);
lean_dec_ref(v___x_2236_);
lean_inc_ref(v_arg_1463_);
v___x_2238_ = l_Lean_Meta_Simp_mkCongrFun(v_a_2237_, v_arg_1463_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v___y_1606_ = v_val_2222_;
v___y_1607_ = v_a_2224_;
v___y_1608_ = v___x_2203_;
v___y_1609_ = v___x_2238_;
goto v___jp_1605_;
}
else
{
v___y_1606_ = v_val_2222_;
v___y_1607_ = v_a_2224_;
v___y_1608_ = v___x_2203_;
v___y_1609_ = v___x_2236_;
goto v___jp_1605_;
}
}
else
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
lean_dec(v_a_2232_);
v___x_2239_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2240_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2239_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v___y_1606_ = v_val_2222_;
v___y_1607_ = v_a_2224_;
v___y_1608_ = v___x_2203_;
v___y_1609_ = v___x_2240_;
goto v___jp_1605_;
}
}
else
{
lean_object* v_a_2241_; 
v_a_2241_ = lean_ctor_get(v___x_2231_, 0);
lean_inc(v_a_2241_);
lean_dec_ref(v___x_2231_);
v___y_1599_ = v_val_2222_;
v___y_1600_ = v_a_2224_;
v___y_1601_ = v___x_2203_;
v_a_1602_ = v_a_2241_;
goto v___jp_1598_;
}
}
else
{
lean_object* v_a_2242_; 
v_a_2242_ = lean_ctor_get(v___x_2229_, 0);
lean_inc(v_a_2242_);
lean_dec_ref(v___x_2229_);
v___y_1599_ = v_val_2222_;
v___y_1600_ = v_a_2224_;
v___y_1601_ = v___x_2203_;
v_a_1602_ = v_a_2242_;
goto v___jp_1598_;
}
}
else
{
lean_object* v_a_2243_; 
v_a_2243_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2243_);
lean_dec_ref(v___x_2227_);
v___y_1599_ = v_val_2222_;
v___y_1600_ = v_a_2224_;
v___y_1601_ = v___x_2203_;
v_a_1602_ = v_a_2243_;
goto v___jp_1598_;
}
}
else
{
lean_object* v_a_2244_; 
lean_dec(v_a_2224_);
lean_dec(v_val_2222_);
lean_dec(v_val_2219_);
v_a_2244_ = lean_ctor_get(v___x_2225_, 0);
lean_inc(v_a_2244_);
lean_dec_ref(v___x_2225_);
v___y_1568_ = v___x_2203_;
v_a_1569_ = v_a_2244_;
goto v___jp_1567_;
}
}
else
{
lean_object* v_a_2245_; 
lean_dec(v_val_2222_);
lean_dec(v_val_2219_);
v_a_2245_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_a_2245_);
lean_dec_ref(v___x_2223_);
v___y_1568_ = v___x_2203_;
v_a_1569_ = v_a_2245_;
goto v___jp_1567_;
}
}
else
{
lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v_a_2248_; 
lean_dec(v_a_2221_);
lean_dec(v_val_2219_);
v___x_2246_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2247_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2246_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_a_2248_);
lean_dec_ref(v___x_2247_);
v___y_1568_ = v___x_2203_;
v_a_1569_ = v_a_2248_;
goto v___jp_1567_;
}
}
else
{
lean_object* v_a_2249_; 
lean_dec(v_val_2219_);
v_a_2249_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2249_);
lean_dec_ref(v___x_2220_);
v___y_1568_ = v___x_2203_;
v_a_1569_ = v_a_2249_;
goto v___jp_1567_;
}
}
else
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v_a_2252_; 
lean_dec(v_a_2218_);
v___x_2250_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2251_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_a_2252_);
lean_dec_ref(v___x_2251_);
v___y_1568_ = v___x_2203_;
v_a_1569_ = v_a_2252_;
goto v___jp_1567_;
}
}
else
{
lean_object* v_a_2253_; 
v_a_2253_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_a_2253_);
lean_dec_ref(v___x_2217_);
v___y_1568_ = v___x_2203_;
v_a_1569_ = v_a_2253_;
goto v___jp_1567_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___f_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; uint8_t v___x_2262_; 
v_inheritedTraceOptions_2254_ = lean_ctor_get(v_a_1253_, 13);
v___x_2255_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_splittingProcedure___closed__1, &l_Lean_Elab_Tactic_NormCast_splittingProcedure___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_splittingProcedure___closed__1);
lean_inc_ref_n(v_expr_1250_, 2);
v___x_2256_ = l_Lean_MessageData_ofExpr(v_expr_1250_);
v___x_2257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2255_);
lean_ctor_set(v___x_2257_, 1, v___x_2256_);
v___f_2258_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_splittingProcedure___lam__4___boxed), 8, 2);
lean_closure_set(v___f_2258_, 0, v___x_2257_);
lean_closure_set(v___f_2258_, 1, v_expr_1250_);
v___x_2259_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__2_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_));
v___x_2260_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_2261_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3);
v___x_2262_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2254_, v_options_2215_, v___x_2261_);
if (v___x_2262_ == 0)
{
lean_object* v___x_2263_; uint8_t v___x_2264_; 
v___x_2263_ = l_Lean_trace_profiler;
v___x_2264_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_2215_, v___x_2263_);
if (v___x_2264_ == 0)
{
lean_object* v___x_2265_; 
lean_dec_ref(v___f_2258_);
v___x_2265_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1465_, v_a_1254_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2266_);
lean_dec_ref(v___x_2265_);
if (lean_obj_tag(v_a_2266_) == 1)
{
lean_object* v_val_2267_; lean_object* v___x_2268_; 
v_val_2267_ = lean_ctor_get(v_a_2266_, 0);
lean_inc(v_val_2267_);
lean_dec_ref(v_a_2266_);
v___x_2268_ = l_Lean_Elab_Tactic_NormCast_isCoeOf_x3f___redArg(v_arg_1463_, v_a_1254_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_a_2269_);
lean_dec_ref(v___x_2268_);
if (lean_obj_tag(v_a_2269_) == 1)
{
lean_object* v_val_2270_; lean_object* v___x_2271_; 
v_val_2270_ = lean_ctor_get(v_a_2269_, 0);
lean_inc(v_val_2270_);
lean_dec_ref(v_a_2269_);
lean_inc(v_a_1254_);
lean_inc_ref(v_a_1253_);
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
lean_inc(v_val_2267_);
v___x_2271_ = lean_infer_type(v_val_2267_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; lean_object* v___x_2273_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2272_);
lean_dec_ref(v___x_2271_);
lean_inc(v_a_1254_);
lean_inc_ref(v_a_1253_);
lean_inc(v_a_1252_);
lean_inc_ref(v_a_1251_);
lean_inc(v_val_2270_);
v___x_2273_ = lean_infer_type(v_val_2270_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v___x_2275_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2274_);
lean_dec_ref(v___x_2273_);
v___x_2275_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_val_2267_, v_a_2274_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; lean_object* v___x_2277_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2276_);
lean_dec_ref(v___x_2275_);
lean_inc_ref(v_binderType_1479_);
v___x_2277_ = l_Lean_Elab_Tactic_NormCast_mkCoe(v_a_2276_, v_binderType_1479_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2278_; lean_object* v___x_2279_; 
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_a_2278_);
lean_dec_ref(v___x_2277_);
lean_inc_ref(v_arg_1465_);
v___x_2279_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_arg_1465_, v_a_2278_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref(v___x_2279_);
if (lean_obj_tag(v_a_2280_) == 1)
{
lean_object* v_val_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v_val_2281_ = lean_ctor_get(v_a_2280_, 0);
lean_inc(v_val_2281_);
lean_dec_ref(v_a_2280_);
v___x_2282_ = lean_box(0);
lean_inc_ref(v_fn_1464_);
v___x_2283_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2283_, 0, v_fn_1464_);
lean_ctor_set(v___x_2283_, 1, v___x_2282_);
lean_ctor_set_uint8(v___x_2283_, sizeof(void*)*2, v___x_2203_);
v___x_2284_ = l_Lean_Meta_Simp_mkCongr(v___x_2283_, v_val_2281_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v_a_2285_; lean_object* v___x_2286_; 
v_a_2285_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_a_2285_);
lean_dec_ref(v___x_2284_);
lean_inc_ref(v_arg_1463_);
v___x_2286_ = l_Lean_Meta_Simp_mkCongrFun(v_a_2285_, v_arg_1463_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v___y_1735_ = v_val_2270_;
v___y_1736_ = v_a_2272_;
v___y_1737_ = v___x_2203_;
v___y_1738_ = v___x_2286_;
goto v___jp_1734_;
}
else
{
v___y_1735_ = v_val_2270_;
v___y_1736_ = v_a_2272_;
v___y_1737_ = v___x_2203_;
v___y_1738_ = v___x_2284_;
goto v___jp_1734_;
}
}
else
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
lean_dec(v_a_2280_);
v___x_2287_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2288_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2287_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v___y_1735_ = v_val_2270_;
v___y_1736_ = v_a_2272_;
v___y_1737_ = v___x_2203_;
v___y_1738_ = v___x_2288_;
goto v___jp_1734_;
}
}
else
{
lean_object* v_a_2289_; 
v_a_2289_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2289_);
lean_dec_ref(v___x_2279_);
v___y_1728_ = v_val_2270_;
v___y_1729_ = v_a_2272_;
v___y_1730_ = v___x_2203_;
v_a_1731_ = v_a_2289_;
goto v___jp_1727_;
}
}
else
{
lean_object* v_a_2290_; 
v_a_2290_ = lean_ctor_get(v___x_2277_, 0);
lean_inc(v_a_2290_);
lean_dec_ref(v___x_2277_);
v___y_1728_ = v_val_2270_;
v___y_1729_ = v_a_2272_;
v___y_1730_ = v___x_2203_;
v_a_1731_ = v_a_2290_;
goto v___jp_1727_;
}
}
else
{
lean_object* v_a_2291_; 
v_a_2291_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2291_);
lean_dec_ref(v___x_2275_);
v___y_1728_ = v_val_2270_;
v___y_1729_ = v_a_2272_;
v___y_1730_ = v___x_2203_;
v_a_1731_ = v_a_2291_;
goto v___jp_1727_;
}
}
else
{
lean_object* v_a_2292_; 
lean_dec(v_a_2272_);
lean_dec(v_val_2270_);
lean_dec(v_val_2267_);
v_a_2292_ = lean_ctor_get(v___x_2273_, 0);
lean_inc(v_a_2292_);
lean_dec_ref(v___x_2273_);
v___y_1697_ = v___x_2203_;
v_a_1698_ = v_a_2292_;
goto v___jp_1696_;
}
}
else
{
lean_object* v_a_2293_; 
lean_dec(v_val_2270_);
lean_dec(v_val_2267_);
v_a_2293_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2293_);
lean_dec_ref(v___x_2271_);
v___y_1697_ = v___x_2203_;
v_a_1698_ = v_a_2293_;
goto v___jp_1696_;
}
}
else
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v_a_2296_; 
lean_dec(v_a_2269_);
lean_dec(v_val_2267_);
v___x_2294_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2295_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2294_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
lean_inc(v_a_2296_);
lean_dec_ref(v___x_2295_);
v___y_1697_ = v___x_2203_;
v_a_1698_ = v_a_2296_;
goto v___jp_1696_;
}
}
else
{
lean_object* v_a_2297_; 
lean_dec(v_val_2267_);
v_a_2297_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_a_2297_);
lean_dec_ref(v___x_2268_);
v___y_1697_ = v___x_2203_;
v_a_1698_ = v_a_2297_;
goto v___jp_1696_;
}
}
else
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v_a_2300_; 
lean_dec(v_a_2266_);
v___x_2298_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_2299_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_2298_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref(v___x_2299_);
v___y_1697_ = v___x_2203_;
v_a_1698_ = v_a_2300_;
goto v___jp_1696_;
}
}
else
{
lean_object* v_a_2301_; 
v_a_2301_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2301_);
lean_dec_ref(v___x_2265_);
v___y_1697_ = v___x_2203_;
v_a_1698_ = v_a_2301_;
goto v___jp_1696_;
}
}
else
{
v___y_2115_ = v___x_2259_;
v___y_2116_ = v_options_2215_;
v___y_2117_ = v___x_2260_;
v___y_2118_ = v___x_2262_;
v___y_2119_ = v___x_2203_;
v___y_2120_ = v___f_2258_;
goto v___jp_2114_;
}
}
else
{
v___y_2115_ = v___x_2259_;
v___y_2116_ = v_options_2215_;
v___y_2117_ = v___x_2260_;
v___y_2118_ = v___x_2262_;
v___y_2119_ = v___x_2203_;
v___y_2120_ = v___f_2258_;
goto v___jp_2114_;
}
}
}
}
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_dec_ref(v_binderType_1479_);
lean_dec_ref(v_expr_1250_);
v_a_2303_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2204_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2204_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
else
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
lean_dec_ref(v_binderType_1480_);
lean_dec_ref(v_binderType_1479_);
v___x_2311_ = lean_box(0);
v___x_2312_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2312_, 0, v_expr_1250_);
lean_ctor_set(v___x_2312_, 1, v___x_2311_);
lean_ctor_set_uint8(v___x_2312_, sizeof(void*)*2, v___x_2203_);
v___x_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2312_);
return v___x_2313_;
}
}
}
else
{
lean_dec_ref(v_a_1467_);
lean_dec_ref(v_body_1478_);
goto v___jp_1471_;
}
}
else
{
lean_dec(v_a_1467_);
goto v___jp_1471_;
}
v___jp_1471_:
{
lean_object* v___x_1472_; uint8_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1476_; 
v___x_1472_ = lean_box(0);
v___x_1473_ = 1;
v___x_1474_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1474_, 0, v_expr_1250_);
lean_ctor_set(v___x_1474_, 1, v___x_1472_);
lean_ctor_set_uint8(v___x_1474_, sizeof(void*)*2, v___x_1473_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 0, v___x_1474_);
v___x_1476_ = v___x_1469_;
goto v_reusejp_1475_;
}
else
{
lean_object* v_reuseFailAlloc_1477_; 
v_reuseFailAlloc_1477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1477_, 0, v___x_1474_);
v___x_1476_ = v_reuseFailAlloc_1477_;
goto v_reusejp_1475_;
}
v_reusejp_1475_:
{
return v___x_1476_;
}
}
}
}
else
{
lean_object* v_a_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2324_; 
lean_dec_ref(v_expr_1250_);
v_a_2317_ = lean_ctor_get(v___x_1466_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_1466_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2319_ = v___x_1466_;
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
else
{
lean_inc(v_a_2317_);
lean_dec(v___x_1466_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2324_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2322_; 
if (v_isShared_2320_ == 0)
{
v___x_2322_ = v___x_2319_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2323_; 
v_reuseFailAlloc_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2323_, 0, v_a_2317_);
v___x_2322_ = v_reuseFailAlloc_2323_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
return v___x_2322_;
}
}
}
}
else
{
goto v___jp_1256_;
}
}
else
{
goto v___jp_1256_;
}
v___jp_1256_:
{
lean_object* v___x_1257_; uint8_t v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1257_ = lean_box(0);
v___x_1258_ = 1;
v___x_1259_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1259_, 0, v_expr_1250_);
lean_ctor_set(v___x_1259_, 1, v___x_1257_);
lean_ctor_set_uint8(v___x_1259_, sizeof(void*)*2, v___x_1258_);
v___x_1260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1260_, 0, v___x_1259_);
return v___x_1260_;
}
v___jp_1261_:
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
v_a_1263_ = lean_ctor_get(v_a_1262_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_a_1262_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v_a_1262_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v_a_1262_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
lean_ctor_set_tag(v___x_1265_, 0);
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
v___jp_1271_:
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1280_; 
v_a_1273_ = lean_ctor_get(v_a_1272_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_a_1272_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1275_ = v_a_1272_;
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v_a_1272_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1280_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1278_; 
if (v_isShared_1276_ == 0)
{
lean_ctor_set_tag(v___x_1275_, 0);
v___x_1278_ = v___x_1275_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1273_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
v___jp_1281_:
{
lean_object* v___x_1291_; double v___x_1292_; double v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1291_ = lean_io_get_num_heartbeats();
v___x_1292_ = lean_float_of_nat(v___y_1285_);
v___x_1293_ = lean_float_of_nat(v___x_1291_);
v___x_1294_ = lean_box_float(v___x_1292_);
v___x_1295_ = lean_box_float(v___x_1293_);
v___x_1296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1294_);
lean_ctor_set(v___x_1296_, 1, v___x_1295_);
v___x_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1297_, 0, v_a_1290_);
lean_ctor_set(v___x_1297_, 1, v___x_1296_);
lean_inc_ref(v___y_1286_);
lean_inc(v___y_1282_);
v___x_1298_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___y_1282_, v___y_1289_, v___y_1286_, v___y_1284_, v___y_1287_, v___y_1283_, v___y_1288_, v___x_1297_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
return v___x_1298_;
}
v___jp_1299_:
{
lean_object* v___x_1309_; 
v___x_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1309_, 0, v_a_1308_);
v___y_1282_ = v___y_1300_;
v___y_1283_ = v___y_1303_;
v___y_1284_ = v___y_1302_;
v___y_1285_ = v___y_1301_;
v___y_1286_ = v___y_1304_;
v___y_1287_ = v___y_1305_;
v___y_1288_ = v___y_1307_;
v___y_1289_ = v___y_1306_;
v_a_1290_ = v___x_1309_;
goto v___jp_1281_;
}
v___jp_1310_:
{
lean_object* v_a_1320_; 
v_a_1320_ = lean_ctor_get(v_a_1319_, 0);
lean_inc(v_a_1320_);
lean_dec_ref(v_a_1319_);
v___y_1300_ = v___y_1311_;
v___y_1301_ = v___y_1314_;
v___y_1302_ = v___y_1313_;
v___y_1303_ = v___y_1312_;
v___y_1304_ = v___y_1315_;
v___y_1305_ = v___y_1316_;
v___y_1306_ = v___y_1318_;
v___y_1307_ = v___y_1317_;
v_a_1308_ = v_a_1320_;
goto v___jp_1299_;
}
v___jp_1321_:
{
lean_object* v___x_1331_; 
v___x_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1331_, 0, v_a_1330_);
v___y_1282_ = v___y_1322_;
v___y_1283_ = v___y_1325_;
v___y_1284_ = v___y_1324_;
v___y_1285_ = v___y_1323_;
v___y_1286_ = v___y_1326_;
v___y_1287_ = v___y_1327_;
v___y_1288_ = v___y_1329_;
v___y_1289_ = v___y_1328_;
v_a_1290_ = v___x_1331_;
goto v___jp_1281_;
}
v___jp_1332_:
{
if (v___y_1342_ == 0)
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
lean_dec_ref(v___y_1337_);
v___x_1343_ = lean_box(0);
v___x_1344_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1344_, 0, v_expr_1250_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
lean_ctor_set_uint8(v___x_1344_, sizeof(void*)*2, v___y_1341_);
v___y_1300_ = v___y_1333_;
v___y_1301_ = v___y_1336_;
v___y_1302_ = v___y_1335_;
v___y_1303_ = v___y_1334_;
v___y_1304_ = v___y_1338_;
v___y_1305_ = v___y_1339_;
v___y_1306_ = v___y_1341_;
v___y_1307_ = v___y_1340_;
v_a_1308_ = v___x_1344_;
goto v___jp_1299_;
}
else
{
lean_dec_ref(v_expr_1250_);
v___y_1322_ = v___y_1333_;
v___y_1323_ = v___y_1336_;
v___y_1324_ = v___y_1335_;
v___y_1325_ = v___y_1334_;
v___y_1326_ = v___y_1338_;
v___y_1327_ = v___y_1339_;
v___y_1328_ = v___y_1341_;
v___y_1329_ = v___y_1340_;
v_a_1330_ = v___y_1337_;
goto v___jp_1321_;
}
}
v___jp_1345_:
{
uint8_t v___x_1355_; 
v___x_1355_ = l_Lean_Exception_isInterrupt(v_a_1354_);
if (v___x_1355_ == 0)
{
uint8_t v___x_1356_; 
lean_inc_ref(v_a_1354_);
v___x_1356_ = l_Lean_Exception_isRuntime(v_a_1354_);
v___y_1333_ = v___y_1346_;
v___y_1334_ = v___y_1349_;
v___y_1335_ = v___y_1348_;
v___y_1336_ = v___y_1347_;
v___y_1337_ = v_a_1354_;
v___y_1338_ = v___y_1350_;
v___y_1339_ = v___y_1351_;
v___y_1340_ = v___y_1353_;
v___y_1341_ = v___y_1352_;
v___y_1342_ = v___x_1356_;
goto v___jp_1332_;
}
else
{
v___y_1333_ = v___y_1346_;
v___y_1334_ = v___y_1349_;
v___y_1335_ = v___y_1348_;
v___y_1336_ = v___y_1347_;
v___y_1337_ = v_a_1354_;
v___y_1338_ = v___y_1350_;
v___y_1339_ = v___y_1351_;
v___y_1340_ = v___y_1353_;
v___y_1341_ = v___y_1352_;
v___y_1342_ = v___x_1355_;
goto v___jp_1332_;
}
}
v___jp_1357_:
{
lean_object* v___x_1367_; double v___x_1368_; double v___x_1369_; double v___x_1370_; double v___x_1371_; double v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1367_ = lean_io_mono_nanos_now();
v___x_1368_ = lean_float_of_nat(v___y_1358_);
v___x_1369_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4);
v___x_1370_ = lean_float_div(v___x_1368_, v___x_1369_);
v___x_1371_ = lean_float_of_nat(v___x_1367_);
v___x_1372_ = lean_float_div(v___x_1371_, v___x_1369_);
v___x_1373_ = lean_box_float(v___x_1370_);
v___x_1374_ = lean_box_float(v___x_1372_);
v___x_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1373_);
lean_ctor_set(v___x_1375_, 1, v___x_1374_);
v___x_1376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1376_, 0, v_a_1366_);
lean_ctor_set(v___x_1376_, 1, v___x_1375_);
lean_inc_ref(v___y_1362_);
lean_inc(v___y_1359_);
v___x_1377_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___y_1359_, v___y_1365_, v___y_1362_, v___y_1361_, v___y_1363_, v___y_1360_, v___y_1364_, v___x_1376_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
return v___x_1377_;
}
v___jp_1378_:
{
lean_object* v___x_1388_; 
v___x_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1388_, 0, v_a_1387_);
v___y_1358_ = v___y_1379_;
v___y_1359_ = v___y_1380_;
v___y_1360_ = v___y_1382_;
v___y_1361_ = v___y_1381_;
v___y_1362_ = v___y_1383_;
v___y_1363_ = v___y_1384_;
v___y_1364_ = v___y_1386_;
v___y_1365_ = v___y_1385_;
v_a_1366_ = v___x_1388_;
goto v___jp_1357_;
}
v___jp_1389_:
{
lean_object* v_a_1399_; 
v_a_1399_ = lean_ctor_get(v_a_1398_, 0);
lean_inc(v_a_1399_);
lean_dec_ref(v_a_1398_);
v___y_1379_ = v___y_1390_;
v___y_1380_ = v___y_1391_;
v___y_1381_ = v___y_1393_;
v___y_1382_ = v___y_1392_;
v___y_1383_ = v___y_1394_;
v___y_1384_ = v___y_1395_;
v___y_1385_ = v___y_1397_;
v___y_1386_ = v___y_1396_;
v_a_1387_ = v_a_1399_;
goto v___jp_1378_;
}
v___jp_1400_:
{
lean_object* v___x_1410_; 
v___x_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1410_, 0, v_a_1409_);
v___y_1358_ = v___y_1401_;
v___y_1359_ = v___y_1402_;
v___y_1360_ = v___y_1404_;
v___y_1361_ = v___y_1403_;
v___y_1362_ = v___y_1405_;
v___y_1363_ = v___y_1406_;
v___y_1364_ = v___y_1408_;
v___y_1365_ = v___y_1407_;
v_a_1366_ = v___x_1410_;
goto v___jp_1357_;
}
v___jp_1411_:
{
if (v___y_1421_ == 0)
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
lean_dec_ref(v___y_1414_);
v___x_1422_ = lean_box(0);
v___x_1423_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1423_, 0, v_expr_1250_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
lean_ctor_set_uint8(v___x_1423_, sizeof(void*)*2, v___y_1420_);
v___y_1379_ = v___y_1412_;
v___y_1380_ = v___y_1413_;
v___y_1381_ = v___y_1416_;
v___y_1382_ = v___y_1415_;
v___y_1383_ = v___y_1417_;
v___y_1384_ = v___y_1418_;
v___y_1385_ = v___y_1420_;
v___y_1386_ = v___y_1419_;
v_a_1387_ = v___x_1423_;
goto v___jp_1378_;
}
else
{
lean_dec_ref(v_expr_1250_);
v___y_1401_ = v___y_1412_;
v___y_1402_ = v___y_1413_;
v___y_1403_ = v___y_1416_;
v___y_1404_ = v___y_1415_;
v___y_1405_ = v___y_1417_;
v___y_1406_ = v___y_1418_;
v___y_1407_ = v___y_1420_;
v___y_1408_ = v___y_1419_;
v_a_1409_ = v___y_1414_;
goto v___jp_1400_;
}
}
v___jp_1424_:
{
uint8_t v___x_1434_; 
v___x_1434_ = l_Lean_Exception_isInterrupt(v_a_1433_);
if (v___x_1434_ == 0)
{
uint8_t v___x_1435_; 
lean_inc_ref(v_a_1433_);
v___x_1435_ = l_Lean_Exception_isRuntime(v_a_1433_);
v___y_1412_ = v___y_1425_;
v___y_1413_ = v___y_1426_;
v___y_1414_ = v_a_1433_;
v___y_1415_ = v___y_1428_;
v___y_1416_ = v___y_1427_;
v___y_1417_ = v___y_1429_;
v___y_1418_ = v___y_1430_;
v___y_1419_ = v___y_1432_;
v___y_1420_ = v___y_1431_;
v___y_1421_ = v___x_1435_;
goto v___jp_1411_;
}
else
{
v___y_1412_ = v___y_1425_;
v___y_1413_ = v___y_1426_;
v___y_1414_ = v_a_1433_;
v___y_1415_ = v___y_1428_;
v___y_1416_ = v___y_1427_;
v___y_1417_ = v___y_1429_;
v___y_1418_ = v___y_1430_;
v___y_1419_ = v___y_1432_;
v___y_1420_ = v___y_1431_;
v___y_1421_ = v___x_1434_;
goto v___jp_1411_;
}
}
v___jp_1436_:
{
if (v___y_1439_ == 0)
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
lean_dec_ref(v___y_1437_);
v___x_1440_ = lean_box(0);
v___x_1441_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1441_, 0, v_expr_1250_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
lean_ctor_set_uint8(v___x_1441_, sizeof(void*)*2, v___y_1438_);
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
return v___x_1442_;
}
else
{
lean_object* v___x_1443_; 
lean_dec_ref(v_expr_1250_);
v___x_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___y_1437_);
return v___x_1443_;
}
}
v___jp_1444_:
{
uint8_t v___x_1447_; 
v___x_1447_ = l_Lean_Exception_isInterrupt(v_a_1446_);
if (v___x_1447_ == 0)
{
uint8_t v___x_1448_; 
lean_inc_ref(v_a_1446_);
v___x_1448_ = l_Lean_Exception_isRuntime(v_a_1446_);
v___y_1437_ = v_a_1446_;
v___y_1438_ = v___y_1445_;
v___y_1439_ = v___x_1448_;
goto v___jp_1436_;
}
else
{
v___y_1437_ = v_a_1446_;
v___y_1438_ = v___y_1445_;
v___y_1439_ = v___x_1447_;
goto v___jp_1436_;
}
}
v___jp_1449_:
{
if (v___y_1452_ == 0)
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
lean_dec_ref(v___y_1450_);
v___x_1453_ = lean_box(0);
v___x_1454_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_1454_, 0, v_expr_1250_);
lean_ctor_set(v___x_1454_, 1, v___x_1453_);
lean_ctor_set_uint8(v___x_1454_, sizeof(void*)*2, v___y_1451_);
v___x_1455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1454_);
return v___x_1455_;
}
else
{
lean_object* v___x_1456_; 
lean_dec_ref(v_expr_1250_);
v___x_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1456_, 0, v___y_1450_);
return v___x_1456_;
}
}
v___jp_1457_:
{
uint8_t v___x_1460_; 
v___x_1460_ = l_Lean_Exception_isInterrupt(v_a_1459_);
if (v___x_1460_ == 0)
{
uint8_t v___x_1461_; 
lean_inc_ref(v_a_1459_);
v___x_1461_ = l_Lean_Exception_isRuntime(v_a_1459_);
v___y_1450_ = v_a_1459_;
v___y_1451_ = v___y_1458_;
v___y_1452_ = v___x_1461_;
goto v___jp_1449_;
}
else
{
v___y_1450_ = v_a_1459_;
v___y_1451_ = v___y_1458_;
v___y_1452_ = v___x_1460_;
goto v___jp_1449_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_splittingProcedure___boxed(lean_object* v_expr_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure(v_expr_2325_, v_a_2326_, v_a_2327_, v_a_2328_, v_a_2329_);
lean_dec(v_a_2329_);
lean_dec_ref(v_a_2328_);
lean_dec(v_a_2327_);
lean_dec_ref(v_a_2326_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___redArg(lean_object* v___y_2332_){
_start:
{
lean_object* v___x_2334_; lean_object* v_traceState_2335_; lean_object* v_traces_2336_; lean_object* v___x_2337_; lean_object* v_traceState_2338_; lean_object* v_env_2339_; lean_object* v_nextMacroScope_2340_; lean_object* v_ngen_2341_; lean_object* v_auxDeclNGen_2342_; lean_object* v_cache_2343_; lean_object* v_messages_2344_; lean_object* v_infoState_2345_; lean_object* v_snapshotTasks_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2367_; 
v___x_2334_ = lean_st_ref_get(v___y_2332_);
v_traceState_2335_ = lean_ctor_get(v___x_2334_, 4);
lean_inc_ref(v_traceState_2335_);
lean_dec(v___x_2334_);
v_traces_2336_ = lean_ctor_get(v_traceState_2335_, 0);
lean_inc_ref(v_traces_2336_);
lean_dec_ref(v_traceState_2335_);
v___x_2337_ = lean_st_ref_take(v___y_2332_);
v_traceState_2338_ = lean_ctor_get(v___x_2337_, 4);
v_env_2339_ = lean_ctor_get(v___x_2337_, 0);
v_nextMacroScope_2340_ = lean_ctor_get(v___x_2337_, 1);
v_ngen_2341_ = lean_ctor_get(v___x_2337_, 2);
v_auxDeclNGen_2342_ = lean_ctor_get(v___x_2337_, 3);
v_cache_2343_ = lean_ctor_get(v___x_2337_, 5);
v_messages_2344_ = lean_ctor_get(v___x_2337_, 6);
v_infoState_2345_ = lean_ctor_get(v___x_2337_, 7);
v_snapshotTasks_2346_ = lean_ctor_get(v___x_2337_, 8);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2348_ = v___x_2337_;
v_isShared_2349_ = v_isSharedCheck_2367_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_snapshotTasks_2346_);
lean_inc(v_infoState_2345_);
lean_inc(v_messages_2344_);
lean_inc(v_cache_2343_);
lean_inc(v_traceState_2338_);
lean_inc(v_auxDeclNGen_2342_);
lean_inc(v_ngen_2341_);
lean_inc(v_nextMacroScope_2340_);
lean_inc(v_env_2339_);
lean_dec(v___x_2337_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2367_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
uint64_t v_tid_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2365_; 
v_tid_2350_ = lean_ctor_get_uint64(v_traceState_2338_, sizeof(void*)*1);
v_isSharedCheck_2365_ = !lean_is_exclusive(v_traceState_2338_);
if (v_isSharedCheck_2365_ == 0)
{
lean_object* v_unused_2366_; 
v_unused_2366_ = lean_ctor_get(v_traceState_2338_, 0);
lean_dec(v_unused_2366_);
v___x_2352_ = v_traceState_2338_;
v_isShared_2353_ = v_isSharedCheck_2365_;
goto v_resetjp_2351_;
}
else
{
lean_dec(v_traceState_2338_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2365_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2358_; 
v___x_2354_ = lean_unsigned_to_nat(32u);
v___x_2355_ = lean_mk_empty_array_with_capacity(v___x_2354_);
lean_dec_ref(v___x_2355_);
v___x_2356_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg___closed__1);
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 0, v___x_2356_);
v___x_2358_ = v___x_2352_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2356_);
lean_ctor_set_uint64(v_reuseFailAlloc_2364_, sizeof(void*)*1, v_tid_2350_);
v___x_2358_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
lean_object* v___x_2360_; 
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 4, v___x_2358_);
v___x_2360_ = v___x_2348_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_env_2339_);
lean_ctor_set(v_reuseFailAlloc_2363_, 1, v_nextMacroScope_2340_);
lean_ctor_set(v_reuseFailAlloc_2363_, 2, v_ngen_2341_);
lean_ctor_set(v_reuseFailAlloc_2363_, 3, v_auxDeclNGen_2342_);
lean_ctor_set(v_reuseFailAlloc_2363_, 4, v___x_2358_);
lean_ctor_set(v_reuseFailAlloc_2363_, 5, v_cache_2343_);
lean_ctor_set(v_reuseFailAlloc_2363_, 6, v_messages_2344_);
lean_ctor_set(v_reuseFailAlloc_2363_, 7, v_infoState_2345_);
lean_ctor_set(v_reuseFailAlloc_2363_, 8, v_snapshotTasks_2346_);
v___x_2360_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2361_ = lean_st_ref_set(v___y_2332_, v___x_2360_);
v___x_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2362_, 0, v_traces_2336_);
return v___x_2362_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___redArg___boxed(lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___redArg(v___y_2368_);
lean_dec(v___y_2368_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__0(lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_){
_start:
{
lean_object* v___x_2379_; 
v___x_2379_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___redArg(v___y_2377_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___boxed(lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__0(v___y_2380_, v___y_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
return v_res_2388_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2390_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__0));
v___x_2391_ = l_Lean_stringToMessageData(v___x_2390_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lam__0(lean_object* v_e_2392_, lean_object* v_x_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2402_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__1, &l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_prove___lam__0___closed__1);
v___x_2403_ = l_Lean_MessageData_ofExpr(v_e_2392_);
v___x_2404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2402_);
lean_ctor_set(v___x_2404_, 1, v___x_2403_);
v___x_2405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2404_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___lam__0___boxed(lean_object* v_e_2406_, lean_object* v_x_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l_Lean_Elab_Tactic_NormCast_prove___lam__0(v_e_2406_, v_x_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v_x_2407_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__2___redArg(lean_object* v_oldTraces_2417_, lean_object* v_data_2418_, lean_object* v_ref_2419_, lean_object* v_msg_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v_fileName_2426_; lean_object* v_fileMap_2427_; lean_object* v_options_2428_; lean_object* v_currRecDepth_2429_; lean_object* v_maxRecDepth_2430_; lean_object* v_ref_2431_; lean_object* v_currNamespace_2432_; lean_object* v_openDecls_2433_; lean_object* v_initHeartbeats_2434_; lean_object* v_maxHeartbeats_2435_; lean_object* v_quotContext_2436_; lean_object* v_currMacroScope_2437_; uint8_t v_diag_2438_; lean_object* v_cancelTk_x3f_2439_; uint8_t v_suppressElabErrors_2440_; lean_object* v_inheritedTraceOptions_2441_; lean_object* v___x_2442_; lean_object* v_traceState_2443_; lean_object* v_traces_2444_; lean_object* v_ref_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; size_t v_sz_2448_; size_t v___x_2449_; lean_object* v___x_2450_; lean_object* v_msg_2451_; lean_object* v___x_2452_; lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2490_; 
v_fileName_2426_ = lean_ctor_get(v___y_2423_, 0);
v_fileMap_2427_ = lean_ctor_get(v___y_2423_, 1);
v_options_2428_ = lean_ctor_get(v___y_2423_, 2);
v_currRecDepth_2429_ = lean_ctor_get(v___y_2423_, 3);
v_maxRecDepth_2430_ = lean_ctor_get(v___y_2423_, 4);
v_ref_2431_ = lean_ctor_get(v___y_2423_, 5);
v_currNamespace_2432_ = lean_ctor_get(v___y_2423_, 6);
v_openDecls_2433_ = lean_ctor_get(v___y_2423_, 7);
v_initHeartbeats_2434_ = lean_ctor_get(v___y_2423_, 8);
v_maxHeartbeats_2435_ = lean_ctor_get(v___y_2423_, 9);
v_quotContext_2436_ = lean_ctor_get(v___y_2423_, 10);
v_currMacroScope_2437_ = lean_ctor_get(v___y_2423_, 11);
v_diag_2438_ = lean_ctor_get_uint8(v___y_2423_, sizeof(void*)*14);
v_cancelTk_x3f_2439_ = lean_ctor_get(v___y_2423_, 12);
v_suppressElabErrors_2440_ = lean_ctor_get_uint8(v___y_2423_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2441_ = lean_ctor_get(v___y_2423_, 13);
v___x_2442_ = lean_st_ref_get(v___y_2424_);
v_traceState_2443_ = lean_ctor_get(v___x_2442_, 4);
lean_inc_ref(v_traceState_2443_);
lean_dec(v___x_2442_);
v_traces_2444_ = lean_ctor_get(v_traceState_2443_, 0);
lean_inc_ref(v_traces_2444_);
lean_dec_ref(v_traceState_2443_);
v_ref_2445_ = l_Lean_replaceRef(v_ref_2419_, v_ref_2431_);
lean_inc_ref(v_inheritedTraceOptions_2441_);
lean_inc(v_cancelTk_x3f_2439_);
lean_inc(v_currMacroScope_2437_);
lean_inc(v_quotContext_2436_);
lean_inc(v_maxHeartbeats_2435_);
lean_inc(v_initHeartbeats_2434_);
lean_inc(v_openDecls_2433_);
lean_inc(v_currNamespace_2432_);
lean_inc(v_maxRecDepth_2430_);
lean_inc(v_currRecDepth_2429_);
lean_inc_ref(v_options_2428_);
lean_inc_ref(v_fileMap_2427_);
lean_inc_ref(v_fileName_2426_);
v___x_2446_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2446_, 0, v_fileName_2426_);
lean_ctor_set(v___x_2446_, 1, v_fileMap_2427_);
lean_ctor_set(v___x_2446_, 2, v_options_2428_);
lean_ctor_set(v___x_2446_, 3, v_currRecDepth_2429_);
lean_ctor_set(v___x_2446_, 4, v_maxRecDepth_2430_);
lean_ctor_set(v___x_2446_, 5, v_ref_2445_);
lean_ctor_set(v___x_2446_, 6, v_currNamespace_2432_);
lean_ctor_set(v___x_2446_, 7, v_openDecls_2433_);
lean_ctor_set(v___x_2446_, 8, v_initHeartbeats_2434_);
lean_ctor_set(v___x_2446_, 9, v_maxHeartbeats_2435_);
lean_ctor_set(v___x_2446_, 10, v_quotContext_2436_);
lean_ctor_set(v___x_2446_, 11, v_currMacroScope_2437_);
lean_ctor_set(v___x_2446_, 12, v_cancelTk_x3f_2439_);
lean_ctor_set(v___x_2446_, 13, v_inheritedTraceOptions_2441_);
lean_ctor_set_uint8(v___x_2446_, sizeof(void*)*14, v_diag_2438_);
lean_ctor_set_uint8(v___x_2446_, sizeof(void*)*14 + 1, v_suppressElabErrors_2440_);
v___x_2447_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2444_);
lean_dec_ref(v_traces_2444_);
v_sz_2448_ = lean_array_size(v___x_2447_);
v___x_2449_ = ((size_t)0ULL);
v___x_2450_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__4(v_sz_2448_, v___x_2449_, v___x_2447_);
v_msg_2451_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2451_, 0, v_data_2418_);
lean_ctor_set(v_msg_2451_, 1, v_msg_2420_);
lean_ctor_set(v_msg_2451_, 2, v___x_2450_);
v___x_2452_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__5(v_msg_2451_, v___y_2421_, v___y_2422_, v___x_2446_, v___y_2424_);
lean_dec_ref(v___x_2446_);
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2455_ = v___x_2452_;
v_isShared_2456_ = v_isSharedCheck_2490_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2452_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2490_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2457_; lean_object* v_traceState_2458_; lean_object* v_env_2459_; lean_object* v_nextMacroScope_2460_; lean_object* v_ngen_2461_; lean_object* v_auxDeclNGen_2462_; lean_object* v_cache_2463_; lean_object* v_messages_2464_; lean_object* v_infoState_2465_; lean_object* v_snapshotTasks_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2489_; 
v___x_2457_ = lean_st_ref_take(v___y_2424_);
v_traceState_2458_ = lean_ctor_get(v___x_2457_, 4);
v_env_2459_ = lean_ctor_get(v___x_2457_, 0);
v_nextMacroScope_2460_ = lean_ctor_get(v___x_2457_, 1);
v_ngen_2461_ = lean_ctor_get(v___x_2457_, 2);
v_auxDeclNGen_2462_ = lean_ctor_get(v___x_2457_, 3);
v_cache_2463_ = lean_ctor_get(v___x_2457_, 5);
v_messages_2464_ = lean_ctor_get(v___x_2457_, 6);
v_infoState_2465_ = lean_ctor_get(v___x_2457_, 7);
v_snapshotTasks_2466_ = lean_ctor_get(v___x_2457_, 8);
v_isSharedCheck_2489_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2489_ == 0)
{
v___x_2468_ = v___x_2457_;
v_isShared_2469_ = v_isSharedCheck_2489_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_snapshotTasks_2466_);
lean_inc(v_infoState_2465_);
lean_inc(v_messages_2464_);
lean_inc(v_cache_2463_);
lean_inc(v_traceState_2458_);
lean_inc(v_auxDeclNGen_2462_);
lean_inc(v_ngen_2461_);
lean_inc(v_nextMacroScope_2460_);
lean_inc(v_env_2459_);
lean_dec(v___x_2457_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2489_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
uint64_t v_tid_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2487_; 
v_tid_2470_ = lean_ctor_get_uint64(v_traceState_2458_, sizeof(void*)*1);
v_isSharedCheck_2487_ = !lean_is_exclusive(v_traceState_2458_);
if (v_isSharedCheck_2487_ == 0)
{
lean_object* v_unused_2488_; 
v_unused_2488_ = lean_ctor_get(v_traceState_2458_, 0);
lean_dec(v_unused_2488_);
v___x_2472_ = v_traceState_2458_;
v_isShared_2473_ = v_isSharedCheck_2487_;
goto v_resetjp_2471_;
}
else
{
lean_dec(v_traceState_2458_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2487_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2477_; 
v___x_2474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2474_, 0, v_ref_2419_);
lean_ctor_set(v___x_2474_, 1, v_a_2453_);
v___x_2475_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2417_, v___x_2474_);
if (v_isShared_2473_ == 0)
{
lean_ctor_set(v___x_2472_, 0, v___x_2475_);
v___x_2477_ = v___x_2472_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v___x_2475_);
lean_ctor_set_uint64(v_reuseFailAlloc_2486_, sizeof(void*)*1, v_tid_2470_);
v___x_2477_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
lean_object* v___x_2479_; 
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 4, v___x_2477_);
v___x_2479_ = v___x_2468_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_env_2459_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v_nextMacroScope_2460_);
lean_ctor_set(v_reuseFailAlloc_2485_, 2, v_ngen_2461_);
lean_ctor_set(v_reuseFailAlloc_2485_, 3, v_auxDeclNGen_2462_);
lean_ctor_set(v_reuseFailAlloc_2485_, 4, v___x_2477_);
lean_ctor_set(v_reuseFailAlloc_2485_, 5, v_cache_2463_);
lean_ctor_set(v_reuseFailAlloc_2485_, 6, v_messages_2464_);
lean_ctor_set(v_reuseFailAlloc_2485_, 7, v_infoState_2465_);
lean_ctor_set(v_reuseFailAlloc_2485_, 8, v_snapshotTasks_2466_);
v___x_2479_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2483_; 
v___x_2480_ = lean_st_ref_set(v___y_2424_, v___x_2479_);
v___x_2481_ = lean_box(0);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 0, v___x_2481_);
v___x_2483_ = v___x_2455_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2481_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__2___redArg___boxed(lean_object* v_oldTraces_2491_, lean_object* v_data_2492_, lean_object* v_ref_2493_, lean_object* v_msg_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__2___redArg(v_oldTraces_2491_, v_data_2492_, v_ref_2493_, v_msg_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
return v_res_2500_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__1(lean_object* v_e_2501_){
_start:
{
if (lean_obj_tag(v_e_2501_) == 0)
{
uint8_t v___x_2502_; 
v___x_2502_ = 2;
return v___x_2502_;
}
else
{
lean_object* v_a_2503_; 
v_a_2503_ = lean_ctor_get(v_e_2501_, 0);
if (lean_obj_tag(v_a_2503_) == 0)
{
uint8_t v___x_2504_; 
v___x_2504_ = 1;
return v___x_2504_;
}
else
{
uint8_t v___x_2505_; 
v___x_2505_ = 0;
return v___x_2505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__1___boxed(lean_object* v_e_2506_){
_start:
{
uint8_t v_res_2507_; lean_object* v_r_2508_; 
v_res_2507_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__1(v_e_2506_);
lean_dec_ref(v_e_2506_);
v_r_2508_ = lean_box(v_res_2507_);
return v_r_2508_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__3___redArg(lean_object* v_x_2509_){
_start:
{
if (lean_obj_tag(v_x_2509_) == 0)
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2518_; 
v_a_2511_ = lean_ctor_get(v_x_2509_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v_x_2509_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2513_ = v_x_2509_;
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v_x_2509_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2516_; 
if (v_isShared_2514_ == 0)
{
lean_ctor_set_tag(v___x_2513_, 1);
v___x_2516_ = v___x_2513_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_a_2511_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
else
{
lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2526_; 
v_a_2519_ = lean_ctor_get(v_x_2509_, 0);
v_isSharedCheck_2526_ = !lean_is_exclusive(v_x_2509_);
if (v_isSharedCheck_2526_ == 0)
{
v___x_2521_ = v_x_2509_;
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v_x_2509_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2526_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2524_; 
if (v_isShared_2522_ == 0)
{
lean_ctor_set_tag(v___x_2521_, 0);
v___x_2524_ = v___x_2521_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2525_; 
v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2519_);
v___x_2524_ = v_reuseFailAlloc_2525_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
return v___x_2524_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__3___redArg___boxed(lean_object* v_x_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__3___redArg(v_x_2527_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1(lean_object* v_cls_2530_, uint8_t v_collapsed_2531_, lean_object* v_tag_2532_, lean_object* v_opts_2533_, uint8_t v_clsEnabled_2534_, lean_object* v_oldTraces_2535_, lean_object* v_msg_2536_, lean_object* v_resStartStop_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_){
_start:
{
lean_object* v_fst_2546_; lean_object* v_snd_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2645_; 
v_fst_2546_ = lean_ctor_get(v_resStartStop_2537_, 0);
v_snd_2547_ = lean_ctor_get(v_resStartStop_2537_, 1);
v_isSharedCheck_2645_ = !lean_is_exclusive(v_resStartStop_2537_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2549_ = v_resStartStop_2537_;
v_isShared_2550_ = v_isSharedCheck_2645_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_snd_2547_);
lean_inc(v_fst_2546_);
lean_dec(v_resStartStop_2537_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2645_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v_data_2554_; lean_object* v_fst_2565_; lean_object* v_snd_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2644_; 
v_fst_2565_ = lean_ctor_get(v_snd_2547_, 0);
v_snd_2566_ = lean_ctor_get(v_snd_2547_, 1);
v_isSharedCheck_2644_ = !lean_is_exclusive(v_snd_2547_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2568_ = v_snd_2547_;
v_isShared_2569_ = v_isSharedCheck_2644_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_snd_2566_);
lean_inc(v_fst_2565_);
lean_dec(v_snd_2547_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2644_;
goto v_resetjp_2567_;
}
v___jp_2551_:
{
lean_object* v___x_2555_; 
lean_inc(v___y_2552_);
v___x_2555_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__2___redArg(v_oldTraces_2535_, v_data_2554_, v___y_2552_, v___y_2553_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v___x_2556_; 
lean_dec_ref(v___x_2555_);
v___x_2556_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__3___redArg(v_fst_2546_);
return v___x_2556_;
}
else
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
lean_dec(v_fst_2546_);
v_a_2557_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2559_ = v___x_2555_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2555_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
v_resetjp_2567_:
{
lean_object* v___x_2570_; uint8_t v___x_2571_; lean_object* v___y_2573_; lean_object* v_a_2574_; uint8_t v___y_2598_; double v___y_2629_; 
v___x_2570_ = l_Lean_trace_profiler;
v___x_2571_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_opts_2533_, v___x_2570_);
if (v___x_2571_ == 0)
{
v___y_2598_ = v___x_2571_;
goto v___jp_2597_;
}
else
{
lean_object* v___x_2634_; uint8_t v___x_2635_; 
v___x_2634_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2635_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_opts_2533_, v___x_2634_);
if (v___x_2635_ == 0)
{
lean_object* v___x_2636_; lean_object* v___x_2637_; double v___x_2638_; double v___x_2639_; double v___x_2640_; 
v___x_2636_ = l_Lean_trace_profiler_threshold;
v___x_2637_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__5(v_opts_2533_, v___x_2636_);
v___x_2638_ = lean_float_of_nat(v___x_2637_);
v___x_2639_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__5, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__5_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__5);
v___x_2640_ = lean_float_div(v___x_2638_, v___x_2639_);
v___y_2629_ = v___x_2640_;
goto v___jp_2628_;
}
else
{
lean_object* v___x_2641_; lean_object* v___x_2642_; double v___x_2643_; 
v___x_2641_ = l_Lean_trace_profiler_threshold;
v___x_2642_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__5(v_opts_2533_, v___x_2641_);
v___x_2643_ = lean_float_of_nat(v___x_2642_);
v___y_2629_ = v___x_2643_;
goto v___jp_2628_;
}
}
v___jp_2572_:
{
uint8_t v_result_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2580_; 
v_result_2575_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__1(v_fst_2546_);
v___x_2576_ = l_Lean_TraceResult_toEmoji(v_result_2575_);
v___x_2577_ = l_Lean_stringToMessageData(v___x_2576_);
v___x_2578_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1);
if (v_isShared_2569_ == 0)
{
lean_ctor_set_tag(v___x_2568_, 7);
lean_ctor_set(v___x_2568_, 1, v___x_2578_);
lean_ctor_set(v___x_2568_, 0, v___x_2577_);
v___x_2580_ = v___x_2568_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v___x_2577_);
lean_ctor_set(v_reuseFailAlloc_2591_, 1, v___x_2578_);
v___x_2580_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
lean_object* v_m_2582_; 
if (v_isShared_2550_ == 0)
{
lean_ctor_set_tag(v___x_2549_, 7);
lean_ctor_set(v___x_2549_, 1, v_a_2574_);
lean_ctor_set(v___x_2549_, 0, v___x_2580_);
v_m_2582_ = v___x_2549_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2580_);
lean_ctor_set(v_reuseFailAlloc_2590_, 1, v_a_2574_);
v_m_2582_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; double v___x_2585_; lean_object* v_data_2586_; 
v___x_2583_ = lean_box(v_result_2575_);
v___x_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2584_, 0, v___x_2583_);
v___x_2585_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2);
lean_inc_ref(v_tag_2532_);
lean_inc_ref(v___x_2584_);
lean_inc(v_cls_2530_);
v_data_2586_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2586_, 0, v_cls_2530_);
lean_ctor_set(v_data_2586_, 1, v___x_2584_);
lean_ctor_set(v_data_2586_, 2, v_tag_2532_);
lean_ctor_set_float(v_data_2586_, sizeof(void*)*3, v___x_2585_);
lean_ctor_set_float(v_data_2586_, sizeof(void*)*3 + 8, v___x_2585_);
lean_ctor_set_uint8(v_data_2586_, sizeof(void*)*3 + 16, v_collapsed_2531_);
if (v___x_2571_ == 0)
{
lean_dec_ref(v___x_2584_);
lean_dec(v_snd_2566_);
lean_dec(v_fst_2565_);
lean_dec_ref(v_tag_2532_);
lean_dec(v_cls_2530_);
v___y_2552_ = v___y_2573_;
v___y_2553_ = v_m_2582_;
v_data_2554_ = v_data_2586_;
goto v___jp_2551_;
}
else
{
lean_object* v_data_2587_; double v___x_2588_; double v___x_2589_; 
lean_dec_ref(v_data_2586_);
v_data_2587_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2587_, 0, v_cls_2530_);
lean_ctor_set(v_data_2587_, 1, v___x_2584_);
lean_ctor_set(v_data_2587_, 2, v_tag_2532_);
v___x_2588_ = lean_unbox_float(v_fst_2565_);
lean_dec(v_fst_2565_);
lean_ctor_set_float(v_data_2587_, sizeof(void*)*3, v___x_2588_);
v___x_2589_ = lean_unbox_float(v_snd_2566_);
lean_dec(v_snd_2566_);
lean_ctor_set_float(v_data_2587_, sizeof(void*)*3 + 8, v___x_2589_);
lean_ctor_set_uint8(v_data_2587_, sizeof(void*)*3 + 16, v_collapsed_2531_);
v___y_2552_ = v___y_2573_;
v___y_2553_ = v_m_2582_;
v_data_2554_ = v_data_2587_;
goto v___jp_2551_;
}
}
}
}
v___jp_2592_:
{
lean_object* v_ref_2593_; lean_object* v___x_2594_; 
v_ref_2593_ = lean_ctor_get(v___y_2543_, 5);
lean_inc(v___y_2544_);
lean_inc_ref(v___y_2543_);
lean_inc(v___y_2542_);
lean_inc_ref(v___y_2541_);
lean_inc(v___y_2540_);
lean_inc_ref(v___y_2539_);
lean_inc(v___y_2538_);
lean_inc(v_fst_2546_);
v___x_2594_ = lean_apply_9(v_msg_2536_, v_fst_2546_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, v___y_2542_, v___y_2543_, v___y_2544_, lean_box(0));
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_object* v_a_2595_; 
v_a_2595_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_a_2595_);
lean_dec_ref(v___x_2594_);
v___y_2573_ = v_ref_2593_;
v_a_2574_ = v_a_2595_;
goto v___jp_2572_;
}
else
{
lean_object* v___x_2596_; 
lean_dec_ref(v___x_2594_);
v___x_2596_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__4);
v___y_2573_ = v_ref_2593_;
v_a_2574_ = v___x_2596_;
goto v___jp_2572_;
}
}
v___jp_2597_:
{
if (v_clsEnabled_2534_ == 0)
{
if (v___y_2598_ == 0)
{
lean_object* v___x_2599_; lean_object* v_traceState_2600_; lean_object* v_env_2601_; lean_object* v_nextMacroScope_2602_; lean_object* v_ngen_2603_; lean_object* v_auxDeclNGen_2604_; lean_object* v_cache_2605_; lean_object* v_messages_2606_; lean_object* v_infoState_2607_; lean_object* v_snapshotTasks_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2627_; 
lean_del_object(v___x_2568_);
lean_dec(v_snd_2566_);
lean_dec(v_fst_2565_);
lean_del_object(v___x_2549_);
lean_dec_ref(v_msg_2536_);
lean_dec_ref(v_tag_2532_);
lean_dec(v_cls_2530_);
v___x_2599_ = lean_st_ref_take(v___y_2544_);
v_traceState_2600_ = lean_ctor_get(v___x_2599_, 4);
v_env_2601_ = lean_ctor_get(v___x_2599_, 0);
v_nextMacroScope_2602_ = lean_ctor_get(v___x_2599_, 1);
v_ngen_2603_ = lean_ctor_get(v___x_2599_, 2);
v_auxDeclNGen_2604_ = lean_ctor_get(v___x_2599_, 3);
v_cache_2605_ = lean_ctor_get(v___x_2599_, 5);
v_messages_2606_ = lean_ctor_get(v___x_2599_, 6);
v_infoState_2607_ = lean_ctor_get(v___x_2599_, 7);
v_snapshotTasks_2608_ = lean_ctor_get(v___x_2599_, 8);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2610_ = v___x_2599_;
v_isShared_2611_ = v_isSharedCheck_2627_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_snapshotTasks_2608_);
lean_inc(v_infoState_2607_);
lean_inc(v_messages_2606_);
lean_inc(v_cache_2605_);
lean_inc(v_traceState_2600_);
lean_inc(v_auxDeclNGen_2604_);
lean_inc(v_ngen_2603_);
lean_inc(v_nextMacroScope_2602_);
lean_inc(v_env_2601_);
lean_dec(v___x_2599_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2627_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
uint64_t v_tid_2612_; lean_object* v_traces_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2626_; 
v_tid_2612_ = lean_ctor_get_uint64(v_traceState_2600_, sizeof(void*)*1);
v_traces_2613_ = lean_ctor_get(v_traceState_2600_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v_traceState_2600_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2615_ = v_traceState_2600_;
v_isShared_2616_ = v_isSharedCheck_2626_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_traces_2613_);
lean_dec(v_traceState_2600_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2626_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2617_; lean_object* v___x_2619_; 
v___x_2617_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2535_, v_traces_2613_);
lean_dec_ref(v_traces_2613_);
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v___x_2617_);
v___x_2619_ = v___x_2615_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2617_);
lean_ctor_set_uint64(v_reuseFailAlloc_2625_, sizeof(void*)*1, v_tid_2612_);
v___x_2619_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
lean_object* v___x_2621_; 
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 4, v___x_2619_);
v___x_2621_ = v___x_2610_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_env_2601_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v_nextMacroScope_2602_);
lean_ctor_set(v_reuseFailAlloc_2624_, 2, v_ngen_2603_);
lean_ctor_set(v_reuseFailAlloc_2624_, 3, v_auxDeclNGen_2604_);
lean_ctor_set(v_reuseFailAlloc_2624_, 4, v___x_2619_);
lean_ctor_set(v_reuseFailAlloc_2624_, 5, v_cache_2605_);
lean_ctor_set(v_reuseFailAlloc_2624_, 6, v_messages_2606_);
lean_ctor_set(v_reuseFailAlloc_2624_, 7, v_infoState_2607_);
lean_ctor_set(v_reuseFailAlloc_2624_, 8, v_snapshotTasks_2608_);
v___x_2621_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2622_ = lean_st_ref_set(v___y_2544_, v___x_2621_);
v___x_2623_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__3___redArg(v_fst_2546_);
return v___x_2623_;
}
}
}
}
}
else
{
goto v___jp_2592_;
}
}
else
{
goto v___jp_2592_;
}
}
v___jp_2628_:
{
double v___x_2630_; double v___x_2631_; double v___x_2632_; uint8_t v___x_2633_; 
v___x_2630_ = lean_unbox_float(v_snd_2566_);
v___x_2631_ = lean_unbox_float(v_fst_2565_);
v___x_2632_ = lean_float_sub(v___x_2630_, v___x_2631_);
v___x_2633_ = lean_float_decLt(v___y_2629_, v___x_2632_);
v___y_2598_ = v___x_2633_;
goto v___jp_2597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1___boxed(lean_object* v_cls_2646_, lean_object* v_collapsed_2647_, lean_object* v_tag_2648_, lean_object* v_opts_2649_, lean_object* v_clsEnabled_2650_, lean_object* v_oldTraces_2651_, lean_object* v_msg_2652_, lean_object* v_resStartStop_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
uint8_t v_collapsed_boxed_2662_; uint8_t v_clsEnabled_boxed_2663_; lean_object* v_res_2664_; 
v_collapsed_boxed_2662_ = lean_unbox(v_collapsed_2647_);
v_clsEnabled_boxed_2663_ = lean_unbox(v_clsEnabled_2650_);
v_res_2664_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1(v_cls_2646_, v_collapsed_boxed_2662_, v_tag_2648_, v_opts_2649_, v_clsEnabled_boxed_2663_, v_oldTraces_2651_, v_msg_2652_, v_resStartStop_2653_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v___y_2654_);
lean_dec_ref(v_opts_2649_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove(lean_object* v_e_2665_, lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_){
_start:
{
lean_object* v_____do__lift_2675_; lean_object* v_options_2688_; uint8_t v_hasTrace_2689_; 
v_options_2688_ = lean_ctor_get(v_a_2671_, 2);
v_hasTrace_2689_ = lean_ctor_get_uint8(v_options_2688_, sizeof(void*)*1);
if (v_hasTrace_2689_ == 0)
{
lean_object* v___x_2690_; 
v___x_2690_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_e_2665_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v_a_2691_; 
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2691_);
lean_dec_ref(v___x_2690_);
v_____do__lift_2675_ = v_a_2691_;
goto v___jp_2674_;
}
else
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2699_; 
v_a_2692_ = lean_ctor_get(v___x_2690_, 0);
v_isSharedCheck_2699_ = !lean_is_exclusive(v___x_2690_);
if (v_isSharedCheck_2699_ == 0)
{
v___x_2694_ = v___x_2690_;
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2690_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2699_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2697_; 
if (v_isShared_2695_ == 0)
{
v___x_2697_ = v___x_2694_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2698_; 
v_reuseFailAlloc_2698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2698_, 0, v_a_2692_);
v___x_2697_ = v_reuseFailAlloc_2698_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
return v___x_2697_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2700_; lean_object* v___f_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; uint8_t v___x_2705_; lean_object* v___y_2707_; lean_object* v___y_2708_; lean_object* v_a_2709_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v_a_2724_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v_a_2729_; lean_object* v___y_2739_; lean_object* v___y_2740_; lean_object* v_a_2741_; 
v_inheritedTraceOptions_2700_ = lean_ctor_get(v_a_2671_, 13);
lean_inc_ref(v_e_2665_);
v___f_2701_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_prove___lam__0___boxed), 10, 1);
lean_closure_set(v___f_2701_, 0, v_e_2665_);
v___x_2702_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__2_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_));
v___x_2703_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_2704_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3);
v___x_2705_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2700_, v_options_2688_, v___x_2704_);
if (v___x_2705_ == 0)
{
lean_object* v___x_2790_; uint8_t v___x_2791_; 
v___x_2790_ = l_Lean_trace_profiler;
v___x_2791_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_2688_, v___x_2790_);
if (v___x_2791_ == 0)
{
lean_object* v___x_2792_; 
lean_dec_ref(v___f_2701_);
v___x_2792_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_e_2665_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2793_);
lean_dec_ref(v___x_2792_);
v_____do__lift_2675_ = v_a_2793_;
goto v___jp_2674_;
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
v_a_2794_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2792_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2792_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
else
{
goto v___jp_2743_;
}
}
else
{
goto v___jp_2743_;
}
v___jp_2706_:
{
lean_object* v___x_2710_; double v___x_2711_; double v___x_2712_; double v___x_2713_; double v___x_2714_; double v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v___x_2710_ = lean_io_mono_nanos_now();
v___x_2711_ = lean_float_of_nat(v___y_2708_);
v___x_2712_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4);
v___x_2713_ = lean_float_div(v___x_2711_, v___x_2712_);
v___x_2714_ = lean_float_of_nat(v___x_2710_);
v___x_2715_ = lean_float_div(v___x_2714_, v___x_2712_);
v___x_2716_ = lean_box_float(v___x_2713_);
v___x_2717_ = lean_box_float(v___x_2715_);
v___x_2718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2716_);
lean_ctor_set(v___x_2718_, 1, v___x_2717_);
v___x_2719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2719_, 0, v_a_2709_);
lean_ctor_set(v___x_2719_, 1, v___x_2718_);
v___x_2720_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1(v___x_2702_, v_hasTrace_2689_, v___x_2703_, v_options_2688_, v___x_2705_, v___y_2707_, v___f_2701_, v___x_2719_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
return v___x_2720_;
}
v___jp_2721_:
{
lean_object* v___x_2725_; 
v___x_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2725_, 0, v_a_2724_);
v___y_2707_ = v___y_2722_;
v___y_2708_ = v___y_2723_;
v_a_2709_ = v___x_2725_;
goto v___jp_2706_;
}
v___jp_2726_:
{
lean_object* v___x_2730_; double v___x_2731_; double v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; 
v___x_2730_ = lean_io_get_num_heartbeats();
v___x_2731_ = lean_float_of_nat(v___y_2727_);
v___x_2732_ = lean_float_of_nat(v___x_2730_);
v___x_2733_ = lean_box_float(v___x_2731_);
v___x_2734_ = lean_box_float(v___x_2732_);
v___x_2735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2735_, 0, v___x_2733_);
lean_ctor_set(v___x_2735_, 1, v___x_2734_);
v___x_2736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2736_, 0, v_a_2729_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
v___x_2737_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1(v___x_2702_, v_hasTrace_2689_, v___x_2703_, v_options_2688_, v___x_2705_, v___y_2728_, v___f_2701_, v___x_2736_, v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
return v___x_2737_;
}
v___jp_2738_:
{
lean_object* v___x_2742_; 
v___x_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2742_, 0, v_a_2741_);
v___y_2727_ = v___y_2739_;
v___y_2728_ = v___y_2740_;
v_a_2729_ = v___x_2742_;
goto v___jp_2726_;
}
v___jp_2743_:
{
lean_object* v___x_2744_; lean_object* v_a_2745_; lean_object* v___x_2746_; uint8_t v___x_2747_; 
v___x_2744_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_prove_spec__0___redArg(v_a_2672_);
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2745_);
lean_dec_ref(v___x_2744_);
v___x_2746_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2747_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_2688_, v___x_2746_);
if (v___x_2747_ == 0)
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2748_ = lean_io_mono_nanos_now();
v___x_2749_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_e_2665_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref(v___x_2749_);
if (lean_obj_tag(v_a_2750_) == 0)
{
lean_object* v___x_2751_; 
v___x_2751_ = lean_box(0);
v___y_2722_ = v_a_2745_;
v___y_2723_ = v___x_2748_;
v_a_2724_ = v___x_2751_;
goto v___jp_2721_;
}
else
{
lean_object* v_val_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2760_; 
v_val_2752_ = lean_ctor_get(v_a_2750_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v_a_2750_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2754_ = v_a_2750_;
v_isShared_2755_ = v_isSharedCheck_2760_;
goto v_resetjp_2753_;
}
else
{
lean_inc(v_val_2752_);
lean_dec(v_a_2750_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2760_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2756_; lean_object* v___x_2758_; 
v___x_2756_ = l_Lean_mkFVar(v_val_2752_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 0, v___x_2756_);
v___x_2758_ = v___x_2754_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2756_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
v___y_2722_ = v_a_2745_;
v___y_2723_ = v___x_2748_;
v_a_2724_ = v___x_2758_;
goto v___jp_2721_;
}
}
}
}
else
{
lean_object* v_a_2761_; lean_object* v___x_2763_; uint8_t v_isShared_2764_; uint8_t v_isSharedCheck_2768_; 
v_a_2761_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2768_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2768_ == 0)
{
v___x_2763_ = v___x_2749_;
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
else
{
lean_inc(v_a_2761_);
lean_dec(v___x_2749_);
v___x_2763_ = lean_box(0);
v_isShared_2764_ = v_isSharedCheck_2768_;
goto v_resetjp_2762_;
}
v_resetjp_2762_:
{
lean_object* v___x_2766_; 
if (v_isShared_2764_ == 0)
{
lean_ctor_set_tag(v___x_2763_, 0);
v___x_2766_ = v___x_2763_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2767_; 
v_reuseFailAlloc_2767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2767_, 0, v_a_2761_);
v___x_2766_ = v_reuseFailAlloc_2767_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
v___y_2707_ = v_a_2745_;
v___y_2708_ = v___x_2748_;
v_a_2709_ = v___x_2766_;
goto v___jp_2706_;
}
}
}
}
else
{
lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2769_ = lean_io_get_num_heartbeats();
v___x_2770_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_e_2665_, v_a_2669_, v_a_2670_, v_a_2671_, v_a_2672_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2771_; 
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
lean_inc(v_a_2771_);
lean_dec_ref(v___x_2770_);
if (lean_obj_tag(v_a_2771_) == 0)
{
lean_object* v___x_2772_; 
v___x_2772_ = lean_box(0);
v___y_2739_ = v___x_2769_;
v___y_2740_ = v_a_2745_;
v_a_2741_ = v___x_2772_;
goto v___jp_2738_;
}
else
{
lean_object* v_val_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2781_; 
v_val_2773_ = lean_ctor_get(v_a_2771_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v_a_2771_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2775_ = v_a_2771_;
v_isShared_2776_ = v_isSharedCheck_2781_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_val_2773_);
lean_dec(v_a_2771_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2781_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2777_; lean_object* v___x_2779_; 
v___x_2777_ = l_Lean_mkFVar(v_val_2773_);
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 0, v___x_2777_);
v___x_2779_ = v___x_2775_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2777_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
v___y_2739_ = v___x_2769_;
v___y_2740_ = v_a_2745_;
v_a_2741_ = v___x_2779_;
goto v___jp_2738_;
}
}
}
}
else
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
v_a_2782_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2770_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2770_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
lean_ctor_set_tag(v___x_2784_, 0);
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
v___y_2727_ = v___x_2769_;
v___y_2728_ = v_a_2745_;
v_a_2729_ = v___x_2787_;
goto v___jp_2726_;
}
}
}
}
}
}
v___jp_2674_:
{
if (lean_obj_tag(v_____do__lift_2675_) == 0)
{
lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2676_ = lean_box(0);
v___x_2677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2677_, 0, v___x_2676_);
return v___x_2677_;
}
else
{
lean_object* v_val_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2687_; 
v_val_2678_ = lean_ctor_get(v_____do__lift_2675_, 0);
v_isSharedCheck_2687_ = !lean_is_exclusive(v_____do__lift_2675_);
if (v_isSharedCheck_2687_ == 0)
{
v___x_2680_ = v_____do__lift_2675_;
v_isShared_2681_ = v_isSharedCheck_2687_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_val_2678_);
lean_dec(v_____do__lift_2675_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2687_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2682_; lean_object* v___x_2684_; 
v___x_2682_ = l_Lean_mkFVar(v_val_2678_);
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 0, v___x_2682_);
v___x_2684_ = v___x_2680_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2686_; 
v_reuseFailAlloc_2686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2686_, 0, v___x_2682_);
v___x_2684_ = v_reuseFailAlloc_2686_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
lean_object* v___x_2685_; 
v___x_2685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
return v___x_2685_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_prove___boxed(lean_object* v_e_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_Lean_Elab_Tactic_NormCast_prove(v_e_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_);
lean_dec(v_a_2809_);
lean_dec_ref(v_a_2808_);
lean_dec(v_a_2807_);
lean_dec_ref(v_a_2806_);
lean_dec(v_a_2805_);
lean_dec_ref(v_a_2804_);
lean_dec(v_a_2803_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__3(lean_object* v_00_u03b1_2812_, lean_object* v_x_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v___x_2822_; 
v___x_2822_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__3___redArg(v_x_2813_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2823_, lean_object* v_x_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__3(v_00_u03b1_2823_, v_x_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec(v___y_2825_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__2(lean_object* v_oldTraces_2834_, lean_object* v_data_2835_, lean_object* v_ref_2836_, lean_object* v_msg_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__2___redArg(v_oldTraces_2834_, v_data_2835_, v_ref_2836_, v_msg_2837_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
return v___x_2846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__2___boxed(lean_object* v_oldTraces_2847_, lean_object* v_data_2848_, lean_object* v_ref_2849_, lean_object* v_msg_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v_res_2859_; 
v_res_2859_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_prove_spec__1_spec__2(v_oldTraces_2847_, v_data_2848_, v_ref_2849_, v_msg_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_);
lean_dec(v___y_2857_);
lean_dec_ref(v___y_2856_);
lean_dec(v___y_2855_);
lean_dec_ref(v___y_2854_);
lean_dec(v___y_2853_);
lean_dec_ref(v___y_2852_);
lean_dec(v___y_2851_);
return v_res_2859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0(lean_object* v_a_2860_, lean_object* v_cache_2861_, lean_object* v_a_x3f_2862_){
_start:
{
lean_object* v___x_2864_; lean_object* v_congrCache_2865_; lean_object* v_dsimpCache_2866_; lean_object* v_usedTheorems_2867_; lean_object* v_numSteps_2868_; lean_object* v_diag_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2879_; 
v___x_2864_ = lean_st_ref_take(v_a_2860_);
v_congrCache_2865_ = lean_ctor_get(v___x_2864_, 1);
v_dsimpCache_2866_ = lean_ctor_get(v___x_2864_, 2);
v_usedTheorems_2867_ = lean_ctor_get(v___x_2864_, 3);
v_numSteps_2868_ = lean_ctor_get(v___x_2864_, 4);
v_diag_2869_ = lean_ctor_get(v___x_2864_, 5);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2879_ == 0)
{
lean_object* v_unused_2880_; 
v_unused_2880_ = lean_ctor_get(v___x_2864_, 0);
lean_dec(v_unused_2880_);
v___x_2871_ = v___x_2864_;
v_isShared_2872_ = v_isSharedCheck_2879_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_diag_2869_);
lean_inc(v_numSteps_2868_);
lean_inc(v_usedTheorems_2867_);
lean_inc(v_dsimpCache_2866_);
lean_inc(v_congrCache_2865_);
lean_dec(v___x_2864_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2879_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v_cache_2861_);
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_cache_2861_);
lean_ctor_set(v_reuseFailAlloc_2878_, 1, v_congrCache_2865_);
lean_ctor_set(v_reuseFailAlloc_2878_, 2, v_dsimpCache_2866_);
lean_ctor_set(v_reuseFailAlloc_2878_, 3, v_usedTheorems_2867_);
lean_ctor_set(v_reuseFailAlloc_2878_, 4, v_numSteps_2868_);
lean_ctor_set(v_reuseFailAlloc_2878_, 5, v_diag_2869_);
v___x_2874_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2875_ = lean_st_ref_set(v_a_2860_, v___x_2874_);
v___x_2876_ = lean_box(0);
v___x_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2876_);
return v___x_2877_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0___boxed(lean_object* v_a_2881_, lean_object* v_cache_2882_, lean_object* v_a_x3f_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0(v_a_2881_, v_cache_2882_, v_a_x3f_2883_);
lean_dec(v_a_x3f_2883_);
lean_dec(v_a_2881_);
return v_res_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim(lean_object* v_up_2888_, lean_object* v_e_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v_congrCache_2900_; lean_object* v_dsimpCache_2901_; lean_object* v_usedTheorems_2902_; lean_object* v_numSteps_2903_; lean_object* v_diag_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_3006_; 
v___x_2898_ = lean_st_ref_get(v_a_2892_);
v___x_2899_ = lean_st_ref_take(v_a_2892_);
v_congrCache_2900_ = lean_ctor_get(v___x_2899_, 1);
v_dsimpCache_2901_ = lean_ctor_get(v___x_2899_, 2);
v_usedTheorems_2902_ = lean_ctor_get(v___x_2899_, 3);
v_numSteps_2903_ = lean_ctor_get(v___x_2899_, 4);
v_diag_2904_ = lean_ctor_get(v___x_2899_, 5);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_3006_ == 0)
{
lean_object* v_unused_3007_; 
v_unused_3007_ = lean_ctor_get(v___x_2899_, 0);
lean_dec(v_unused_3007_);
v___x_2906_ = v___x_2899_;
v_isShared_2907_ = v_isSharedCheck_3006_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_diag_2904_);
lean_inc(v_numSteps_2903_);
lean_inc(v_usedTheorems_2902_);
lean_inc(v_dsimpCache_2901_);
lean_inc(v_congrCache_2900_);
lean_dec(v___x_2899_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_3006_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
uint8_t v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2911_; 
v___x_2908_ = 1;
v___x_2909_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__6);
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 0, v___x_2909_);
v___x_2911_ = v___x_2906_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_2909_);
lean_ctor_set(v_reuseFailAlloc_3005_, 1, v_congrCache_2900_);
lean_ctor_set(v_reuseFailAlloc_3005_, 2, v_dsimpCache_2901_);
lean_ctor_set(v_reuseFailAlloc_3005_, 3, v_usedTheorems_2902_);
lean_ctor_set(v_reuseFailAlloc_3005_, 4, v_numSteps_2903_);
lean_ctor_set(v_reuseFailAlloc_3005_, 5, v_diag_2904_);
v___x_2911_ = v_reuseFailAlloc_3005_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
lean_object* v___x_2912_; lean_object* v_post_2913_; lean_object* v_erased_2914_; lean_object* v_cache_2915_; lean_object* v_pre_2916_; lean_object* v_post_2917_; lean_object* v_dpre_2918_; lean_object* v_dpost_2919_; lean_object* v___x_2920_; uint8_t v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v_r_2924_; 
v___x_2912_ = lean_st_ref_set(v_a_2892_, v___x_2911_);
v_post_2913_ = lean_ctor_get(v_up_2888_, 1);
v_erased_2914_ = lean_ctor_get(v_up_2888_, 4);
v_cache_2915_ = lean_ctor_get(v___x_2898_, 0);
lean_inc_ref(v_cache_2915_);
lean_dec(v___x_2898_);
v_pre_2916_ = lean_ctor_get(v_a_2890_, 0);
v_post_2917_ = lean_ctor_get(v_a_2890_, 1);
v_dpre_2918_ = lean_ctor_get(v_a_2890_, 2);
v_dpost_2919_ = lean_ctor_get(v_a_2890_, 3);
v___x_2920_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__0));
v___x_2921_ = 0;
v___x_2922_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_upwardAndElim___closed__1));
lean_inc_ref(v_dpost_2919_);
lean_inc_ref(v_dpre_2918_);
lean_inc_ref(v_post_2917_);
lean_inc_ref(v_pre_2916_);
v___x_2923_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_2923_, 0, v_pre_2916_);
lean_ctor_set(v___x_2923_, 1, v_post_2917_);
lean_ctor_set(v___x_2923_, 2, v_dpre_2918_);
lean_ctor_set(v___x_2923_, 3, v_dpost_2919_);
lean_ctor_set(v___x_2923_, 4, v___x_2920_);
lean_ctor_set_uint8(v___x_2923_, sizeof(void*)*5, v___x_2921_);
lean_inc_ref(v_e_2889_);
v_r_2924_ = l_Lean_Meta_Simp_rewrite_x3f(v_e_2889_, v_post_2913_, v_erased_2914_, v___x_2922_, v___x_2921_, v___x_2923_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_);
lean_dec_ref(v___x_2923_);
if (lean_obj_tag(v_r_2924_) == 0)
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2993_; 
v_a_2925_ = lean_ctor_get(v_r_2924_, 0);
v_isSharedCheck_2993_ = !lean_is_exclusive(v_r_2924_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2927_ = v_r_2924_;
v_isShared_2928_ = v_isSharedCheck_2993_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v_r_2924_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2993_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
lean_inc(v_a_2925_);
if (v_isShared_2928_ == 0)
{
lean_ctor_set_tag(v___x_2927_, 1);
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
lean_object* v___x_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2990_; 
v___x_2931_ = l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0(v_a_2892_, v_cache_2915_, v___x_2930_);
lean_dec_ref(v___x_2930_);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2990_ == 0)
{
lean_object* v_unused_2991_; 
v_unused_2991_ = lean_ctor_get(v___x_2931_, 0);
lean_dec(v_unused_2991_);
v___x_2933_ = v___x_2931_;
v_isShared_2934_ = v_isSharedCheck_2990_;
goto v_resetjp_2932_;
}
else
{
lean_dec(v___x_2931_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2990_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___y_2936_; lean_object* v_expr_2937_; 
if (lean_obj_tag(v_a_2925_) == 0)
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = lean_box(0);
lean_inc_ref_n(v_e_2889_, 2);
v___x_2987_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2987_, 0, v_e_2889_);
lean_ctor_set(v___x_2987_, 1, v___x_2986_);
lean_ctor_set_uint8(v___x_2987_, sizeof(void*)*2, v___x_2908_);
v___y_2936_ = v___x_2987_;
v_expr_2937_ = v_e_2889_;
goto v___jp_2935_;
}
else
{
lean_object* v_val_2988_; lean_object* v_expr_2989_; 
v_val_2988_ = lean_ctor_get(v_a_2925_, 0);
lean_inc(v_val_2988_);
lean_dec_ref(v_a_2925_);
v_expr_2989_ = lean_ctor_get(v_val_2988_, 0);
lean_inc_ref(v_expr_2989_);
v___y_2936_ = v_val_2988_;
v_expr_2937_ = v_expr_2989_;
goto v___jp_2935_;
}
v___jp_2935_:
{
lean_object* v___x_2938_; 
v___x_2938_ = l_Lean_Elab_Tactic_NormCast_splittingProcedure(v_expr_2937_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v___x_2940_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref(v___x_2938_);
v___x_2940_ = l_Lean_Meta_Simp_Result_mkEqTrans(v___y_2936_, v_a_2939_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2969_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2943_ = v___x_2940_;
v_isShared_2944_ = v_isSharedCheck_2969_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2940_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2969_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v_expr_2945_; uint8_t v___x_2946_; 
v_expr_2945_ = lean_ctor_get(v_a_2941_, 0);
v___x_2946_ = lean_expr_eqv(v_expr_2945_, v_e_2889_);
if (v___x_2946_ == 0)
{
lean_object* v___x_2948_; 
lean_dec_ref(v_e_2889_);
if (v_isShared_2934_ == 0)
{
lean_ctor_set_tag(v___x_2933_, 1);
lean_ctor_set(v___x_2933_, 0, v_a_2941_);
v___x_2948_ = v___x_2933_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2941_);
v___x_2948_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
lean_object* v___x_2950_; 
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v___x_2948_);
v___x_2950_ = v___x_2943_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v___x_2948_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
else
{
lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2966_; 
v_isSharedCheck_2966_ = !lean_is_exclusive(v_a_2941_);
if (v_isSharedCheck_2966_ == 0)
{
lean_object* v_unused_2967_; lean_object* v_unused_2968_; 
v_unused_2967_ = lean_ctor_get(v_a_2941_, 1);
lean_dec(v_unused_2967_);
v_unused_2968_ = lean_ctor_get(v_a_2941_, 0);
lean_dec(v_unused_2968_);
v___x_2954_ = v_a_2941_;
v_isShared_2955_ = v_isSharedCheck_2966_;
goto v_resetjp_2953_;
}
else
{
lean_dec(v_a_2941_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2966_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2956_; lean_object* v___x_2958_; 
v___x_2956_ = lean_box(0);
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 1, v___x_2956_);
lean_ctor_set(v___x_2954_, 0, v_e_2889_);
v___x_2958_ = v___x_2954_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_e_2889_);
lean_ctor_set(v_reuseFailAlloc_2965_, 1, v___x_2956_);
v___x_2958_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
lean_object* v___x_2960_; 
lean_ctor_set_uint8(v___x_2958_, sizeof(void*)*2, v___x_2946_);
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 0, v___x_2958_);
v___x_2960_ = v___x_2933_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v___x_2958_);
v___x_2960_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
lean_object* v___x_2962_; 
if (v_isShared_2944_ == 0)
{
lean_ctor_set(v___x_2943_, 0, v___x_2960_);
v___x_2962_ = v___x_2943_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v___x_2960_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_del_object(v___x_2933_);
lean_dec_ref(v_e_2889_);
v_a_2970_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2940_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2940_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
else
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
lean_dec_ref(v___y_2936_);
lean_del_object(v___x_2933_);
lean_dec_ref(v_e_2889_);
v_a_2978_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___x_2938_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2938_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_a_2978_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
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
lean_object* v_a_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
lean_dec_ref(v_e_2889_);
v_a_2994_ = lean_ctor_get(v_r_2924_, 0);
lean_inc(v_a_2994_);
lean_dec_ref(v_r_2924_);
v___x_2995_ = lean_box(0);
v___x_2996_ = l_Lean_Elab_Tactic_NormCast_upwardAndElim___lam__0(v_a_2892_, v_cache_2915_, v___x_2995_);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3003_ == 0)
{
lean_object* v_unused_3004_; 
v_unused_3004_ = lean_ctor_get(v___x_2996_, 0);
lean_dec(v_unused_3004_);
v___x_2998_ = v___x_2996_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_dec(v___x_2996_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
lean_ctor_set_tag(v___x_2998_, 1);
lean_ctor_set(v___x_2998_, 0, v_a_2994_);
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2994_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_upwardAndElim___boxed(lean_object* v_up_3008_, lean_object* v_e_3009_, lean_object* v_a_3010_, lean_object* v_a_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_){
_start:
{
lean_object* v_res_3018_; 
v_res_3018_ = l_Lean_Elab_Tactic_NormCast_upwardAndElim(v_up_3008_, v_e_3009_, v_a_3010_, v_a_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_);
lean_dec(v_a_3016_);
lean_dec_ref(v_a_3015_);
lean_dec(v_a_3014_);
lean_dec_ref(v_a_3013_);
lean_dec(v_a_3012_);
lean_dec_ref(v_a_3011_);
lean_dec(v_a_3010_);
lean_dec_ref(v_up_3008_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_numeralToCoe(lean_object* v_e_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_){
_start:
{
lean_object* v___x_3029_; 
v___x_3029_ = l_Lean_Elab_Tactic_NormCast_isNumeral_x3f(v_e_3023_);
if (lean_obj_tag(v___x_3029_) == 1)
{
lean_object* v_val_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3105_; 
v_val_3030_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3032_ = v___x_3029_;
v_isShared_3033_ = v_isSharedCheck_3105_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_val_3030_);
lean_dec(v___x_3029_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3105_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v_fst_3034_; lean_object* v_snd_3035_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___x_3083_; 
v_fst_3034_ = lean_ctor_get(v_val_3030_, 0);
lean_inc_n(v_fst_3034_, 2);
v_snd_3035_ = lean_ctor_get(v_val_3030_, 1);
lean_inc(v_snd_3035_);
lean_dec(v_val_3030_);
lean_inc(v_a_3027_);
lean_inc_ref(v_a_3026_);
lean_inc(v_a_3025_);
lean_inc_ref(v_a_3024_);
v___x_3083_ = lean_whnf(v_fst_3034_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_a_3084_; lean_object* v___x_3085_; uint8_t v___x_3086_; 
v_a_3084_ = lean_ctor_get(v___x_3083_, 0);
lean_inc(v_a_3084_);
lean_dec_ref(v___x_3083_);
v___x_3085_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_isNumeral_x3f___closed__5));
v___x_3086_ = l_Lean_Expr_isConstOf(v_a_3084_, v___x_3085_);
lean_dec(v_a_3084_);
if (v___x_3086_ == 0)
{
v___y_3037_ = v_a_3024_;
v___y_3038_ = v_a_3025_;
v___y_3039_ = v_a_3026_;
v___y_3040_ = v_a_3027_;
goto v___jp_3036_;
}
else
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
lean_dec(v_snd_3035_);
lean_dec(v_fst_3034_);
lean_del_object(v___x_3032_);
lean_dec_ref(v_e_3023_);
v___x_3087_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_3088_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_3087_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3088_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3088_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
else
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
lean_dec(v_snd_3035_);
lean_dec(v_fst_3034_);
lean_del_object(v___x_3032_);
lean_dec_ref(v_e_3023_);
v_a_3097_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3083_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3083_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
v___jp_3036_:
{
lean_object* v___x_3041_; lean_object* v___x_3043_; 
v___x_3041_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_numeralToCoe___closed__1));
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 0, v_fst_3034_);
v___x_3043_ = v___x_3032_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_fst_3034_);
v___x_3043_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3044_ = lean_box(0);
v___x_3045_ = l_Lean_mkNatLit(v_snd_3035_);
v___x_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3045_);
v___x_3047_ = lean_unsigned_to_nat(3u);
v___x_3048_ = lean_mk_empty_array_with_capacity(v___x_3047_);
v___x_3049_ = lean_array_push(v___x_3048_, v___x_3043_);
v___x_3050_ = lean_array_push(v___x_3049_, v___x_3044_);
v___x_3051_ = lean_array_push(v___x_3050_, v___x_3046_);
v___x_3052_ = l_Lean_Meta_mkAppOptM(v___x_3041_, v___x_3051_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; lean_object* v___x_3054_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
lean_dec_ref(v___x_3052_);
v___x_3054_ = l_Lean_Elab_Tactic_NormCast_proveEqUsingDown(v_e_3023_, v_a_3053_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3065_; 
v_a_3055_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3057_ = v___x_3054_;
v_isShared_3058_ = v_isSharedCheck_3065_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3054_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3065_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
if (lean_obj_tag(v_a_3055_) == 1)
{
lean_object* v_val_3059_; lean_object* v___x_3061_; 
v_val_3059_ = lean_ctor_get(v_a_3055_, 0);
lean_inc(v_val_3059_);
lean_dec_ref(v_a_3055_);
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 0, v_val_3059_);
v___x_3061_ = v___x_3057_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_val_3059_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
else
{
lean_object* v___x_3063_; lean_object* v___x_3064_; 
lean_del_object(v___x_3057_);
lean_dec(v_a_3055_);
v___x_3063_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_3064_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_3063_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
return v___x_3064_;
}
}
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
v_a_3066_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_3054_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3054_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
else
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
lean_dec_ref(v_e_3023_);
v_a_3074_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_3052_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_3052_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3074_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3106_; lean_object* v___x_3107_; 
lean_dec(v___x_3029_);
lean_dec_ref(v_e_3023_);
v___x_3106_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1, &l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_mkCoe___closed__1);
v___x_3107_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_mkCoe_spec__0___redArg(v___x_3106_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_);
return v___x_3107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_numeralToCoe___boxed(lean_object* v_e_3108_, lean_object* v_a_3109_, lean_object* v_a_3110_, lean_object* v_a_3111_, lean_object* v_a_3112_, lean_object* v_a_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l_Lean_Elab_Tactic_NormCast_numeralToCoe(v_e_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_);
lean_dec(v_a_3112_);
lean_dec_ref(v_a_3111_);
lean_dec(v_a_3110_);
lean_dec_ref(v_a_3109_);
return v_res_3114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(lean_object* v_e_3123_, lean_object* v_a_3124_, lean_object* v_a_3125_, lean_object* v_a_3126_, lean_object* v_a_3127_){
_start:
{
lean_object* v___x_3129_; uint8_t v___x_3130_; uint8_t v___x_3131_; lean_object* v___x_3132_; 
v___x_3129_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_));
v___x_3130_ = 0;
v___x_3131_ = 1;
v___x_3132_ = l_Lean_Meta_evalExpr_x27___redArg(v___x_3129_, v_e_3123_, v___x_3130_, v___x_3131_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3____boxed(lean_object* v_e_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(v_e_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_);
lean_dec(v_a_3137_);
lean_dec_ref(v_a_3136_);
lean_dec(v_a_3135_);
lean_dec_ref(v_a_3134_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(lean_object* v_e_3140_, lean_object* v_a_3141_, lean_object* v_a_3142_, lean_object* v_a_3143_, lean_object* v_a_3144_, lean_object* v_a_3145_, lean_object* v_a_3146_){
_start:
{
lean_object* v___x_3148_; 
v___x_3148_ = l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(v_e_3140_, v_a_3143_, v_a_3144_, v_a_3145_, v_a_3146_);
return v___x_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalUnsafe_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3____boxed(lean_object* v_e_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_){
_start:
{
lean_object* v_res_3157_; 
v_res_3157_ = l_Lean_Elab_Tactic_NormCast_evalUnsafe_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(v_e_3149_, v_a_3150_, v_a_3151_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_a_3153_);
lean_dec_ref(v_a_3152_);
lean_dec(v_a_3151_);
lean_dec_ref(v_a_3150_);
return v_res_3157_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__0(void){
_start:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3158_ = lean_box(1);
v___x_3159_ = l_Lean_MessageData_ofFormat(v___x_3158_);
return v___x_3159_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__3(void){
_start:
{
lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3163_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__2));
v___x_3164_ = l_Lean_MessageData_ofFormat(v___x_3163_);
return v___x_3164_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8(lean_object* v_x_3165_, lean_object* v_x_3166_){
_start:
{
if (lean_obj_tag(v_x_3166_) == 0)
{
return v_x_3165_;
}
else
{
lean_object* v_head_3167_; lean_object* v_tail_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3190_; 
v_head_3167_ = lean_ctor_get(v_x_3166_, 0);
v_tail_3168_ = lean_ctor_get(v_x_3166_, 1);
v_isSharedCheck_3190_ = !lean_is_exclusive(v_x_3166_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3170_ = v_x_3166_;
v_isShared_3171_ = v_isSharedCheck_3190_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_tail_3168_);
lean_inc(v_head_3167_);
lean_dec(v_x_3166_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3190_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v_before_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3188_; 
v_before_3172_ = lean_ctor_get(v_head_3167_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v_head_3167_);
if (v_isSharedCheck_3188_ == 0)
{
lean_object* v_unused_3189_; 
v_unused_3189_ = lean_ctor_get(v_head_3167_, 1);
lean_dec(v_unused_3189_);
v___x_3174_ = v_head_3167_;
v_isShared_3175_ = v_isSharedCheck_3188_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_before_3172_);
lean_dec(v_head_3167_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3188_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3176_; lean_object* v___x_3178_; 
v___x_3176_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__0);
if (v_isShared_3175_ == 0)
{
lean_ctor_set_tag(v___x_3174_, 7);
lean_ctor_set(v___x_3174_, 1, v___x_3176_);
lean_ctor_set(v___x_3174_, 0, v_x_3165_);
v___x_3178_ = v___x_3174_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_x_3165_);
lean_ctor_set(v_reuseFailAlloc_3187_, 1, v___x_3176_);
v___x_3178_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
lean_object* v___x_3179_; lean_object* v___x_3181_; 
v___x_3179_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__3);
if (v_isShared_3171_ == 0)
{
lean_ctor_set_tag(v___x_3170_, 7);
lean_ctor_set(v___x_3170_, 1, v___x_3179_);
lean_ctor_set(v___x_3170_, 0, v___x_3178_);
v___x_3181_ = v___x_3170_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v___x_3178_);
lean_ctor_set(v_reuseFailAlloc_3186_, 1, v___x_3179_);
v___x_3181_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3182_ = l_Lean_MessageData_ofSyntax(v_before_3172_);
v___x_3183_ = l_Lean_indentD(v___x_3182_);
v___x_3184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3181_);
lean_ctor_set(v___x_3184_, 1, v___x_3183_);
v_x_3165_ = v___x_3184_;
v_x_3166_ = v_tail_3168_;
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
lean_object* v___x_3194_; lean_object* v___x_3195_; 
v___x_3194_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__1));
v___x_3195_ = l_Lean_MessageData_ofFormat(v___x_3194_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg(lean_object* v_msgData_3196_, lean_object* v_macroStack_3197_, lean_object* v___y_3198_){
_start:
{
lean_object* v_options_3200_; lean_object* v___x_3201_; uint8_t v___x_3202_; 
v_options_3200_ = lean_ctor_get(v___y_3198_, 2);
v___x_3201_ = l_Lean_Elab_pp_macroStack;
v___x_3202_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_3200_, v___x_3201_);
if (v___x_3202_ == 0)
{
lean_object* v___x_3203_; 
lean_dec(v_macroStack_3197_);
v___x_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3203_, 0, v_msgData_3196_);
return v___x_3203_;
}
else
{
if (lean_obj_tag(v_macroStack_3197_) == 0)
{
lean_object* v___x_3204_; 
v___x_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3204_, 0, v_msgData_3196_);
return v___x_3204_;
}
else
{
lean_object* v_head_3205_; lean_object* v_after_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3221_; 
v_head_3205_ = lean_ctor_get(v_macroStack_3197_, 0);
lean_inc(v_head_3205_);
v_after_3206_ = lean_ctor_get(v_head_3205_, 1);
v_isSharedCheck_3221_ = !lean_is_exclusive(v_head_3205_);
if (v_isSharedCheck_3221_ == 0)
{
lean_object* v_unused_3222_; 
v_unused_3222_ = lean_ctor_get(v_head_3205_, 0);
lean_dec(v_unused_3222_);
v___x_3208_ = v_head_3205_;
v_isShared_3209_ = v_isSharedCheck_3221_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_after_3206_);
lean_dec(v_head_3205_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3221_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3210_; lean_object* v___x_3212_; 
v___x_3210_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8___closed__0);
if (v_isShared_3209_ == 0)
{
lean_ctor_set_tag(v___x_3208_, 7);
lean_ctor_set(v___x_3208_, 1, v___x_3210_);
lean_ctor_set(v___x_3208_, 0, v_msgData_3196_);
v___x_3212_ = v___x_3208_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_msgData_3196_);
lean_ctor_set(v_reuseFailAlloc_3220_, 1, v___x_3210_);
v___x_3212_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v_msgData_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3213_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___closed__2);
v___x_3214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3214_, 0, v___x_3212_);
lean_ctor_set(v___x_3214_, 1, v___x_3213_);
v___x_3215_ = l_Lean_MessageData_ofSyntax(v_after_3206_);
v___x_3216_ = l_Lean_indentD(v___x_3215_);
v_msgData_3217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_3217_, 0, v___x_3214_);
lean_ctor_set(v_msgData_3217_, 1, v___x_3216_);
v___x_3218_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4_spec__8(v_msgData_3217_, v_macroStack_3197_);
v___x_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3219_, 0, v___x_3218_);
return v___x_3219_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg___boxed(lean_object* v_msgData_3223_, lean_object* v_macroStack_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg(v_msgData_3223_, v_macroStack_3224_, v___y_3225_);
lean_dec_ref(v___y_3225_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg(lean_object* v_msg_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_){
_start:
{
lean_object* v_ref_3236_; lean_object* v___x_3237_; lean_object* v_a_3238_; lean_object* v_macroStack_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3250_; 
v_ref_3236_ = lean_ctor_get(v___y_3233_, 5);
v___x_3237_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__5(v_msg_3228_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
v_a_3238_ = lean_ctor_get(v___x_3237_, 0);
lean_inc(v_a_3238_);
lean_dec_ref(v___x_3237_);
v_macroStack_3239_ = lean_ctor_get(v___y_3229_, 1);
v___x_3240_ = l_Lean_Elab_getBetterRef(v_ref_3236_, v_macroStack_3239_);
lean_inc(v_macroStack_3239_);
v___x_3241_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg(v_a_3238_, v_macroStack_3239_, v___y_3233_);
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3244_ = v___x_3241_;
v_isShared_3245_ = v_isSharedCheck_3250_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3241_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3250_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3246_; lean_object* v___x_3248_; 
v___x_3246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3240_);
lean_ctor_set(v___x_3246_, 1, v_a_3242_);
if (v_isShared_3245_ == 0)
{
lean_ctor_set_tag(v___x_3244_, 1);
lean_ctor_set(v___x_3244_, 0, v___x_3246_);
v___x_3248_ = v___x_3244_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3246_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg___boxed(lean_object* v_msg_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_, lean_object* v___y_3258_){
_start:
{
lean_object* v_res_3259_; 
v_res_3259_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg(v_msg_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
lean_dec(v___y_3257_);
lean_dec_ref(v___y_3256_);
lean_dec(v___y_3255_);
lean_dec_ref(v___y_3254_);
lean_dec(v___y_3253_);
lean_dec_ref(v___y_3252_);
return v_res_3259_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg(lean_object* v_cls_3262_, lean_object* v_msg_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_){
_start:
{
lean_object* v_ref_3269_; lean_object* v___x_3270_; lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3315_; 
v_ref_3269_ = lean_ctor_get(v___y_3266_, 5);
v___x_3270_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2_spec__3_spec__5(v_msg_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_);
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3273_ = v___x_3270_;
v_isShared_3274_ = v_isSharedCheck_3315_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3270_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3315_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3275_; lean_object* v_traceState_3276_; lean_object* v_env_3277_; lean_object* v_nextMacroScope_3278_; lean_object* v_ngen_3279_; lean_object* v_auxDeclNGen_3280_; lean_object* v_cache_3281_; lean_object* v_messages_3282_; lean_object* v_infoState_3283_; lean_object* v_snapshotTasks_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3314_; 
v___x_3275_ = lean_st_ref_take(v___y_3267_);
v_traceState_3276_ = lean_ctor_get(v___x_3275_, 4);
v_env_3277_ = lean_ctor_get(v___x_3275_, 0);
v_nextMacroScope_3278_ = lean_ctor_get(v___x_3275_, 1);
v_ngen_3279_ = lean_ctor_get(v___x_3275_, 2);
v_auxDeclNGen_3280_ = lean_ctor_get(v___x_3275_, 3);
v_cache_3281_ = lean_ctor_get(v___x_3275_, 5);
v_messages_3282_ = lean_ctor_get(v___x_3275_, 6);
v_infoState_3283_ = lean_ctor_get(v___x_3275_, 7);
v_snapshotTasks_3284_ = lean_ctor_get(v___x_3275_, 8);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3286_ = v___x_3275_;
v_isShared_3287_ = v_isSharedCheck_3314_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_snapshotTasks_3284_);
lean_inc(v_infoState_3283_);
lean_inc(v_messages_3282_);
lean_inc(v_cache_3281_);
lean_inc(v_traceState_3276_);
lean_inc(v_auxDeclNGen_3280_);
lean_inc(v_ngen_3279_);
lean_inc(v_nextMacroScope_3278_);
lean_inc(v_env_3277_);
lean_dec(v___x_3275_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3314_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
uint64_t v_tid_3288_; lean_object* v_traces_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3313_; 
v_tid_3288_ = lean_ctor_get_uint64(v_traceState_3276_, sizeof(void*)*1);
v_traces_3289_ = lean_ctor_get(v_traceState_3276_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v_traceState_3276_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3291_ = v_traceState_3276_;
v_isShared_3292_ = v_isSharedCheck_3313_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_traces_3289_);
lean_dec(v_traceState_3276_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3313_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; double v___x_3294_; uint8_t v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3303_; 
v___x_3293_ = lean_box(0);
v___x_3294_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__2);
v___x_3295_ = 0;
v___x_3296_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_3297_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3297_, 0, v_cls_3262_);
lean_ctor_set(v___x_3297_, 1, v___x_3293_);
lean_ctor_set(v___x_3297_, 2, v___x_3296_);
lean_ctor_set_float(v___x_3297_, sizeof(void*)*3, v___x_3294_);
lean_ctor_set_float(v___x_3297_, sizeof(void*)*3 + 8, v___x_3294_);
lean_ctor_set_uint8(v___x_3297_, sizeof(void*)*3 + 16, v___x_3295_);
v___x_3298_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_3299_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3297_);
lean_ctor_set(v___x_3299_, 1, v_a_3271_);
lean_ctor_set(v___x_3299_, 2, v___x_3298_);
lean_inc(v_ref_3269_);
v___x_3300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3300_, 0, v_ref_3269_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
v___x_3301_ = l_Lean_PersistentArray_push___redArg(v_traces_3289_, v___x_3300_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 0, v___x_3301_);
v___x_3303_ = v___x_3291_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3301_);
lean_ctor_set_uint64(v_reuseFailAlloc_3312_, sizeof(void*)*1, v_tid_3288_);
v___x_3303_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
lean_object* v___x_3305_; 
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 4, v___x_3303_);
v___x_3305_ = v___x_3286_;
goto v_reusejp_3304_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_env_3277_);
lean_ctor_set(v_reuseFailAlloc_3311_, 1, v_nextMacroScope_3278_);
lean_ctor_set(v_reuseFailAlloc_3311_, 2, v_ngen_3279_);
lean_ctor_set(v_reuseFailAlloc_3311_, 3, v_auxDeclNGen_3280_);
lean_ctor_set(v_reuseFailAlloc_3311_, 4, v___x_3303_);
lean_ctor_set(v_reuseFailAlloc_3311_, 5, v_cache_3281_);
lean_ctor_set(v_reuseFailAlloc_3311_, 6, v_messages_3282_);
lean_ctor_set(v_reuseFailAlloc_3311_, 7, v_infoState_3283_);
lean_ctor_set(v_reuseFailAlloc_3311_, 8, v_snapshotTasks_3284_);
v___x_3305_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3304_;
}
v_reusejp_3304_:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3309_; 
v___x_3306_ = lean_st_ref_set(v___y_3267_, v___x_3305_);
v___x_3307_ = lean_box(0);
if (v_isShared_3274_ == 0)
{
lean_ctor_set(v___x_3273_, 0, v___x_3307_);
v___x_3309_ = v___x_3273_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v___x_3307_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_cls_3316_, lean_object* v_msg_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v_res_3323_; 
v_res_3323_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg(v_cls_3316_, v_msg_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec(v___y_3319_);
lean_dec_ref(v___y_3318_);
return v_res_3323_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(lean_object* v_keys_3324_, lean_object* v_i_3325_, lean_object* v_k_3326_){
_start:
{
lean_object* v___x_3327_; uint8_t v___x_3328_; 
v___x_3327_ = lean_array_get_size(v_keys_3324_);
v___x_3328_ = lean_nat_dec_lt(v_i_3325_, v___x_3327_);
if (v___x_3328_ == 0)
{
lean_dec(v_i_3325_);
return v___x_3328_;
}
else
{
lean_object* v_k_x27_3329_; uint8_t v___x_3330_; 
v_k_x27_3329_ = lean_array_fget_borrowed(v_keys_3324_, v_i_3325_);
v___x_3330_ = l_Lean_instBEqExtraModUse_beq(v_k_3326_, v_k_x27_3329_);
if (v___x_3330_ == 0)
{
lean_object* v___x_3331_; lean_object* v___x_3332_; 
v___x_3331_ = lean_unsigned_to_nat(1u);
v___x_3332_ = lean_nat_add(v_i_3325_, v___x_3331_);
lean_dec(v_i_3325_);
v_i_3325_ = v___x_3332_;
goto _start;
}
else
{
lean_dec(v_i_3325_);
return v___x_3330_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__7___redArg___boxed(lean_object* v_keys_3334_, lean_object* v_i_3335_, lean_object* v_k_3336_){
_start:
{
uint8_t v_res_3337_; lean_object* v_r_3338_; 
v_res_3337_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_3334_, v_i_3335_, v_k_3336_);
lean_dec_ref(v_k_3336_);
lean_dec_ref(v_keys_3334_);
v_r_3338_ = lean_box(v_res_3337_);
return v_r_3338_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0(void){
_start:
{
size_t v___x_3339_; size_t v___x_3340_; size_t v___x_3341_; 
v___x_3339_ = ((size_t)5ULL);
v___x_3340_ = ((size_t)1ULL);
v___x_3341_ = lean_usize_shift_left(v___x_3340_, v___x_3339_);
return v___x_3341_;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_3342_; size_t v___x_3343_; size_t v___x_3344_; 
v___x_3342_ = ((size_t)1ULL);
v___x_3343_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__0);
v___x_3344_ = lean_usize_sub(v___x_3343_, v___x_3342_);
return v___x_3344_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_x_3345_, size_t v_x_3346_, lean_object* v_x_3347_){
_start:
{
if (lean_obj_tag(v_x_3345_) == 0)
{
lean_object* v_es_3348_; lean_object* v___x_3349_; size_t v___x_3350_; size_t v___x_3351_; size_t v___x_3352_; lean_object* v_j_3353_; lean_object* v___x_3354_; 
v_es_3348_ = lean_ctor_get(v_x_3345_, 0);
v___x_3349_ = lean_box(2);
v___x_3350_ = ((size_t)5ULL);
v___x_3351_ = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___closed__1);
v___x_3352_ = lean_usize_land(v_x_3346_, v___x_3351_);
v_j_3353_ = lean_usize_to_nat(v___x_3352_);
v___x_3354_ = lean_array_get_borrowed(v___x_3349_, v_es_3348_, v_j_3353_);
lean_dec(v_j_3353_);
switch(lean_obj_tag(v___x_3354_))
{
case 0:
{
lean_object* v_key_3355_; uint8_t v___x_3356_; 
v_key_3355_ = lean_ctor_get(v___x_3354_, 0);
v___x_3356_ = l_Lean_instBEqExtraModUse_beq(v_x_3347_, v_key_3355_);
return v___x_3356_;
}
case 1:
{
lean_object* v_node_3357_; size_t v___x_3358_; 
v_node_3357_ = lean_ctor_get(v___x_3354_, 0);
v___x_3358_ = lean_usize_shift_right(v_x_3346_, v___x_3350_);
v_x_3345_ = v_node_3357_;
v_x_3346_ = v___x_3358_;
goto _start;
}
default: 
{
uint8_t v___x_3360_; 
v___x_3360_ = 0;
return v___x_3360_;
}
}
}
else
{
lean_object* v_ks_3361_; lean_object* v___x_3362_; uint8_t v___x_3363_; 
v_ks_3361_ = lean_ctor_get(v_x_3345_, 0);
v___x_3362_ = lean_unsigned_to_nat(0u);
v___x_3363_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ks_3361_, v___x_3362_, v_x_3347_);
return v___x_3363_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_x_3364_, lean_object* v_x_3365_, lean_object* v_x_3366_){
_start:
{
size_t v_x_12090__boxed_3367_; uint8_t v_res_3368_; lean_object* v_r_3369_; 
v_x_12090__boxed_3367_ = lean_unbox_usize(v_x_3365_);
lean_dec(v_x_3365_);
v_res_3368_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg(v_x_3364_, v_x_12090__boxed_3367_, v_x_3366_);
lean_dec_ref(v_x_3366_);
lean_dec_ref(v_x_3364_);
v_r_3369_ = lean_box(v_res_3368_);
return v_r_3369_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___redArg(lean_object* v_x_3370_, lean_object* v_x_3371_){
_start:
{
uint64_t v___x_3372_; size_t v___x_3373_; uint8_t v___x_3374_; 
v___x_3372_ = l_Lean_instHashableExtraModUse_hash(v_x_3371_);
v___x_3373_ = lean_uint64_to_usize(v___x_3372_);
v___x_3374_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg(v_x_3370_, v___x_3373_, v_x_3371_);
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_3375_, lean_object* v_x_3376_){
_start:
{
uint8_t v_res_3377_; lean_object* v_r_3378_; 
v_res_3377_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___redArg(v_x_3375_, v_x_3376_);
lean_dec_ref(v_x_3376_);
lean_dec_ref(v_x_3375_);
v_r_3378_ = lean_box(v_res_3377_);
return v_r_3378_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
v___x_3381_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__1));
v___x_3382_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__0));
v___x_3383_ = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_3382_, v___x_3381_);
return v___x_3383_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_3384_; 
v___x_3384_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3384_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4(void){
_start:
{
lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3385_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__3);
v___x_3386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3385_);
return v___x_3386_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3387_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4);
v___x_3388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3388_, 0, v___x_3387_);
lean_ctor_set(v___x_3388_, 1, v___x_3387_);
return v___x_3388_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__6(void){
_start:
{
lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3389_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__4);
v___x_3390_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3389_);
lean_ctor_set(v___x_3390_, 1, v___x_3389_);
lean_ctor_set(v___x_3390_, 2, v___x_3389_);
lean_ctor_set(v___x_3390_, 3, v___x_3389_);
lean_ctor_set(v___x_3390_, 4, v___x_3389_);
lean_ctor_set(v___x_3390_, 5, v___x_3389_);
return v___x_3390_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3395_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__9));
v___x_3396_ = l_Lean_stringToMessageData(v___x_3395_);
return v___x_3396_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__12(void){
_start:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3398_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__11));
v___x_3399_ = l_Lean_stringToMessageData(v___x_3398_);
return v___x_3399_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__13(void){
_start:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_3401_ = l_Lean_stringToMessageData(v___x_3400_);
return v___x_3401_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__14(void){
_start:
{
lean_object* v_cls_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; 
v_cls_3402_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__8));
v___x_3403_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__2));
v___x_3404_ = l_Lean_Name_append(v___x_3403_, v_cls_3402_);
return v___x_3404_;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__16(void){
_start:
{
lean_object* v___x_3406_; lean_object* v___x_3407_; 
v___x_3406_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__15));
v___x_3407_ = l_Lean_stringToMessageData(v___x_3406_);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0(lean_object* v_mod_3412_, uint8_t v_isMeta_3413_, lean_object* v_hint_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v___x_3422_; lean_object* v_env_3423_; uint8_t v_isExporting_3424_; lean_object* v___x_3425_; lean_object* v_env_3426_; lean_object* v___x_3427_; lean_object* v_entry_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___x_3474_; uint8_t v___x_3475_; 
v___x_3422_ = lean_st_ref_get(v___y_3420_);
v_env_3423_ = lean_ctor_get(v___x_3422_, 0);
lean_inc_ref(v_env_3423_);
lean_dec(v___x_3422_);
v_isExporting_3424_ = lean_ctor_get_uint8(v_env_3423_, sizeof(void*)*8);
lean_dec_ref(v_env_3423_);
v___x_3425_ = lean_st_ref_get(v___y_3420_);
v_env_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc_ref(v_env_3426_);
lean_dec(v___x_3425_);
v___x_3427_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__2);
lean_inc(v_mod_3412_);
v_entry_3428_ = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(v_entry_3428_, 0, v_mod_3412_);
lean_ctor_set_uint8(v_entry_3428_, sizeof(void*)*1, v_isExporting_3424_);
lean_ctor_set_uint8(v_entry_3428_, sizeof(void*)*1 + 1, v_isMeta_3413_);
v___x_3429_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
v___x_3430_ = lean_box(1);
v___x_3431_ = lean_box(0);
v___x_3474_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3427_, v___x_3429_, v_env_3426_, v___x_3430_, v___x_3431_);
v___x_3475_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___redArg(v___x_3474_, v_entry_3428_);
lean_dec(v___x_3474_);
if (v___x_3475_ == 0)
{
lean_object* v_options_3476_; uint8_t v_hasTrace_3477_; 
v_options_3476_ = lean_ctor_get(v___y_3419_, 2);
v_hasTrace_3477_ = lean_ctor_get_uint8(v_options_3476_, sizeof(void*)*1);
if (v_hasTrace_3477_ == 0)
{
lean_dec(v_hint_3414_);
lean_dec(v_mod_3412_);
v___y_3433_ = v___y_3418_;
v___y_3434_ = v___y_3420_;
goto v___jp_3432_;
}
else
{
lean_object* v_inheritedTraceOptions_3478_; lean_object* v_cls_3479_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___x_3499_; uint8_t v___x_3500_; 
v_inheritedTraceOptions_3478_ = lean_ctor_get(v___y_3419_, 13);
v_cls_3479_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__8));
v___x_3499_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__14, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__14_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__14);
v___x_3500_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3478_, v_options_3476_, v___x_3499_);
if (v___x_3500_ == 0)
{
lean_dec(v_hint_3414_);
lean_dec(v_mod_3412_);
v___y_3433_ = v___y_3418_;
v___y_3434_ = v___y_3420_;
goto v___jp_3432_;
}
else
{
lean_object* v___x_3501_; lean_object* v___y_3503_; 
v___x_3501_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__16, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__16_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__16);
if (v_isExporting_3424_ == 0)
{
lean_object* v___x_3510_; 
v___x_3510_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__19));
v___y_3503_ = v___x_3510_;
goto v___jp_3502_;
}
else
{
lean_object* v___x_3511_; 
v___x_3511_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__20));
v___y_3503_ = v___x_3511_;
goto v___jp_3502_;
}
v___jp_3502_:
{
lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
lean_inc_ref(v___y_3503_);
v___x_3504_ = l_Lean_stringToMessageData(v___y_3503_);
v___x_3505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3501_);
lean_ctor_set(v___x_3505_, 1, v___x_3504_);
v___x_3506_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1);
v___x_3507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3507_, 0, v___x_3505_);
lean_ctor_set(v___x_3507_, 1, v___x_3506_);
if (v_isMeta_3413_ == 0)
{
lean_object* v___x_3508_; 
v___x_3508_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__17));
v___y_3486_ = v___x_3507_;
v___y_3487_ = v___x_3508_;
goto v___jp_3485_;
}
else
{
lean_object* v___x_3509_; 
v___x_3509_ = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__18));
v___y_3486_ = v___x_3507_;
v___y_3487_ = v___x_3509_;
goto v___jp_3485_;
}
}
}
v___jp_3480_:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; 
v___x_3483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___y_3481_);
lean_ctor_set(v___x_3483_, 1, v___y_3482_);
v___x_3484_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg(v_cls_3479_, v___x_3483_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_dec_ref(v___x_3484_);
v___y_3433_ = v___y_3418_;
v___y_3434_ = v___y_3420_;
goto v___jp_3432_;
}
else
{
lean_dec_ref(v_entry_3428_);
return v___x_3484_;
}
}
v___jp_3485_:
{
lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; uint8_t v___x_3494_; 
lean_inc_ref(v___y_3487_);
v___x_3488_ = l_Lean_stringToMessageData(v___y_3487_);
v___x_3489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3489_, 0, v___y_3486_);
lean_ctor_set(v___x_3489_, 1, v___x_3488_);
v___x_3490_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__10);
v___x_3491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3489_);
lean_ctor_set(v___x_3491_, 1, v___x_3490_);
v___x_3492_ = l_Lean_MessageData_ofName(v_mod_3412_);
v___x_3493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3491_);
lean_ctor_set(v___x_3493_, 1, v___x_3492_);
v___x_3494_ = l_Lean_Name_isAnonymous(v_hint_3414_);
if (v___x_3494_ == 0)
{
lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3495_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__12);
v___x_3496_ = l_Lean_MessageData_ofName(v_hint_3414_);
v___x_3497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3495_);
lean_ctor_set(v___x_3497_, 1, v___x_3496_);
v___y_3481_ = v___x_3493_;
v___y_3482_ = v___x_3497_;
goto v___jp_3480_;
}
else
{
lean_object* v___x_3498_; 
lean_dec(v_hint_3414_);
v___x_3498_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__13);
v___y_3481_ = v___x_3493_;
v___y_3482_ = v___x_3498_;
goto v___jp_3480_;
}
}
}
}
else
{
lean_object* v___x_3512_; lean_object* v___x_3513_; 
lean_dec_ref(v_entry_3428_);
lean_dec(v_hint_3414_);
lean_dec(v_mod_3412_);
v___x_3512_ = lean_box(0);
v___x_3513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3512_);
return v___x_3513_;
}
v___jp_3432_:
{
lean_object* v___x_3435_; lean_object* v_toEnvExtension_3436_; lean_object* v_env_3437_; lean_object* v_nextMacroScope_3438_; lean_object* v_ngen_3439_; lean_object* v_auxDeclNGen_3440_; lean_object* v_traceState_3441_; lean_object* v_messages_3442_; lean_object* v_infoState_3443_; lean_object* v_snapshotTasks_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3472_; 
v___x_3435_ = lean_st_ref_take(v___y_3434_);
v_toEnvExtension_3436_ = lean_ctor_get(v___x_3429_, 0);
v_env_3437_ = lean_ctor_get(v___x_3435_, 0);
v_nextMacroScope_3438_ = lean_ctor_get(v___x_3435_, 1);
v_ngen_3439_ = lean_ctor_get(v___x_3435_, 2);
v_auxDeclNGen_3440_ = lean_ctor_get(v___x_3435_, 3);
v_traceState_3441_ = lean_ctor_get(v___x_3435_, 4);
v_messages_3442_ = lean_ctor_get(v___x_3435_, 6);
v_infoState_3443_ = lean_ctor_get(v___x_3435_, 7);
v_snapshotTasks_3444_ = lean_ctor_get(v___x_3435_, 8);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3472_ == 0)
{
lean_object* v_unused_3473_; 
v_unused_3473_ = lean_ctor_get(v___x_3435_, 5);
lean_dec(v_unused_3473_);
v___x_3446_ = v___x_3435_;
v_isShared_3447_ = v_isSharedCheck_3472_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_snapshotTasks_3444_);
lean_inc(v_infoState_3443_);
lean_inc(v_messages_3442_);
lean_inc(v_traceState_3441_);
lean_inc(v_auxDeclNGen_3440_);
lean_inc(v_ngen_3439_);
lean_inc(v_nextMacroScope_3438_);
lean_inc(v_env_3437_);
lean_dec(v___x_3435_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3472_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v_asyncMode_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3452_; 
v_asyncMode_3448_ = lean_ctor_get(v_toEnvExtension_3436_, 2);
v___x_3449_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_3429_, v_env_3437_, v_entry_3428_, v_asyncMode_3448_, v___x_3431_);
v___x_3450_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__5);
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 5, v___x_3450_);
lean_ctor_set(v___x_3446_, 0, v___x_3449_);
v___x_3452_ = v___x_3446_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v___x_3449_);
lean_ctor_set(v_reuseFailAlloc_3471_, 1, v_nextMacroScope_3438_);
lean_ctor_set(v_reuseFailAlloc_3471_, 2, v_ngen_3439_);
lean_ctor_set(v_reuseFailAlloc_3471_, 3, v_auxDeclNGen_3440_);
lean_ctor_set(v_reuseFailAlloc_3471_, 4, v_traceState_3441_);
lean_ctor_set(v_reuseFailAlloc_3471_, 5, v___x_3450_);
lean_ctor_set(v_reuseFailAlloc_3471_, 6, v_messages_3442_);
lean_ctor_set(v_reuseFailAlloc_3471_, 7, v_infoState_3443_);
lean_ctor_set(v_reuseFailAlloc_3471_, 8, v_snapshotTasks_3444_);
v___x_3452_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v_mctx_3455_; lean_object* v_zetaDeltaFVarIds_3456_; lean_object* v_postponed_3457_; lean_object* v_diag_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3469_; 
v___x_3453_ = lean_st_ref_set(v___y_3434_, v___x_3452_);
v___x_3454_ = lean_st_ref_take(v___y_3433_);
v_mctx_3455_ = lean_ctor_get(v___x_3454_, 0);
v_zetaDeltaFVarIds_3456_ = lean_ctor_get(v___x_3454_, 2);
v_postponed_3457_ = lean_ctor_get(v___x_3454_, 3);
v_diag_3458_ = lean_ctor_get(v___x_3454_, 4);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3469_ == 0)
{
lean_object* v_unused_3470_; 
v_unused_3470_ = lean_ctor_get(v___x_3454_, 1);
lean_dec(v_unused_3470_);
v___x_3460_ = v___x_3454_;
v_isShared_3461_ = v_isSharedCheck_3469_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_diag_3458_);
lean_inc(v_postponed_3457_);
lean_inc(v_zetaDeltaFVarIds_3456_);
lean_inc(v_mctx_3455_);
lean_dec(v___x_3454_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3469_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3462_; lean_object* v___x_3464_; 
v___x_3462_ = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___closed__6);
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 1, v___x_3462_);
v___x_3464_ = v___x_3460_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_mctx_3455_);
lean_ctor_set(v_reuseFailAlloc_3468_, 1, v___x_3462_);
lean_ctor_set(v_reuseFailAlloc_3468_, 2, v_zetaDeltaFVarIds_3456_);
lean_ctor_set(v_reuseFailAlloc_3468_, 3, v_postponed_3457_);
lean_ctor_set(v_reuseFailAlloc_3468_, 4, v_diag_3458_);
v___x_3464_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3465_ = lean_st_ref_set(v___y_3433_, v___x_3464_);
v___x_3466_ = lean_box(0);
v___x_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3466_);
return v___x_3467_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0___boxed(lean_object* v_mod_3514_, lean_object* v_isMeta_3515_, lean_object* v_hint_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
uint8_t v_isMeta_boxed_3524_; lean_object* v_res_3525_; 
v_isMeta_boxed_3524_ = lean_unbox(v_isMeta_3515_);
v_res_3525_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0(v_mod_3514_, v_isMeta_boxed_3524_, v_hint_3516_, v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v___y_3518_);
lean_dec_ref(v___y_3517_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__1(lean_object* v___x_3526_, lean_object* v_declName_3527_, lean_object* v_as_3528_, size_t v_sz_3529_, size_t v_i_3530_, lean_object* v_b_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_){
_start:
{
uint8_t v___x_3539_; 
v___x_3539_ = lean_usize_dec_lt(v_i_3530_, v_sz_3529_);
if (v___x_3539_ == 0)
{
lean_object* v___x_3540_; 
lean_dec(v_declName_3527_);
v___x_3540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3540_, 0, v_b_3531_);
return v___x_3540_;
}
else
{
lean_object* v___x_3541_; lean_object* v_modules_3542_; lean_object* v___x_3543_; lean_object* v_a_3544_; lean_object* v___x_3545_; lean_object* v_toImport_3546_; lean_object* v_module_3547_; uint8_t v___x_3548_; lean_object* v___x_3549_; 
v___x_3541_ = l_Lean_Environment_header(v___x_3526_);
v_modules_3542_ = lean_ctor_get(v___x_3541_, 3);
lean_inc_ref(v_modules_3542_);
lean_dec_ref(v___x_3541_);
v___x_3543_ = l_Lean_instInhabitedEffectiveImport_default;
v_a_3544_ = lean_array_uget_borrowed(v_as_3528_, v_i_3530_);
v___x_3545_ = lean_array_get(v___x_3543_, v_modules_3542_, v_a_3544_);
lean_dec_ref(v_modules_3542_);
v_toImport_3546_ = lean_ctor_get(v___x_3545_, 0);
lean_inc_ref(v_toImport_3546_);
lean_dec(v___x_3545_);
v_module_3547_ = lean_ctor_get(v_toImport_3546_, 0);
lean_inc(v_module_3547_);
lean_dec_ref(v_toImport_3546_);
v___x_3548_ = 0;
lean_inc(v_declName_3527_);
v___x_3549_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0(v_module_3547_, v___x_3548_, v_declName_3527_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v___x_3550_; size_t v___x_3551_; size_t v___x_3552_; 
lean_dec_ref(v___x_3549_);
v___x_3550_ = lean_box(0);
v___x_3551_ = ((size_t)1ULL);
v___x_3552_ = lean_usize_add(v_i_3530_, v___x_3551_);
v_i_3530_ = v___x_3552_;
v_b_3531_ = v___x_3550_;
goto _start;
}
else
{
lean_dec(v_declName_3527_);
return v___x_3549_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__1___boxed(lean_object* v___x_3554_, lean_object* v_declName_3555_, lean_object* v_as_3556_, lean_object* v_sz_3557_, lean_object* v_i_3558_, lean_object* v_b_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_){
_start:
{
size_t v_sz_boxed_3567_; size_t v_i_boxed_3568_; lean_object* v_res_3569_; 
v_sz_boxed_3567_ = lean_unbox_usize(v_sz_3557_);
lean_dec(v_sz_3557_);
v_i_boxed_3568_ = lean_unbox_usize(v_i_3558_);
lean_dec(v_i_3558_);
v_res_3569_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__1(v___x_3554_, v_declName_3555_, v_as_3556_, v_sz_boxed_3567_, v_i_boxed_3568_, v_b_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_);
lean_dec(v___y_3565_);
lean_dec_ref(v___y_3564_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec_ref(v_as_3556_);
lean_dec_ref(v___x_3554_);
return v_res_3569_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__5___redArg(lean_object* v_a_3570_, lean_object* v_x_3571_){
_start:
{
if (lean_obj_tag(v_x_3571_) == 0)
{
lean_object* v___x_3572_; 
v___x_3572_ = lean_box(0);
return v___x_3572_;
}
else
{
lean_object* v_key_3573_; lean_object* v_value_3574_; lean_object* v_tail_3575_; uint8_t v___x_3576_; 
v_key_3573_ = lean_ctor_get(v_x_3571_, 0);
v_value_3574_ = lean_ctor_get(v_x_3571_, 1);
v_tail_3575_ = lean_ctor_get(v_x_3571_, 2);
v___x_3576_ = lean_name_eq(v_key_3573_, v_a_3570_);
if (v___x_3576_ == 0)
{
v_x_3571_ = v_tail_3575_;
goto _start;
}
else
{
lean_object* v___x_3578_; 
lean_inc(v_value_3574_);
v___x_3578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3578_, 0, v_value_3574_);
return v___x_3578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_a_3579_, lean_object* v_x_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__5___redArg(v_a_3579_, v_x_3580_);
lean_dec(v_x_3580_);
lean_dec(v_a_3579_);
return v_res_3581_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3582_; uint64_t v___x_3583_; 
v___x_3582_ = lean_unsigned_to_nat(1723u);
v___x_3583_ = lean_uint64_of_nat(v___x_3582_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg(lean_object* v_m_3584_, lean_object* v_a_3585_){
_start:
{
lean_object* v_buckets_3586_; lean_object* v___x_3587_; uint64_t v___y_3589_; 
v_buckets_3586_ = lean_ctor_get(v_m_3584_, 1);
v___x_3587_ = lean_array_get_size(v_buckets_3586_);
if (lean_obj_tag(v_a_3585_) == 0)
{
uint64_t v___x_3603_; 
v___x_3603_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg___closed__0);
v___y_3589_ = v___x_3603_;
goto v___jp_3588_;
}
else
{
uint64_t v_hash_3604_; 
v_hash_3604_ = lean_ctor_get_uint64(v_a_3585_, sizeof(void*)*2);
v___y_3589_ = v_hash_3604_;
goto v___jp_3588_;
}
v___jp_3588_:
{
uint64_t v___x_3590_; uint64_t v___x_3591_; uint64_t v_fold_3592_; uint64_t v___x_3593_; uint64_t v___x_3594_; uint64_t v___x_3595_; size_t v___x_3596_; size_t v___x_3597_; size_t v___x_3598_; size_t v___x_3599_; size_t v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3590_ = 32ULL;
v___x_3591_ = lean_uint64_shift_right(v___y_3589_, v___x_3590_);
v_fold_3592_ = lean_uint64_xor(v___y_3589_, v___x_3591_);
v___x_3593_ = 16ULL;
v___x_3594_ = lean_uint64_shift_right(v_fold_3592_, v___x_3593_);
v___x_3595_ = lean_uint64_xor(v_fold_3592_, v___x_3594_);
v___x_3596_ = lean_uint64_to_usize(v___x_3595_);
v___x_3597_ = lean_usize_of_nat(v___x_3587_);
v___x_3598_ = ((size_t)1ULL);
v___x_3599_ = lean_usize_sub(v___x_3597_, v___x_3598_);
v___x_3600_ = lean_usize_land(v___x_3596_, v___x_3599_);
v___x_3601_ = lean_array_uget_borrowed(v_buckets_3586_, v___x_3600_);
v___x_3602_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__5___redArg(v_a_3585_, v___x_3601_);
return v___x_3602_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg___boxed(lean_object* v_m_3605_, lean_object* v_a_3606_){
_start:
{
lean_object* v_res_3607_; 
v_res_3607_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg(v_m_3605_, v_a_3606_);
lean_dec(v_a_3606_);
lean_dec_ref(v_m_3605_);
return v_res_3607_;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__2(void){
_start:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3610_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__1));
v___x_3611_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__0));
v___x_3612_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_3611_, v___x_3610_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0(lean_object* v_declName_3615_, uint8_t v_isMeta_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v___x_3624_; lean_object* v_env_3628_; lean_object* v___y_3630_; lean_object* v___x_3643_; 
v___x_3624_ = lean_st_ref_get(v___y_3622_);
v_env_3628_ = lean_ctor_get(v___x_3624_, 0);
lean_inc_ref(v_env_3628_);
lean_dec(v___x_3624_);
v___x_3643_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_3628_, v_declName_3615_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_dec_ref(v_env_3628_);
lean_dec(v_declName_3615_);
goto v___jp_3625_;
}
else
{
lean_object* v_val_3644_; lean_object* v___x_3645_; lean_object* v_modules_3646_; lean_object* v___x_3647_; uint8_t v___x_3648_; 
v_val_3644_ = lean_ctor_get(v___x_3643_, 0);
lean_inc(v_val_3644_);
lean_dec_ref(v___x_3643_);
v___x_3645_ = l_Lean_Environment_header(v_env_3628_);
v_modules_3646_ = lean_ctor_get(v___x_3645_, 3);
lean_inc_ref(v_modules_3646_);
lean_dec_ref(v___x_3645_);
v___x_3647_ = lean_array_get_size(v_modules_3646_);
v___x_3648_ = lean_nat_dec_lt(v_val_3644_, v___x_3647_);
if (v___x_3648_ == 0)
{
lean_dec_ref(v_modules_3646_);
lean_dec(v_val_3644_);
lean_dec_ref(v_env_3628_);
lean_dec(v_declName_3615_);
goto v___jp_3625_;
}
else
{
lean_object* v___x_3649_; lean_object* v_env_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; uint8_t v___y_3654_; 
v___x_3649_ = lean_st_ref_get(v___y_3622_);
v_env_3650_ = lean_ctor_get(v___x_3649_, 0);
lean_inc_ref(v_env_3650_);
lean_dec(v___x_3649_);
v___x_3651_ = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__2);
v___x_3652_ = lean_array_fget(v_modules_3646_, v_val_3644_);
lean_dec(v_val_3644_);
lean_dec_ref(v_modules_3646_);
if (v_isMeta_3616_ == 0)
{
lean_dec_ref(v_env_3650_);
v___y_3654_ = v_isMeta_3616_;
goto v___jp_3653_;
}
else
{
uint8_t v___x_3665_; 
lean_inc(v_declName_3615_);
v___x_3665_ = l_Lean_isMarkedMeta(v_env_3650_, v_declName_3615_);
if (v___x_3665_ == 0)
{
v___y_3654_ = v_isMeta_3616_;
goto v___jp_3653_;
}
else
{
uint8_t v___x_3666_; 
v___x_3666_ = 0;
v___y_3654_ = v___x_3666_;
goto v___jp_3653_;
}
}
v___jp_3653_:
{
lean_object* v_toImport_3655_; lean_object* v_module_3656_; lean_object* v___x_3657_; 
v_toImport_3655_ = lean_ctor_get(v___x_3652_, 0);
lean_inc_ref(v_toImport_3655_);
lean_dec(v___x_3652_);
v_module_3656_ = lean_ctor_get(v_toImport_3655_, 0);
lean_inc(v_module_3656_);
lean_dec_ref(v_toImport_3655_);
lean_inc(v_declName_3615_);
v___x_3657_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0(v_module_3656_, v___y_3654_, v_declName_3615_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; 
lean_dec_ref(v___x_3657_);
v___x_3658_ = l_Lean_indirectModUseExt;
v___x_3659_ = lean_box(1);
v___x_3660_ = lean_box(0);
lean_inc_ref(v_env_3628_);
v___x_3661_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_3651_, v___x_3658_, v_env_3628_, v___x_3659_, v___x_3660_);
v___x_3662_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg(v___x_3661_, v_declName_3615_);
lean_dec(v___x_3661_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v___x_3663_; 
v___x_3663_ = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___closed__3));
v___y_3630_ = v___x_3663_;
goto v___jp_3629_;
}
else
{
lean_object* v_val_3664_; 
v_val_3664_ = lean_ctor_get(v___x_3662_, 0);
lean_inc(v_val_3664_);
lean_dec_ref(v___x_3662_);
v___y_3630_ = v_val_3664_;
goto v___jp_3629_;
}
}
else
{
lean_dec_ref(v_env_3628_);
lean_dec(v_declName_3615_);
return v___x_3657_;
}
}
}
}
v___jp_3625_:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3626_ = lean_box(0);
v___x_3627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3626_);
return v___x_3627_;
}
v___jp_3629_:
{
lean_object* v___x_3631_; size_t v_sz_3632_; size_t v___x_3633_; lean_object* v___x_3634_; 
v___x_3631_ = lean_box(0);
v_sz_3632_ = lean_array_size(v___y_3630_);
v___x_3633_ = ((size_t)0ULL);
v___x_3634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__1(v_env_3628_, v_declName_3615_, v___y_3630_, v_sz_3632_, v___x_3633_, v___x_3631_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
lean_dec_ref(v___y_3630_);
lean_dec_ref(v_env_3628_);
if (lean_obj_tag(v___x_3634_) == 0)
{
lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3641_; 
v_isSharedCheck_3641_ = !lean_is_exclusive(v___x_3634_);
if (v_isSharedCheck_3641_ == 0)
{
lean_object* v_unused_3642_; 
v_unused_3642_ = lean_ctor_get(v___x_3634_, 0);
lean_dec(v_unused_3642_);
v___x_3636_ = v___x_3634_;
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
else
{
lean_dec(v___x_3634_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3641_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3639_; 
if (v_isShared_3637_ == 0)
{
lean_ctor_set(v___x_3636_, 0, v___x_3631_);
v___x_3639_ = v___x_3636_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v___x_3631_);
v___x_3639_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
return v___x_3639_;
}
}
}
else
{
return v___x_3634_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0___boxed(lean_object* v_declName_3667_, lean_object* v_isMeta_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_){
_start:
{
uint8_t v_isMeta_boxed_3676_; lean_object* v_res_3677_; 
v_isMeta_boxed_3676_ = lean_unbox(v_isMeta_3668_);
v_res_3677_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0(v_declName_3667_, v_isMeta_boxed_3676_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_, v___y_3673_, v___y_3674_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec_ref(v___y_3671_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
return v_res_3677_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__1(void){
_start:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3679_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__0));
v___x_3680_ = l_Lean_stringToMessageData(v___x_3679_);
return v___x_3680_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__3(void){
_start:
{
lean_object* v___x_3682_; lean_object* v___x_3683_; 
v___x_3682_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__2));
v___x_3683_ = l_Lean_stringToMessageData(v___x_3682_);
return v___x_3683_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__5(void){
_start:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; 
v___x_3685_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__4));
v___x_3686_ = l_Lean_stringToMessageData(v___x_3685_);
return v___x_3686_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__7(void){
_start:
{
lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3688_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__6));
v___x_3689_ = l_Lean_stringToMessageData(v___x_3688_);
return v___x_3689_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__8(void){
_start:
{
lean_object* v___x_3690_; lean_object* v___x_3691_; 
v___x_3690_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_));
v___x_3691_ = l_Lean_MessageData_ofName(v___x_3690_);
return v___x_3691_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__9(void){
_start:
{
lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v___x_3692_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__8, &l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__8);
v___x_3693_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__7, &l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__7_once, _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__7);
v___x_3694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3693_);
lean_ctor_set(v___x_3694_, 1, v___x_3692_);
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg(lean_object* v_optConfig_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_){
_start:
{
lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v___y_3716_; lean_object* v___y_3717_; lean_object* v___y_3718_; lean_object* v___y_3719_; lean_object* v___y_3720_; uint8_t v___y_3721_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___y_3738_; uint8_t v_recover_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; uint8_t v___x_3748_; uint8_t v___x_3749_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v___y_3756_; 
v_recover_3743_ = lean_ctor_get_uint8(v_a_3703_, sizeof(void*)*1);
lean_inc(v_optConfig_3702_);
v___x_3744_ = l_Lean_Parser_Tactic_getConfigItems(v_optConfig_3702_);
v___x_3745_ = l_Lean_Elab_Tactic_mkConfigItemViews(v___x_3744_);
v___x_3746_ = lean_array_get_size(v___x_3745_);
v___x_3747_ = lean_unsigned_to_nat(0u);
v___x_3748_ = lean_nat_dec_eq(v___x_3746_, v___x_3747_);
v___x_3749_ = 1;
if (v___x_3748_ == 0)
{
lean_object* v___x_3801_; lean_object* v_fileName_3802_; lean_object* v_fileMap_3803_; lean_object* v_options_3804_; lean_object* v_currRecDepth_3805_; lean_object* v_maxRecDepth_3806_; lean_object* v_ref_3807_; lean_object* v_currNamespace_3808_; lean_object* v_openDecls_3809_; lean_object* v_initHeartbeats_3810_; lean_object* v_maxHeartbeats_3811_; lean_object* v_quotContext_3812_; lean_object* v_currMacroScope_3813_; uint8_t v_diag_3814_; lean_object* v_cancelTk_x3f_3815_; uint8_t v_suppressElabErrors_3816_; lean_object* v_inheritedTraceOptions_3817_; lean_object* v_env_3818_; lean_object* v_ref_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; uint8_t v___x_3822_; 
v___x_3801_ = lean_st_ref_get(v_a_3709_);
v_fileName_3802_ = lean_ctor_get(v_a_3708_, 0);
v_fileMap_3803_ = lean_ctor_get(v_a_3708_, 1);
v_options_3804_ = lean_ctor_get(v_a_3708_, 2);
v_currRecDepth_3805_ = lean_ctor_get(v_a_3708_, 3);
v_maxRecDepth_3806_ = lean_ctor_get(v_a_3708_, 4);
v_ref_3807_ = lean_ctor_get(v_a_3708_, 5);
v_currNamespace_3808_ = lean_ctor_get(v_a_3708_, 6);
v_openDecls_3809_ = lean_ctor_get(v_a_3708_, 7);
v_initHeartbeats_3810_ = lean_ctor_get(v_a_3708_, 8);
v_maxHeartbeats_3811_ = lean_ctor_get(v_a_3708_, 9);
v_quotContext_3812_ = lean_ctor_get(v_a_3708_, 10);
v_currMacroScope_3813_ = lean_ctor_get(v_a_3708_, 11);
v_diag_3814_ = lean_ctor_get_uint8(v_a_3708_, sizeof(void*)*14);
v_cancelTk_x3f_3815_ = lean_ctor_get(v_a_3708_, 12);
v_suppressElabErrors_3816_ = lean_ctor_get_uint8(v_a_3708_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3817_ = lean_ctor_get(v_a_3708_, 13);
v_env_3818_ = lean_ctor_get(v___x_3801_, 0);
lean_inc_ref(v_env_3818_);
lean_dec(v___x_3801_);
v_ref_3819_ = l_Lean_replaceRef(v_optConfig_3702_, v_ref_3807_);
lean_dec(v_optConfig_3702_);
lean_inc_ref(v_inheritedTraceOptions_3817_);
lean_inc(v_cancelTk_x3f_3815_);
lean_inc(v_currMacroScope_3813_);
lean_inc(v_quotContext_3812_);
lean_inc(v_maxHeartbeats_3811_);
lean_inc(v_initHeartbeats_3810_);
lean_inc(v_openDecls_3809_);
lean_inc(v_currNamespace_3808_);
lean_inc(v_maxRecDepth_3806_);
lean_inc(v_currRecDepth_3805_);
lean_inc_ref(v_options_3804_);
lean_inc_ref(v_fileMap_3803_);
lean_inc_ref(v_fileName_3802_);
v___x_3820_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3820_, 0, v_fileName_3802_);
lean_ctor_set(v___x_3820_, 1, v_fileMap_3803_);
lean_ctor_set(v___x_3820_, 2, v_options_3804_);
lean_ctor_set(v___x_3820_, 3, v_currRecDepth_3805_);
lean_ctor_set(v___x_3820_, 4, v_maxRecDepth_3806_);
lean_ctor_set(v___x_3820_, 5, v_ref_3819_);
lean_ctor_set(v___x_3820_, 6, v_currNamespace_3808_);
lean_ctor_set(v___x_3820_, 7, v_openDecls_3809_);
lean_ctor_set(v___x_3820_, 8, v_initHeartbeats_3810_);
lean_ctor_set(v___x_3820_, 9, v_maxHeartbeats_3811_);
lean_ctor_set(v___x_3820_, 10, v_quotContext_3812_);
lean_ctor_set(v___x_3820_, 11, v_currMacroScope_3813_);
lean_ctor_set(v___x_3820_, 12, v_cancelTk_x3f_3815_);
lean_ctor_set(v___x_3820_, 13, v_inheritedTraceOptions_3817_);
lean_ctor_set_uint8(v___x_3820_, sizeof(void*)*14, v_diag_3814_);
lean_ctor_set_uint8(v___x_3820_, sizeof(void*)*14 + 1, v_suppressElabErrors_3816_);
v___x_3821_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_));
v___x_3822_ = l_Lean_Environment_contains(v_env_3818_, v___x_3821_, v___x_3749_);
if (v___x_3822_ == 0)
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
lean_dec_ref(v___x_3745_);
v___x_3823_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__9, &l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__9_once, _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__9);
v___x_3824_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg(v___x_3823_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v___x_3820_, v_a_3709_);
lean_dec_ref(v___x_3820_);
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3824_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3824_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
else
{
v___y_3751_ = v_a_3704_;
v___y_3752_ = v_a_3705_;
v___y_3753_ = v_a_3706_;
v___y_3754_ = v_a_3707_;
v___y_3755_ = v___x_3820_;
v___y_3756_ = v_a_3709_;
goto v___jp_3750_;
}
}
else
{
lean_object* v___x_3833_; lean_object* v___x_3834_; 
lean_dec_ref(v___x_3745_);
lean_dec(v_optConfig_3702_);
v___x_3833_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__10));
v___x_3834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3833_);
return v___x_3834_;
}
v___jp_3711_:
{
if (v___y_3721_ == 0)
{
lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
lean_dec_ref(v___y_3712_);
v___x_3722_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__1, &l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__1);
v___x_3723_ = l_Lean_MessageData_ofExpr(v___y_3713_);
v___x_3724_ = l_Lean_indentD(v___x_3723_);
v___x_3725_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3722_);
lean_ctor_set(v___x_3725_, 1, v___x_3724_);
v___x_3726_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__3, &l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__3_once, _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__3);
v___x_3727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3725_);
lean_ctor_set(v___x_3727_, 1, v___x_3726_);
v___x_3728_ = l_Lean_Exception_toMessageData(v___y_3720_);
v___x_3729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3727_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
v___x_3730_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg(v___x_3729_, v___y_3717_, v___y_3719_, v___y_3716_, v___y_3715_, v___y_3714_, v___y_3718_);
lean_dec_ref(v___y_3714_);
return v___x_3730_;
}
else
{
lean_dec_ref(v___y_3720_);
lean_dec_ref(v___y_3714_);
lean_dec_ref(v___y_3713_);
return v___y_3712_;
}
}
v___jp_3731_:
{
lean_object* v___x_3739_; 
lean_inc_ref(v___y_3732_);
v___x_3739_ = l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_(v___y_3732_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_dec_ref(v___y_3737_);
lean_dec_ref(v___y_3732_);
return v___x_3739_;
}
else
{
lean_object* v_a_3740_; uint8_t v___x_3741_; 
v_a_3740_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_a_3740_);
v___x_3741_ = l_Lean_Exception_isInterrupt(v_a_3740_);
if (v___x_3741_ == 0)
{
uint8_t v___x_3742_; 
lean_inc(v_a_3740_);
v___x_3742_ = l_Lean_Exception_isRuntime(v_a_3740_);
v___y_3712_ = v___x_3739_;
v___y_3713_ = v___y_3732_;
v___y_3714_ = v___y_3737_;
v___y_3715_ = v___y_3736_;
v___y_3716_ = v___y_3735_;
v___y_3717_ = v___y_3733_;
v___y_3718_ = v___y_3738_;
v___y_3719_ = v___y_3734_;
v___y_3720_ = v_a_3740_;
v___y_3721_ = v___x_3742_;
goto v___jp_3711_;
}
else
{
v___y_3712_ = v___x_3739_;
v___y_3713_ = v___y_3732_;
v___y_3714_ = v___y_3737_;
v___y_3715_ = v___y_3736_;
v___y_3716_ = v___y_3735_;
v___y_3717_ = v___y_3733_;
v___y_3718_ = v___y_3738_;
v___y_3719_ = v___y_3734_;
v___y_3720_ = v_a_3740_;
v___y_3721_ = v___x_3741_;
goto v___jp_3711_;
}
}
}
v___jp_3750_:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3757_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalUnsafe___redArg___closed__3_00___x40_Lean_Elab_Tactic_NormCast_121220554____hygCtx___hyg_3_));
v___x_3758_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0(v___x_3757_, v___x_3749_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
if (lean_obj_tag(v___x_3758_) == 0)
{
lean_object* v___x_3759_; 
lean_dec_ref(v___x_3758_);
v___x_3759_ = l_Lean_Elab_Tactic_elabConfig(v_recover_3743_, v___x_3757_, v___x_3745_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
if (lean_obj_tag(v___x_3759_) == 0)
{
lean_object* v_a_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3784_; 
v_a_3760_ = lean_ctor_get(v___x_3759_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3762_ = v___x_3759_;
v_isShared_3763_ = v_isSharedCheck_3784_;
goto v_resetjp_3761_;
}
else
{
lean_inc(v_a_3760_);
lean_dec(v___x_3759_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3784_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
uint8_t v___x_3764_; 
v___x_3764_ = l_Lean_Expr_hasSyntheticSorry(v_a_3760_);
if (v___x_3764_ == 0)
{
uint8_t v___x_3765_; 
lean_del_object(v___x_3762_);
v___x_3765_ = l_Lean_Expr_hasSorry(v_a_3760_);
if (v___x_3765_ == 0)
{
v___y_3732_ = v_a_3760_;
v___y_3733_ = v___y_3751_;
v___y_3734_ = v___y_3752_;
v___y_3735_ = v___y_3753_;
v___y_3736_ = v___y_3754_;
v___y_3737_ = v___y_3755_;
v___y_3738_ = v___y_3756_;
goto v___jp_3731_;
}
else
{
lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
lean_dec(v_a_3760_);
v___x_3766_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__5, &l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__5);
v___x_3767_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg(v___x_3766_, v___y_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
lean_dec_ref(v___y_3755_);
v_a_3768_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3770_ = v___x_3767_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___x_3767_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3768_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
else
{
lean_object* v___x_3776_; lean_object* v___x_3777_; uint8_t v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3782_; 
lean_dec(v_a_3760_);
lean_dec_ref(v___y_3755_);
v___x_3776_ = lean_unsigned_to_nat(100000u);
v___x_3777_ = lean_unsigned_to_nat(2u);
v___x_3778_ = 0;
v___x_3779_ = lean_box(0);
v___x_3780_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_3780_, 0, v___x_3776_);
lean_ctor_set(v___x_3780_, 1, v___x_3777_);
lean_ctor_set(v___x_3780_, 2, v___x_3779_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3, v___x_3748_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 1, v___x_3749_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 2, v___x_3748_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 3, v___x_3748_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 4, v___x_3748_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 5, v___x_3748_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 6, v___x_3778_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 7, v___x_3748_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 8, v___x_3748_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 9, v___x_3748_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 10, v___x_3748_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 11, v___x_3748_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 12, v___x_3749_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 13, v___x_3749_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 14, v___x_3748_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 15, v___x_3748_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 16, v___x_3748_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 17, v___x_3749_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 18, v___x_3749_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 19, v___x_3749_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 20, v___x_3749_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 21, v___x_3749_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 22, v___x_3749_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 23, v___x_3749_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 24, v___x_3749_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 25, v___x_3749_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 26, v___x_3748_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 27, v___x_3748_);
lean_ctor_set_uint8(v___x_3780_, sizeof(void*)*3 + 28, v___x_3748_);
if (v_isShared_3763_ == 0)
{
lean_ctor_set(v___x_3762_, 0, v___x_3780_);
v___x_3782_ = v___x_3762_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v___x_3780_);
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
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3792_; 
lean_dec_ref(v___y_3755_);
v_a_3785_ = lean_ctor_get(v___x_3759_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3759_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3787_ = v___x_3759_;
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3759_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3790_; 
if (v_isShared_3788_ == 0)
{
v___x_3790_ = v___x_3787_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_a_3785_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
}
else
{
lean_object* v_a_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3800_; 
lean_dec_ref(v___y_3755_);
lean_dec_ref(v___x_3745_);
v_a_3793_ = lean_ctor_get(v___x_3758_, 0);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3795_ = v___x_3758_;
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_a_3793_);
lean_dec(v___x_3758_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3798_; 
if (v_isShared_3796_ == 0)
{
v___x_3798_ = v___x_3795_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_a_3793_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___boxed(lean_object* v_optConfig_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_){
_start:
{
lean_object* v_res_3844_; 
v_res_3844_ = l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg(v_optConfig_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_);
lean_dec(v_a_3842_);
lean_dec_ref(v_a_3841_);
lean_dec(v_a_3840_);
lean_dec_ref(v_a_3839_);
lean_dec(v_a_3838_);
lean_dec_ref(v_a_3837_);
lean_dec_ref(v_a_3836_);
return v_res_3844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig(lean_object* v_optConfig_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_){
_start:
{
lean_object* v___x_3855_; 
v___x_3855_ = l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg(v_optConfig_3845_, v_a_3846_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_);
return v___x_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___boxed(lean_object* v_optConfig_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_){
_start:
{
lean_object* v_res_3866_; 
v_res_3866_ = l_Lean_Elab_Tactic_NormCast_elabNormCastConfig(v_optConfig_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_);
lean_dec(v_a_3864_);
lean_dec_ref(v_a_3863_);
lean_dec(v_a_3862_);
lean_dec_ref(v_a_3861_);
lean_dec(v_a_3860_);
lean_dec_ref(v_a_3859_);
lean_dec(v_a_3858_);
lean_dec_ref(v_a_3857_);
return v_res_3866_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1(lean_object* v_00_u03b1_3867_, lean_object* v_msg_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
lean_object* v___x_3876_; 
v___x_3876_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___redArg(v_msg_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_);
return v___x_3876_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1___boxed(lean_object* v_00_u03b1_3877_, lean_object* v_msg_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_){
_start:
{
lean_object* v_res_3886_; 
v_res_3886_ = l_Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1(v_00_u03b1_3877_, v_msg_3878_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_);
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
lean_dec(v___y_3882_);
lean_dec_ref(v___y_3881_);
lean_dec(v___y_3880_);
lean_dec_ref(v___y_3879_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2(lean_object* v_00_u03b2_3887_, lean_object* v_m_3888_, lean_object* v_a_3889_){
_start:
{
lean_object* v___x_3890_; 
v___x_3890_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___redArg(v_m_3888_, v_a_3889_);
return v___x_3890_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2___boxed(lean_object* v_00_u03b2_3891_, lean_object* v_m_3892_, lean_object* v_a_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2(v_00_u03b2_3891_, v_m_3892_, v_a_3893_);
lean_dec(v_a_3893_);
lean_dec_ref(v_m_3892_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4(lean_object* v_msgData_3895_, lean_object* v_macroStack_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_){
_start:
{
lean_object* v___x_3904_; 
v___x_3904_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___redArg(v_msgData_3895_, v_macroStack_3896_, v___y_3901_);
return v___x_3904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4___boxed(lean_object* v_msgData_3905_, lean_object* v_macroStack_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_){
_start:
{
lean_object* v_res_3914_; 
v_res_3914_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__1_spec__4(v_msgData_3905_, v_macroStack_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_);
lean_dec(v___y_3912_);
lean_dec_ref(v___y_3911_);
lean_dec(v___y_3910_);
lean_dec_ref(v___y_3909_);
lean_dec(v___y_3908_);
lean_dec_ref(v___y_3907_);
return v_res_3914_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_3915_, lean_object* v_x_3916_, lean_object* v_x_3917_){
_start:
{
uint8_t v___x_3918_; 
v___x_3918_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___redArg(v_x_3916_, v_x_3917_);
return v___x_3918_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_3919_, lean_object* v_x_3920_, lean_object* v_x_3921_){
_start:
{
uint8_t v_res_3922_; lean_object* v_r_3923_; 
v_res_3922_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1(v_00_u03b2_3919_, v_x_3920_, v_x_3921_);
lean_dec_ref(v_x_3921_);
lean_dec_ref(v_x_3920_);
v_r_3923_ = lean_box(v_res_3922_);
return v_r_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2(lean_object* v_cls_3924_, lean_object* v_msg_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_){
_start:
{
lean_object* v___x_3933_; 
v___x_3933_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___redArg(v_cls_3924_, v_msg_3925_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
return v___x_3933_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2___boxed(lean_object* v_cls_3934_, lean_object* v_msg_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
lean_object* v_res_3943_; 
v_res_3943_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__2(v_cls_3934_, v_msg_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
lean_dec(v___y_3937_);
lean_dec_ref(v___y_3936_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_3944_, lean_object* v_a_3945_, lean_object* v_x_3946_){
_start:
{
lean_object* v___x_3947_; 
v___x_3947_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__5___redArg(v_a_3945_, v_x_3946_);
return v___x_3947_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_3948_, lean_object* v_a_3949_, lean_object* v_x_3950_){
_start:
{
lean_object* v_res_3951_; 
v_res_3951_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__2_spec__5(v_00_u03b2_3948_, v_a_3949_, v_x_3950_);
lean_dec(v_x_3950_);
lean_dec(v_a_3949_);
return v_res_3951_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_3952_, lean_object* v_x_3953_, size_t v_x_3954_, lean_object* v_x_3955_){
_start:
{
uint8_t v___x_3956_; 
v___x_3956_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___redArg(v_x_3953_, v_x_3954_, v_x_3955_);
return v___x_3956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_3957_, lean_object* v_x_3958_, lean_object* v_x_3959_, lean_object* v_x_3960_){
_start:
{
size_t v_x_13112__boxed_3961_; uint8_t v_res_3962_; lean_object* v_r_3963_; 
v_x_13112__boxed_3961_ = lean_unbox_usize(v_x_3959_);
lean_dec(v_x_3959_);
v_res_3962_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_3957_, v_x_3958_, v_x_13112__boxed_3961_, v_x_3960_);
lean_dec_ref(v_x_3960_);
lean_dec_ref(v_x_3958_);
v_r_3963_ = lean_box(v_res_3962_);
return v_r_3963_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__7(lean_object* v_00_u03b2_3964_, lean_object* v_keys_3965_, lean_object* v_vals_3966_, lean_object* v_heq_3967_, lean_object* v_i_3968_, lean_object* v_k_3969_){
_start:
{
uint8_t v___x_3970_; 
v___x_3970_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_keys_3965_, v_i_3968_, v_k_3969_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(lean_object* v_00_u03b2_3971_, lean_object* v_keys_3972_, lean_object* v_vals_3973_, lean_object* v_heq_3974_, lean_object* v_i_3975_, lean_object* v_k_3976_){
_start:
{
uint8_t v_res_3977_; lean_object* v_r_3978_; 
v_res_3977_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Tactic_NormCast_elabNormCastConfig_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b2_3971_, v_keys_3972_, v_vals_3973_, v_heq_3974_, v_i_3975_, v_k_3976_);
lean_dec_ref(v_k_3976_);
lean_dec_ref(v_vals_3973_);
lean_dec_ref(v_keys_3972_);
v_r_3978_ = lean_box(v_res_3977_);
return v_r_3978_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(lean_object* v_e_3979_, lean_object* v___y_3980_){
_start:
{
uint8_t v___x_3982_; 
v___x_3982_ = l_Lean_Expr_hasMVar(v_e_3979_);
if (v___x_3982_ == 0)
{
lean_object* v___x_3983_; 
v___x_3983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3983_, 0, v_e_3979_);
return v___x_3983_;
}
else
{
lean_object* v___x_3984_; lean_object* v_mctx_3985_; lean_object* v___x_3986_; lean_object* v_fst_3987_; lean_object* v_snd_3988_; lean_object* v___x_3989_; lean_object* v_cache_3990_; lean_object* v_zetaDeltaFVarIds_3991_; lean_object* v_postponed_3992_; lean_object* v_diag_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4002_; 
v___x_3984_ = lean_st_ref_get(v___y_3980_);
v_mctx_3985_ = lean_ctor_get(v___x_3984_, 0);
lean_inc_ref(v_mctx_3985_);
lean_dec(v___x_3984_);
v___x_3986_ = l_Lean_instantiateMVarsCore(v_mctx_3985_, v_e_3979_);
v_fst_3987_ = lean_ctor_get(v___x_3986_, 0);
lean_inc(v_fst_3987_);
v_snd_3988_ = lean_ctor_get(v___x_3986_, 1);
lean_inc(v_snd_3988_);
lean_dec_ref(v___x_3986_);
v___x_3989_ = lean_st_ref_take(v___y_3980_);
v_cache_3990_ = lean_ctor_get(v___x_3989_, 1);
v_zetaDeltaFVarIds_3991_ = lean_ctor_get(v___x_3989_, 2);
v_postponed_3992_ = lean_ctor_get(v___x_3989_, 3);
v_diag_3993_ = lean_ctor_get(v___x_3989_, 4);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3989_);
if (v_isSharedCheck_4002_ == 0)
{
lean_object* v_unused_4003_; 
v_unused_4003_ = lean_ctor_get(v___x_3989_, 0);
lean_dec(v_unused_4003_);
v___x_3995_ = v___x_3989_;
v_isShared_3996_ = v_isSharedCheck_4002_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_diag_3993_);
lean_inc(v_postponed_3992_);
lean_inc(v_zetaDeltaFVarIds_3991_);
lean_inc(v_cache_3990_);
lean_dec(v___x_3989_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4002_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
lean_ctor_set(v___x_3995_, 0, v_snd_3988_);
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_snd_3988_);
lean_ctor_set(v_reuseFailAlloc_4001_, 1, v_cache_3990_);
lean_ctor_set(v_reuseFailAlloc_4001_, 2, v_zetaDeltaFVarIds_3991_);
lean_ctor_set(v_reuseFailAlloc_4001_, 3, v_postponed_3992_);
lean_ctor_set(v_reuseFailAlloc_4001_, 4, v_diag_3993_);
v___x_3998_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3999_ = lean_st_ref_set(v___y_3980_, v___x_3998_);
v___x_4000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4000_, 0, v_fst_3987_);
return v___x_4000_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg___boxed(lean_object* v_e_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_){
_start:
{
lean_object* v_res_4007_; 
v_res_4007_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_e_4004_, v___y_4005_);
lean_dec(v___y_4005_);
return v_res_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0(lean_object* v_e_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
lean_object* v___x_4014_; 
v___x_4014_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_e_4008_, v___y_4010_);
return v___x_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___boxed(lean_object* v_e_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v_res_4021_; 
v_res_4021_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0(v_e_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
return v_res_4021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__0(lean_object* v_x_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_){
_start:
{
lean_object* v___x_4033_; lean_object* v___x_4034_; 
v___x_4033_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___lam__0___closed__0));
v___x_4034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4034_, 0, v___x_4033_);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__0___boxed(lean_object* v_x_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l_Lean_Elab_Tactic_NormCast_derive___lam__0(v_x_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec_ref(v_x_4035_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__1(lean_object* v_e_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_){
_start:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4054_, 0, v_e_4045_);
v___x_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4054_);
return v___x_4055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__1___boxed(lean_object* v_e_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_){
_start:
{
lean_object* v_res_4065_; 
v_res_4065_ = l_Lean_Elab_Tactic_NormCast_derive___lam__1(v_e_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_);
lean_dec(v___y_4063_);
lean_dec_ref(v___y_4062_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
lean_dec(v___y_4059_);
lean_dec_ref(v___y_4058_);
lean_dec(v___y_4057_);
return v_res_4065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__2(lean_object* v___x_4066_, lean_object* v_x_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_){
_start:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4076_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4066_);
v___x_4077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4076_);
return v___x_4077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__2___boxed(lean_object* v___x_4078_, lean_object* v_x_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_){
_start:
{
lean_object* v_res_4088_; 
v_res_4088_ = l_Lean_Elab_Tactic_NormCast_derive___lam__2(v___x_4078_, v_x_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_);
lean_dec(v___y_4086_);
lean_dec_ref(v___y_4085_);
lean_dec(v___y_4084_);
lean_dec_ref(v___y_4083_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
lean_dec(v___y_4080_);
lean_dec_ref(v_x_4079_);
return v_res_4088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__3(lean_object* v___x_4089_, lean_object* v_x_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_){
_start:
{
lean_object* v___x_4099_; 
v___x_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4099_, 0, v___x_4089_);
return v___x_4099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__3___boxed(lean_object* v___x_4100_, lean_object* v_x_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l_Lean_Elab_Tactic_NormCast_derive___lam__3(v___x_4100_, v_x_4101_, v___y_4102_, v___y_4103_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
lean_dec(v___y_4108_);
lean_dec_ref(v___y_4107_);
lean_dec(v___y_4106_);
lean_dec_ref(v___y_4105_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec(v___y_4102_);
lean_dec_ref(v_x_4101_);
return v_res_4110_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__0(void){
_start:
{
lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4111_ = l_Lean_bombEmoji;
v___x_4112_ = l_Lean_stringToMessageData(v___x_4111_);
return v___x_4112_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__1(void){
_start:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___x_4113_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__2___closed__1);
v___x_4114_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__0, &l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__0_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__0);
v___x_4115_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4114_);
lean_ctor_set(v___x_4115_, 1, v___x_4113_);
return v___x_4115_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__3(void){
_start:
{
lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___x_4117_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__2));
v___x_4118_ = l_Lean_stringToMessageData(v___x_4117_);
return v___x_4118_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__5(void){
_start:
{
lean_object* v___x_4120_; lean_object* v___x_4121_; 
v___x_4120_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__4));
v___x_4121_ = l_Lean_stringToMessageData(v___x_4120_);
return v___x_4121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__4(lean_object* v_phase_4122_, lean_object* v_x_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_){
_start:
{
if (lean_obj_tag(v_x_4123_) == 0)
{
lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4138_; 
v_isSharedCheck_4138_ = !lean_is_exclusive(v_x_4123_);
if (v_isSharedCheck_4138_ == 0)
{
lean_object* v_unused_4139_; 
v_unused_4139_ = lean_ctor_get(v_x_4123_, 0);
lean_dec(v_unused_4139_);
v___x_4130_ = v_x_4123_;
v_isShared_4131_ = v_isSharedCheck_4138_;
goto v_resetjp_4129_;
}
else
{
lean_dec(v_x_4123_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4138_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4136_; 
v___x_4132_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__1, &l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__1);
v___x_4133_ = l_Lean_stringToMessageData(v_phase_4122_);
v___x_4134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4134_, 0, v___x_4132_);
lean_ctor_set(v___x_4134_, 1, v___x_4133_);
if (v_isShared_4131_ == 0)
{
lean_ctor_set(v___x_4130_, 0, v___x_4134_);
v___x_4136_ = v___x_4130_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v___x_4134_);
v___x_4136_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
return v___x_4136_;
}
}
}
else
{
lean_object* v_a_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4155_; 
v_a_4140_ = lean_ctor_get(v_x_4123_, 0);
v_isSharedCheck_4155_ = !lean_is_exclusive(v_x_4123_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4142_ = v_x_4123_;
v_isShared_4143_ = v_isSharedCheck_4155_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_a_4140_);
lean_dec(v_x_4123_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4155_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v_expr_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4153_; 
v_expr_4144_ = lean_ctor_get(v_a_4140_, 0);
lean_inc_ref(v_expr_4144_);
lean_dec(v_a_4140_);
v___x_4145_ = l_Lean_MessageData_ofExpr(v_expr_4144_);
v___x_4146_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__3, &l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__3_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__3);
v___x_4147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4147_, 0, v___x_4145_);
lean_ctor_set(v___x_4147_, 1, v___x_4146_);
v___x_4148_ = l_Lean_stringToMessageData(v_phase_4122_);
v___x_4149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4149_, 0, v___x_4147_);
lean_ctor_set(v___x_4149_, 1, v___x_4148_);
v___x_4150_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__5, &l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__4___closed__5);
v___x_4151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4149_);
lean_ctor_set(v___x_4151_, 1, v___x_4150_);
if (v_isShared_4143_ == 0)
{
lean_ctor_set_tag(v___x_4142_, 0);
lean_ctor_set(v___x_4142_, 0, v___x_4151_);
v___x_4153_ = v___x_4142_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v___x_4151_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__4___boxed(lean_object* v_phase_4156_, lean_object* v_x_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_){
_start:
{
lean_object* v_res_4163_; 
v_res_4163_ = l_Lean_Elab_Tactic_NormCast_derive___lam__4(v_phase_4156_, v_x_4157_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_);
lean_dec(v___y_4161_);
lean_dec_ref(v___y_4160_);
lean_dec(v___y_4159_);
lean_dec_ref(v___y_4158_);
return v_res_4163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__5(lean_object* v___x_4164_, uint8_t v___x_4165_, lean_object* v_phase_4166_, lean_object* v_k_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v_options_4173_; uint8_t v_hasTrace_4174_; 
v_options_4173_ = lean_ctor_get(v___y_4170_, 2);
v_hasTrace_4174_ = lean_ctor_get_uint8(v_options_4173_, sizeof(void*)*1);
if (v_hasTrace_4174_ == 0)
{
lean_object* v___x_4175_; 
lean_dec_ref(v_phase_4166_);
lean_dec(v___x_4164_);
lean_inc(v___y_4171_);
lean_inc_ref(v___y_4170_);
lean_inc(v___y_4169_);
lean_inc_ref(v___y_4168_);
v___x_4175_ = lean_apply_5(v_k_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, lean_box(0));
return v___x_4175_;
}
else
{
lean_object* v_inheritedTraceOptions_4176_; lean_object* v___f_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; uint8_t v___x_4181_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v_a_4185_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v_a_4200_; 
v_inheritedTraceOptions_4176_ = lean_ctor_get(v___y_4170_, 13);
v___f_4177_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4177_, 0, v_phase_4166_);
v___x_4178_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_4179_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__2));
lean_inc(v___x_4164_);
v___x_4180_ = l_Lean_Name_append(v___x_4179_, v___x_4164_);
v___x_4181_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4176_, v_options_4173_, v___x_4180_);
lean_dec(v___x_4180_);
if (v___x_4181_ == 0)
{
lean_object* v___x_4250_; uint8_t v___x_4251_; 
v___x_4250_ = l_Lean_trace_profiler;
v___x_4251_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_4173_, v___x_4250_);
if (v___x_4251_ == 0)
{
lean_object* v___x_4252_; 
lean_dec_ref(v___f_4177_);
lean_dec(v___x_4164_);
lean_inc(v___y_4171_);
lean_inc_ref(v___y_4170_);
lean_inc(v___y_4169_);
lean_inc_ref(v___y_4168_);
v___x_4252_ = lean_apply_5(v_k_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, lean_box(0));
return v___x_4252_;
}
else
{
goto v___jp_4209_;
}
}
else
{
goto v___jp_4209_;
}
v___jp_4182_:
{
lean_object* v___x_4186_; double v___x_4187_; double v___x_4188_; double v___x_4189_; double v___x_4190_; double v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4186_ = lean_io_mono_nanos_now();
v___x_4187_ = lean_float_of_nat(v___y_4183_);
v___x_4188_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4);
v___x_4189_ = lean_float_div(v___x_4187_, v___x_4188_);
v___x_4190_ = lean_float_of_nat(v___x_4186_);
v___x_4191_ = lean_float_div(v___x_4190_, v___x_4188_);
v___x_4192_ = lean_box_float(v___x_4189_);
v___x_4193_ = lean_box_float(v___x_4191_);
v___x_4194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4192_);
lean_ctor_set(v___x_4194_, 1, v___x_4193_);
v___x_4195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4195_, 0, v_a_4185_);
lean_ctor_set(v___x_4195_, 1, v___x_4194_);
v___x_4196_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4164_, v___x_4165_, v___x_4178_, v_options_4173_, v___x_4181_, v___y_4184_, v___f_4177_, v___x_4195_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
return v___x_4196_;
}
v___jp_4197_:
{
lean_object* v___x_4201_; double v___x_4202_; double v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4201_ = lean_io_get_num_heartbeats();
v___x_4202_ = lean_float_of_nat(v___y_4198_);
v___x_4203_ = lean_float_of_nat(v___x_4201_);
v___x_4204_ = lean_box_float(v___x_4202_);
v___x_4205_ = lean_box_float(v___x_4203_);
v___x_4206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4206_, 0, v___x_4204_);
lean_ctor_set(v___x_4206_, 1, v___x_4205_);
v___x_4207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4207_, 0, v_a_4200_);
lean_ctor_set(v___x_4207_, 1, v___x_4206_);
v___x_4208_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4164_, v___x_4165_, v___x_4178_, v_options_4173_, v___x_4181_, v___y_4199_, v___f_4177_, v___x_4207_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_);
return v___x_4208_;
}
v___jp_4209_:
{
lean_object* v___x_4210_; lean_object* v_a_4211_; lean_object* v___x_4212_; uint8_t v___x_4213_; 
v___x_4210_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___y_4171_);
v_a_4211_ = lean_ctor_get(v___x_4210_, 0);
lean_inc(v_a_4211_);
lean_dec_ref(v___x_4210_);
v___x_4212_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4213_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_4173_, v___x_4212_);
if (v___x_4213_ == 0)
{
lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4214_ = lean_io_mono_nanos_now();
lean_inc(v___y_4171_);
lean_inc_ref(v___y_4170_);
lean_inc(v___y_4169_);
lean_inc_ref(v___y_4168_);
v___x_4215_ = lean_apply_5(v_k_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, lean_box(0));
if (lean_obj_tag(v___x_4215_) == 0)
{
lean_object* v_a_4216_; lean_object* v___x_4218_; uint8_t v_isShared_4219_; uint8_t v_isSharedCheck_4223_; 
v_a_4216_ = lean_ctor_get(v___x_4215_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v___x_4215_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4218_ = v___x_4215_;
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
else
{
lean_inc(v_a_4216_);
lean_dec(v___x_4215_);
v___x_4218_ = lean_box(0);
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
v_resetjp_4217_:
{
lean_object* v___x_4221_; 
if (v_isShared_4219_ == 0)
{
lean_ctor_set_tag(v___x_4218_, 1);
v___x_4221_ = v___x_4218_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v_a_4216_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
v___y_4183_ = v___x_4214_;
v___y_4184_ = v_a_4211_;
v_a_4185_ = v___x_4221_;
goto v___jp_4182_;
}
}
}
else
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4231_; 
v_a_4224_ = lean_ctor_get(v___x_4215_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4215_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4226_ = v___x_4215_;
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___x_4215_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4229_; 
if (v_isShared_4227_ == 0)
{
lean_ctor_set_tag(v___x_4226_, 0);
v___x_4229_ = v___x_4226_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_a_4224_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
v___y_4183_ = v___x_4214_;
v___y_4184_ = v_a_4211_;
v_a_4185_ = v___x_4229_;
goto v___jp_4182_;
}
}
}
}
else
{
lean_object* v___x_4232_; lean_object* v___x_4233_; 
v___x_4232_ = lean_io_get_num_heartbeats();
lean_inc(v___y_4171_);
lean_inc_ref(v___y_4170_);
lean_inc(v___y_4169_);
lean_inc_ref(v___y_4168_);
v___x_4233_ = lean_apply_5(v_k_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, lean_box(0));
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v_a_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4241_; 
v_a_4234_ = lean_ctor_get(v___x_4233_, 0);
v_isSharedCheck_4241_ = !lean_is_exclusive(v___x_4233_);
if (v_isSharedCheck_4241_ == 0)
{
v___x_4236_ = v___x_4233_;
v_isShared_4237_ = v_isSharedCheck_4241_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_a_4234_);
lean_dec(v___x_4233_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4241_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
lean_object* v___x_4239_; 
if (v_isShared_4237_ == 0)
{
lean_ctor_set_tag(v___x_4236_, 1);
v___x_4239_ = v___x_4236_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_a_4234_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
v___y_4198_ = v___x_4232_;
v___y_4199_ = v_a_4211_;
v_a_4200_ = v___x_4239_;
goto v___jp_4197_;
}
}
}
else
{
lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4249_; 
v_a_4242_ = lean_ctor_get(v___x_4233_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4233_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4244_ = v___x_4233_;
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_dec(v___x_4233_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4247_; 
if (v_isShared_4245_ == 0)
{
lean_ctor_set_tag(v___x_4244_, 0);
v___x_4247_ = v___x_4244_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v_a_4242_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
v___y_4198_ = v___x_4232_;
v___y_4199_ = v_a_4211_;
v_a_4200_ = v___x_4247_;
goto v___jp_4197_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__5___boxed(lean_object* v___x_4253_, lean_object* v___x_4254_, lean_object* v_phase_4255_, lean_object* v_k_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_){
_start:
{
uint8_t v___x_35174__boxed_4262_; lean_object* v_res_4263_; 
v___x_35174__boxed_4262_ = lean_unbox(v___x_4254_);
v_res_4263_ = l_Lean_Elab_Tactic_NormCast_derive___lam__5(v___x_4253_, v___x_35174__boxed_4262_, v_phase_4255_, v_k_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_);
lean_dec(v___y_4260_);
lean_dec_ref(v___y_4259_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
return v_res_4263_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__6(lean_object* v___x_4264_, uint8_t v___x_4265_, lean_object* v_e_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
lean_object* v_a_4276_; lean_object* v___y_4280_; lean_object* v___x_4290_; 
lean_inc_ref(v_e_4266_);
v___x_4290_ = l_Lean_Elab_Tactic_NormCast_numeralToCoe(v_e_4266_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_);
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_dec_ref(v_e_4266_);
lean_dec(v___x_4264_);
v___y_4280_ = v___x_4290_;
goto v___jp_4279_;
}
else
{
lean_object* v_a_4291_; uint8_t v___y_4293_; uint8_t v___x_4295_; 
v_a_4291_ = lean_ctor_get(v___x_4290_, 0);
lean_inc(v_a_4291_);
v___x_4295_ = l_Lean_Exception_isInterrupt(v_a_4291_);
if (v___x_4295_ == 0)
{
uint8_t v___x_4296_; 
v___x_4296_ = l_Lean_Exception_isRuntime(v_a_4291_);
v___y_4293_ = v___x_4296_;
goto v___jp_4292_;
}
else
{
lean_dec(v_a_4291_);
v___y_4293_ = v___x_4295_;
goto v___jp_4292_;
}
v___jp_4292_:
{
if (v___y_4293_ == 0)
{
lean_object* v___x_4294_; 
lean_dec_ref(v___x_4290_);
v___x_4294_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4294_, 0, v_e_4266_);
lean_ctor_set(v___x_4294_, 1, v___x_4264_);
lean_ctor_set_uint8(v___x_4294_, sizeof(void*)*2, v___x_4265_);
v_a_4276_ = v___x_4294_;
goto v___jp_4275_;
}
else
{
lean_dec_ref(v_e_4266_);
lean_dec(v___x_4264_);
v___y_4280_ = v___x_4290_;
goto v___jp_4279_;
}
}
}
v___jp_4275_:
{
lean_object* v___x_4277_; lean_object* v___x_4278_; 
v___x_4277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4277_, 0, v_a_4276_);
v___x_4278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4278_, 0, v___x_4277_);
return v___x_4278_;
}
v___jp_4279_:
{
if (lean_obj_tag(v___y_4280_) == 0)
{
lean_object* v_a_4281_; 
v_a_4281_ = lean_ctor_get(v___y_4280_, 0);
lean_inc(v_a_4281_);
lean_dec_ref(v___y_4280_);
v_a_4276_ = v_a_4281_;
goto v___jp_4275_;
}
else
{
lean_object* v_a_4282_; lean_object* v___x_4284_; uint8_t v_isShared_4285_; uint8_t v_isSharedCheck_4289_; 
v_a_4282_ = lean_ctor_get(v___y_4280_, 0);
v_isSharedCheck_4289_ = !lean_is_exclusive(v___y_4280_);
if (v_isSharedCheck_4289_ == 0)
{
v___x_4284_ = v___y_4280_;
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
else
{
lean_inc(v_a_4282_);
lean_dec(v___y_4280_);
v___x_4284_ = lean_box(0);
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
v_resetjp_4283_:
{
lean_object* v___x_4287_; 
if (v_isShared_4285_ == 0)
{
v___x_4287_ = v___x_4284_;
goto v_reusejp_4286_;
}
else
{
lean_object* v_reuseFailAlloc_4288_; 
v_reuseFailAlloc_4288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4288_, 0, v_a_4282_);
v___x_4287_ = v_reuseFailAlloc_4288_;
goto v_reusejp_4286_;
}
v_reusejp_4286_:
{
return v___x_4287_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__6___boxed(lean_object* v___x_4297_, lean_object* v___x_4298_, lean_object* v_e_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_){
_start:
{
uint8_t v___x_35352__boxed_4308_; lean_object* v_res_4309_; 
v___x_35352__boxed_4308_ = lean_unbox(v___x_4298_);
v_res_4309_ = l_Lean_Elab_Tactic_NormCast_derive___lam__6(v___x_4297_, v___x_35352__boxed_4308_, v_e_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec(v___y_4302_);
lean_dec_ref(v___y_4301_);
lean_dec(v___y_4300_);
return v_res_4309_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__0(void){
_start:
{
lean_object* v___x_4310_; 
v___x_4310_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4310_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1(void){
_start:
{
lean_object* v___x_4311_; lean_object* v___x_4312_; 
v___x_4311_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__0, &l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__0_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__0);
v___x_4312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4312_, 0, v___x_4311_);
return v___x_4312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__7(lean_object* v_config_4313_, lean_object* v___x_4314_, lean_object* v_a_4315_, lean_object* v___x_4316_, lean_object* v___f_4317_, lean_object* v___f_4318_, lean_object* v___f_4319_, lean_object* v___f_4320_, lean_object* v___f_4321_, uint8_t v___x_4322_, lean_object* v_a_4323_, lean_object* v___x_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_){
_start:
{
lean_object* v___x_4330_; 
v___x_4330_ = l_Lean_Meta_Simp_mkContext___redArg(v_config_4313_, v___x_4314_, v_a_4315_, v___y_4325_, v___y_4327_, v___y_4328_);
if (lean_obj_tag(v___x_4330_) == 0)
{
lean_object* v_a_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; size_t v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; 
v_a_4331_ = lean_ctor_get(v___x_4330_, 0);
lean_inc(v_a_4331_);
lean_dec_ref(v___x_4330_);
v___x_4332_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1, &l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1);
lean_inc_n(v___x_4316_, 2);
v___x_4333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4333_, 0, v___x_4332_);
lean_ctor_set(v___x_4333_, 1, v___x_4316_);
v___x_4334_ = lean_unsigned_to_nat(32u);
v___x_4335_ = lean_mk_empty_array_with_capacity(v___x_4334_);
v___x_4336_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8);
v___x_4337_ = ((size_t)5ULL);
v___x_4338_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4338_, 0, v___x_4336_);
lean_ctor_set(v___x_4338_, 1, v___x_4335_);
lean_ctor_set(v___x_4338_, 2, v___x_4316_);
lean_ctor_set(v___x_4338_, 3, v___x_4316_);
lean_ctor_set_usize(v___x_4338_, 4, v___x_4337_);
v___x_4339_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4339_, 0, v___x_4332_);
lean_ctor_set(v___x_4339_, 1, v___x_4332_);
lean_ctor_set(v___x_4339_, 2, v___x_4332_);
lean_ctor_set(v___x_4339_, 3, v___x_4338_);
v___x_4340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4340_, 0, v___x_4333_);
lean_ctor_set(v___x_4340_, 1, v___x_4339_);
v___x_4341_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4341_, 0, v___f_4317_);
lean_ctor_set(v___x_4341_, 1, v___f_4318_);
lean_ctor_set(v___x_4341_, 2, v___f_4319_);
lean_ctor_set(v___x_4341_, 3, v___f_4320_);
lean_ctor_set(v___x_4341_, 4, v___f_4321_);
lean_ctor_set_uint8(v___x_4341_, sizeof(void*)*5, v___x_4322_);
v___x_4342_ = l_Lean_Meta_Simp_main(v_a_4323_, v_a_4331_, v___x_4340_, v___x_4341_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
if (lean_obj_tag(v___x_4342_) == 0)
{
lean_object* v_a_4343_; lean_object* v_fst_4344_; lean_object* v___x_4345_; 
v_a_4343_ = lean_ctor_get(v___x_4342_, 0);
lean_inc(v_a_4343_);
lean_dec_ref(v___x_4342_);
v_fst_4344_ = lean_ctor_get(v_a_4343_, 0);
lean_inc(v_fst_4344_);
lean_dec(v_a_4343_);
v___x_4345_ = l_Lean_Meta_Simp_Result_mkEqTrans(v___x_4324_, v_fst_4344_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
return v___x_4345_;
}
else
{
lean_object* v_a_4346_; lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4353_; 
lean_dec_ref(v___x_4324_);
v_a_4346_ = lean_ctor_get(v___x_4342_, 0);
v_isSharedCheck_4353_ = !lean_is_exclusive(v___x_4342_);
if (v_isSharedCheck_4353_ == 0)
{
v___x_4348_ = v___x_4342_;
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
else
{
lean_inc(v_a_4346_);
lean_dec(v___x_4342_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v___x_4351_; 
if (v_isShared_4349_ == 0)
{
v___x_4351_ = v___x_4348_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_a_4346_);
v___x_4351_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
return v___x_4351_;
}
}
}
}
else
{
lean_object* v_a_4354_; lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4361_; 
lean_dec_ref(v___x_4324_);
lean_dec_ref(v_a_4323_);
lean_dec_ref(v___f_4321_);
lean_dec_ref(v___f_4320_);
lean_dec_ref(v___f_4319_);
lean_dec_ref(v___f_4318_);
lean_dec_ref(v___f_4317_);
lean_dec(v___x_4316_);
v_a_4354_ = lean_ctor_get(v___x_4330_, 0);
v_isSharedCheck_4361_ = !lean_is_exclusive(v___x_4330_);
if (v_isSharedCheck_4361_ == 0)
{
v___x_4356_ = v___x_4330_;
v_isShared_4357_ = v_isSharedCheck_4361_;
goto v_resetjp_4355_;
}
else
{
lean_inc(v_a_4354_);
lean_dec(v___x_4330_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4361_;
goto v_resetjp_4355_;
}
v_resetjp_4355_:
{
lean_object* v___x_4359_; 
if (v_isShared_4357_ == 0)
{
v___x_4359_ = v___x_4356_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v_a_4354_);
v___x_4359_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
return v___x_4359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__7___boxed(lean_object** _args){
lean_object* v_config_4362_ = _args[0];
lean_object* v___x_4363_ = _args[1];
lean_object* v_a_4364_ = _args[2];
lean_object* v___x_4365_ = _args[3];
lean_object* v___f_4366_ = _args[4];
lean_object* v___f_4367_ = _args[5];
lean_object* v___f_4368_ = _args[6];
lean_object* v___f_4369_ = _args[7];
lean_object* v___f_4370_ = _args[8];
lean_object* v___x_4371_ = _args[9];
lean_object* v_a_4372_ = _args[10];
lean_object* v___x_4373_ = _args[11];
lean_object* v___y_4374_ = _args[12];
lean_object* v___y_4375_ = _args[13];
lean_object* v___y_4376_ = _args[14];
lean_object* v___y_4377_ = _args[15];
lean_object* v___y_4378_ = _args[16];
_start:
{
uint8_t v___x_35443__boxed_4379_; lean_object* v_res_4380_; 
v___x_35443__boxed_4379_ = lean_unbox(v___x_4371_);
v_res_4380_ = l_Lean_Elab_Tactic_NormCast_derive___lam__7(v_config_4362_, v___x_4363_, v_a_4364_, v___x_4365_, v___f_4366_, v___f_4367_, v___f_4368_, v___f_4369_, v___f_4370_, v___x_35443__boxed_4379_, v_a_4372_, v___x_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4374_);
return v_res_4380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__12(lean_object* v_up_4381_, lean_object* v_config_4382_, lean_object* v___x_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v___x_4386_, lean_object* v___f_4387_, lean_object* v___f_4388_, lean_object* v___f_4389_, lean_object* v___f_4390_, uint8_t v___x_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_){
_start:
{
lean_object* v___x_4397_; 
v___x_4397_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_up_4381_, v___y_4395_);
if (lean_obj_tag(v___x_4397_) == 0)
{
lean_object* v_a_4398_; lean_object* v___x_4399_; 
v_a_4398_ = lean_ctor_get(v___x_4397_, 0);
lean_inc(v_a_4398_);
lean_dec_ref(v___x_4397_);
v___x_4399_ = l_Lean_Meta_Simp_mkContext___redArg(v_config_4382_, v___x_4383_, v_a_4384_, v___y_4392_, v___y_4394_, v___y_4395_);
if (lean_obj_tag(v___x_4399_) == 0)
{
lean_object* v_a_4400_; lean_object* v_expr_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; size_t v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; 
v_a_4400_ = lean_ctor_get(v___x_4399_, 0);
lean_inc(v_a_4400_);
lean_dec_ref(v___x_4399_);
v_expr_4401_ = lean_ctor_get(v_a_4385_, 0);
v___x_4402_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_upwardAndElim___boxed), 10, 1);
lean_closure_set(v___x_4402_, 0, v_a_4398_);
v___x_4403_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1, &l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1);
lean_inc_n(v___x_4386_, 2);
v___x_4404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4404_, 0, v___x_4403_);
lean_ctor_set(v___x_4404_, 1, v___x_4386_);
v___x_4405_ = lean_unsigned_to_nat(32u);
v___x_4406_ = lean_mk_empty_array_with_capacity(v___x_4405_);
v___x_4407_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8);
v___x_4408_ = ((size_t)5ULL);
v___x_4409_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4409_, 0, v___x_4407_);
lean_ctor_set(v___x_4409_, 1, v___x_4406_);
lean_ctor_set(v___x_4409_, 2, v___x_4386_);
lean_ctor_set(v___x_4409_, 3, v___x_4386_);
lean_ctor_set_usize(v___x_4409_, 4, v___x_4408_);
v___x_4410_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4410_, 0, v___x_4403_);
lean_ctor_set(v___x_4410_, 1, v___x_4403_);
lean_ctor_set(v___x_4410_, 2, v___x_4403_);
lean_ctor_set(v___x_4410_, 3, v___x_4409_);
v___x_4411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4411_, 0, v___x_4404_);
lean_ctor_set(v___x_4411_, 1, v___x_4410_);
v___x_4412_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4412_, 0, v___f_4387_);
lean_ctor_set(v___x_4412_, 1, v___x_4402_);
lean_ctor_set(v___x_4412_, 2, v___f_4388_);
lean_ctor_set(v___x_4412_, 3, v___f_4389_);
lean_ctor_set(v___x_4412_, 4, v___f_4390_);
lean_ctor_set_uint8(v___x_4412_, sizeof(void*)*5, v___x_4391_);
lean_inc_ref(v_expr_4401_);
v___x_4413_ = l_Lean_Meta_Simp_main(v_expr_4401_, v_a_4400_, v___x_4411_, v___x_4412_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
if (lean_obj_tag(v___x_4413_) == 0)
{
lean_object* v_a_4414_; lean_object* v_fst_4415_; lean_object* v___x_4416_; 
v_a_4414_ = lean_ctor_get(v___x_4413_, 0);
lean_inc(v_a_4414_);
lean_dec_ref(v___x_4413_);
v_fst_4415_ = lean_ctor_get(v_a_4414_, 0);
lean_inc(v_fst_4415_);
lean_dec(v_a_4414_);
v___x_4416_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_4385_, v_fst_4415_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
return v___x_4416_;
}
else
{
lean_object* v_a_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4424_; 
lean_dec_ref(v_a_4385_);
v_a_4417_ = lean_ctor_get(v___x_4413_, 0);
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4413_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4419_ = v___x_4413_;
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_a_4417_);
lean_dec(v___x_4413_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v___x_4422_; 
if (v_isShared_4420_ == 0)
{
v___x_4422_ = v___x_4419_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_a_4417_);
v___x_4422_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
return v___x_4422_;
}
}
}
}
else
{
lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4432_; 
lean_dec(v_a_4398_);
lean_dec_ref(v___f_4390_);
lean_dec_ref(v___f_4389_);
lean_dec_ref(v___f_4388_);
lean_dec_ref(v___f_4387_);
lean_dec(v___x_4386_);
lean_dec_ref(v_a_4385_);
v_a_4425_ = lean_ctor_get(v___x_4399_, 0);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4399_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4427_ = v___x_4399_;
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v___x_4399_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4430_; 
if (v_isShared_4428_ == 0)
{
v___x_4430_ = v___x_4427_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_a_4425_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
}
}
}
}
else
{
lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4440_; 
lean_dec_ref(v___f_4390_);
lean_dec_ref(v___f_4389_);
lean_dec_ref(v___f_4388_);
lean_dec_ref(v___f_4387_);
lean_dec(v___x_4386_);
lean_dec_ref(v_a_4385_);
lean_dec_ref(v_a_4384_);
lean_dec_ref(v___x_4383_);
lean_dec_ref(v_config_4382_);
v_a_4433_ = lean_ctor_get(v___x_4397_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4397_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4435_ = v___x_4397_;
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4397_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4438_; 
if (v_isShared_4436_ == 0)
{
v___x_4438_ = v___x_4435_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_a_4433_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__12___boxed(lean_object* v_up_4441_, lean_object* v_config_4442_, lean_object* v___x_4443_, lean_object* v_a_4444_, lean_object* v_a_4445_, lean_object* v___x_4446_, lean_object* v___f_4447_, lean_object* v___f_4448_, lean_object* v___f_4449_, lean_object* v___f_4450_, lean_object* v___x_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_){
_start:
{
uint8_t v___x_35562__boxed_4457_; lean_object* v_res_4458_; 
v___x_35562__boxed_4457_ = lean_unbox(v___x_4451_);
v_res_4458_ = l_Lean_Elab_Tactic_NormCast_derive___lam__12(v_up_4441_, v_config_4442_, v___x_4443_, v_a_4444_, v_a_4445_, v___x_4446_, v___f_4447_, v___f_4448_, v___f_4449_, v___f_4450_, v___x_35562__boxed_4457_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_);
lean_dec(v___y_4455_);
lean_dec_ref(v___y_4454_);
lean_dec(v___y_4453_);
lean_dec_ref(v___y_4452_);
lean_dec_ref(v_up_4441_);
return v_res_4458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__8(lean_object* v_squash_4459_, lean_object* v_config_4460_, lean_object* v_a_4461_, lean_object* v_a_4462_, lean_object* v___x_4463_, lean_object* v_a_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_){
_start:
{
lean_object* v___x_4470_; 
v___x_4470_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_squash_4459_, v___y_4468_);
if (lean_obj_tag(v___x_4470_) == 0)
{
lean_object* v_a_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; 
v_a_4471_ = lean_ctor_get(v___x_4470_, 0);
lean_inc(v_a_4471_);
lean_dec_ref(v___x_4470_);
v___x_4472_ = lean_unsigned_to_nat(1u);
v___x_4473_ = lean_mk_empty_array_with_capacity(v___x_4472_);
v___x_4474_ = lean_array_push(v___x_4473_, v_a_4471_);
v___x_4475_ = l_Lean_Meta_Simp_mkContext___redArg(v_config_4460_, v___x_4474_, v_a_4461_, v___y_4465_, v___y_4467_, v___y_4468_);
if (lean_obj_tag(v___x_4475_) == 0)
{
lean_object* v_a_4476_; lean_object* v_expr_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; size_t v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; 
v_a_4476_ = lean_ctor_get(v___x_4475_, 0);
lean_inc(v_a_4476_);
lean_dec_ref(v___x_4475_);
v_expr_4477_ = lean_ctor_get(v_a_4462_, 0);
v___x_4478_ = lean_box(0);
v___x_4479_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1, &l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1);
lean_inc_n(v___x_4463_, 2);
v___x_4480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4480_, 0, v___x_4479_);
lean_ctor_set(v___x_4480_, 1, v___x_4463_);
v___x_4481_ = lean_unsigned_to_nat(32u);
v___x_4482_ = lean_mk_empty_array_with_capacity(v___x_4481_);
v___x_4483_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8);
v___x_4484_ = ((size_t)5ULL);
v___x_4485_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4485_, 0, v___x_4483_);
lean_ctor_set(v___x_4485_, 1, v___x_4482_);
lean_ctor_set(v___x_4485_, 2, v___x_4463_);
lean_ctor_set(v___x_4485_, 3, v___x_4463_);
lean_ctor_set_usize(v___x_4485_, 4, v___x_4484_);
v___x_4486_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4486_, 0, v___x_4479_);
lean_ctor_set(v___x_4486_, 1, v___x_4479_);
lean_ctor_set(v___x_4486_, 2, v___x_4479_);
lean_ctor_set(v___x_4486_, 3, v___x_4485_);
v___x_4487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4487_, 0, v___x_4480_);
lean_ctor_set(v___x_4487_, 1, v___x_4486_);
lean_inc_ref(v_expr_4477_);
v___x_4488_ = l_Lean_Meta_simp(v_expr_4477_, v_a_4476_, v_a_4464_, v___x_4478_, v___x_4487_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_);
lean_dec_ref(v___x_4487_);
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_object* v_a_4489_; lean_object* v_fst_4490_; lean_object* v___x_4491_; 
v_a_4489_ = lean_ctor_get(v___x_4488_, 0);
lean_inc(v_a_4489_);
lean_dec_ref(v___x_4488_);
v_fst_4490_ = lean_ctor_get(v_a_4489_, 0);
lean_inc(v_fst_4490_);
lean_dec(v_a_4489_);
v___x_4491_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_4462_, v_fst_4490_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_);
return v___x_4491_;
}
else
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4499_; 
lean_dec_ref(v_a_4462_);
v_a_4492_ = lean_ctor_get(v___x_4488_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4488_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4494_ = v___x_4488_;
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_a_4492_);
lean_dec(v___x_4488_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4497_; 
if (v_isShared_4495_ == 0)
{
v___x_4497_ = v___x_4494_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_a_4492_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
}
}
}
}
else
{
lean_object* v_a_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4507_; 
lean_dec_ref(v_a_4464_);
lean_dec(v___x_4463_);
lean_dec_ref(v_a_4462_);
v_a_4500_ = lean_ctor_get(v___x_4475_, 0);
v_isSharedCheck_4507_ = !lean_is_exclusive(v___x_4475_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4502_ = v___x_4475_;
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_a_4500_);
lean_dec(v___x_4475_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v___x_4505_; 
if (v_isShared_4503_ == 0)
{
v___x_4505_ = v___x_4502_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_a_4500_);
v___x_4505_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
return v___x_4505_;
}
}
}
}
else
{
lean_object* v_a_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4515_; 
lean_dec_ref(v_a_4464_);
lean_dec(v___x_4463_);
lean_dec_ref(v_a_4462_);
lean_dec_ref(v_a_4461_);
lean_dec_ref(v_config_4460_);
v_a_4508_ = lean_ctor_get(v___x_4470_, 0);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4470_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4510_ = v___x_4470_;
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
else
{
lean_inc(v_a_4508_);
lean_dec(v___x_4470_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v___x_4513_; 
if (v_isShared_4511_ == 0)
{
v___x_4513_ = v___x_4510_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_a_4508_);
v___x_4513_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
return v___x_4513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__8___boxed(lean_object* v_squash_4516_, lean_object* v_config_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v___x_4520_, lean_object* v_a_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_){
_start:
{
lean_object* v_res_4527_; 
v_res_4527_ = l_Lean_Elab_Tactic_NormCast_derive___lam__8(v_squash_4516_, v_config_4517_, v_a_4518_, v_a_4519_, v___x_4520_, v_a_4521_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_);
lean_dec(v___y_4525_);
lean_dec_ref(v___y_4524_);
lean_dec(v___y_4523_);
lean_dec_ref(v___y_4522_);
lean_dec_ref(v_squash_4516_);
return v_res_4527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__18(lean_object* v_e_4528_, lean_object* v_x_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_){
_start:
{
lean_object* v___x_4535_; lean_object* v___x_4536_; 
v___x_4535_ = l_Lean_MessageData_ofExpr(v_e_4528_);
v___x_4536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4536_, 0, v___x_4535_);
return v___x_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__18___boxed(lean_object* v_e_4537_, lean_object* v_x_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_, lean_object* v___y_4543_){
_start:
{
lean_object* v_res_4544_; 
v_res_4544_ = l_Lean_Elab_Tactic_NormCast_derive___lam__18(v_e_4537_, v_x_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_);
lean_dec(v___y_4542_);
lean_dec_ref(v___y_4541_);
lean_dec(v___y_4540_);
lean_dec_ref(v___y_4539_);
lean_dec_ref(v_x_4538_);
return v_res_4544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__10(lean_object* v___x_4545_, uint8_t v_hasTrace_4546_, lean_object* v_phase_4547_, lean_object* v_k_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_){
_start:
{
lean_object* v_options_4554_; uint8_t v_hasTrace_4555_; 
v_options_4554_ = lean_ctor_get(v___y_4551_, 2);
v_hasTrace_4555_ = lean_ctor_get_uint8(v_options_4554_, sizeof(void*)*1);
if (v_hasTrace_4555_ == 0)
{
lean_object* v___x_4556_; 
lean_dec_ref(v_phase_4547_);
lean_dec(v___x_4545_);
lean_inc(v___y_4552_);
lean_inc_ref(v___y_4551_);
lean_inc(v___y_4550_);
lean_inc_ref(v___y_4549_);
v___x_4556_ = lean_apply_5(v_k_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, lean_box(0));
return v___x_4556_;
}
else
{
lean_object* v_inheritedTraceOptions_4557_; lean_object* v___f_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; uint8_t v___x_4562_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v_a_4566_; lean_object* v___y_4579_; lean_object* v___y_4580_; lean_object* v_a_4581_; 
v_inheritedTraceOptions_4557_ = lean_ctor_get(v___y_4551_, 13);
v___f_4558_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4558_, 0, v_phase_4547_);
v___x_4559_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_4560_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__2));
lean_inc(v___x_4545_);
v___x_4561_ = l_Lean_Name_append(v___x_4560_, v___x_4545_);
v___x_4562_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4557_, v_options_4554_, v___x_4561_);
lean_dec(v___x_4561_);
if (v___x_4562_ == 0)
{
lean_object* v___x_4631_; uint8_t v___x_4632_; 
v___x_4631_ = l_Lean_trace_profiler;
v___x_4632_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_4554_, v___x_4631_);
if (v___x_4632_ == 0)
{
lean_object* v___x_4633_; 
lean_dec_ref(v___f_4558_);
lean_dec(v___x_4545_);
lean_inc(v___y_4552_);
lean_inc_ref(v___y_4551_);
lean_inc(v___y_4550_);
lean_inc_ref(v___y_4549_);
v___x_4633_ = lean_apply_5(v_k_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, lean_box(0));
return v___x_4633_;
}
else
{
goto v___jp_4590_;
}
}
else
{
goto v___jp_4590_;
}
v___jp_4563_:
{
lean_object* v___x_4567_; double v___x_4568_; double v___x_4569_; double v___x_4570_; double v___x_4571_; double v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; 
v___x_4567_ = lean_io_mono_nanos_now();
v___x_4568_ = lean_float_of_nat(v___y_4564_);
v___x_4569_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4);
v___x_4570_ = lean_float_div(v___x_4568_, v___x_4569_);
v___x_4571_ = lean_float_of_nat(v___x_4567_);
v___x_4572_ = lean_float_div(v___x_4571_, v___x_4569_);
v___x_4573_ = lean_box_float(v___x_4570_);
v___x_4574_ = lean_box_float(v___x_4572_);
v___x_4575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4575_, 0, v___x_4573_);
lean_ctor_set(v___x_4575_, 1, v___x_4574_);
v___x_4576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4576_, 0, v_a_4566_);
lean_ctor_set(v___x_4576_, 1, v___x_4575_);
v___x_4577_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4545_, v_hasTrace_4546_, v___x_4559_, v_options_4554_, v___x_4562_, v___y_4565_, v___f_4558_, v___x_4576_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_);
return v___x_4577_;
}
v___jp_4578_:
{
lean_object* v___x_4582_; double v___x_4583_; double v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; 
v___x_4582_ = lean_io_get_num_heartbeats();
v___x_4583_ = lean_float_of_nat(v___y_4579_);
v___x_4584_ = lean_float_of_nat(v___x_4582_);
v___x_4585_ = lean_box_float(v___x_4583_);
v___x_4586_ = lean_box_float(v___x_4584_);
v___x_4587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4587_, 0, v___x_4585_);
lean_ctor_set(v___x_4587_, 1, v___x_4586_);
v___x_4588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4588_, 0, v_a_4581_);
lean_ctor_set(v___x_4588_, 1, v___x_4587_);
v___x_4589_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4545_, v_hasTrace_4546_, v___x_4559_, v_options_4554_, v___x_4562_, v___y_4580_, v___f_4558_, v___x_4588_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_);
return v___x_4589_;
}
v___jp_4590_:
{
lean_object* v___x_4591_; lean_object* v_a_4592_; lean_object* v___x_4593_; uint8_t v___x_4594_; 
v___x_4591_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___y_4552_);
v_a_4592_ = lean_ctor_get(v___x_4591_, 0);
lean_inc(v_a_4592_);
lean_dec_ref(v___x_4591_);
v___x_4593_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4594_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_4554_, v___x_4593_);
if (v___x_4594_ == 0)
{
lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4595_ = lean_io_mono_nanos_now();
lean_inc(v___y_4552_);
lean_inc_ref(v___y_4551_);
lean_inc(v___y_4550_);
lean_inc_ref(v___y_4549_);
v___x_4596_ = lean_apply_5(v_k_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, lean_box(0));
if (lean_obj_tag(v___x_4596_) == 0)
{
lean_object* v_a_4597_; lean_object* v___x_4599_; uint8_t v_isShared_4600_; uint8_t v_isSharedCheck_4604_; 
v_a_4597_ = lean_ctor_get(v___x_4596_, 0);
v_isSharedCheck_4604_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4599_ = v___x_4596_;
v_isShared_4600_ = v_isSharedCheck_4604_;
goto v_resetjp_4598_;
}
else
{
lean_inc(v_a_4597_);
lean_dec(v___x_4596_);
v___x_4599_ = lean_box(0);
v_isShared_4600_ = v_isSharedCheck_4604_;
goto v_resetjp_4598_;
}
v_resetjp_4598_:
{
lean_object* v___x_4602_; 
if (v_isShared_4600_ == 0)
{
lean_ctor_set_tag(v___x_4599_, 1);
v___x_4602_ = v___x_4599_;
goto v_reusejp_4601_;
}
else
{
lean_object* v_reuseFailAlloc_4603_; 
v_reuseFailAlloc_4603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4603_, 0, v_a_4597_);
v___x_4602_ = v_reuseFailAlloc_4603_;
goto v_reusejp_4601_;
}
v_reusejp_4601_:
{
v___y_4564_ = v___x_4595_;
v___y_4565_ = v_a_4592_;
v_a_4566_ = v___x_4602_;
goto v___jp_4563_;
}
}
}
else
{
lean_object* v_a_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4612_; 
v_a_4605_ = lean_ctor_get(v___x_4596_, 0);
v_isSharedCheck_4612_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4612_ == 0)
{
v___x_4607_ = v___x_4596_;
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_a_4605_);
lean_dec(v___x_4596_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4612_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
lean_object* v___x_4610_; 
if (v_isShared_4608_ == 0)
{
lean_ctor_set_tag(v___x_4607_, 0);
v___x_4610_ = v___x_4607_;
goto v_reusejp_4609_;
}
else
{
lean_object* v_reuseFailAlloc_4611_; 
v_reuseFailAlloc_4611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4611_, 0, v_a_4605_);
v___x_4610_ = v_reuseFailAlloc_4611_;
goto v_reusejp_4609_;
}
v_reusejp_4609_:
{
v___y_4564_ = v___x_4595_;
v___y_4565_ = v_a_4592_;
v_a_4566_ = v___x_4610_;
goto v___jp_4563_;
}
}
}
}
else
{
lean_object* v___x_4613_; lean_object* v___x_4614_; 
v___x_4613_ = lean_io_get_num_heartbeats();
lean_inc(v___y_4552_);
lean_inc_ref(v___y_4551_);
lean_inc(v___y_4550_);
lean_inc_ref(v___y_4549_);
v___x_4614_ = lean_apply_5(v_k_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_, lean_box(0));
if (lean_obj_tag(v___x_4614_) == 0)
{
lean_object* v_a_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4622_; 
v_a_4615_ = lean_ctor_get(v___x_4614_, 0);
v_isSharedCheck_4622_ = !lean_is_exclusive(v___x_4614_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4617_ = v___x_4614_;
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_a_4615_);
lean_dec(v___x_4614_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4620_; 
if (v_isShared_4618_ == 0)
{
lean_ctor_set_tag(v___x_4617_, 1);
v___x_4620_ = v___x_4617_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v_a_4615_);
v___x_4620_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
v___y_4579_ = v___x_4613_;
v___y_4580_ = v_a_4592_;
v_a_4581_ = v___x_4620_;
goto v___jp_4578_;
}
}
}
else
{
lean_object* v_a_4623_; lean_object* v___x_4625_; uint8_t v_isShared_4626_; uint8_t v_isSharedCheck_4630_; 
v_a_4623_ = lean_ctor_get(v___x_4614_, 0);
v_isSharedCheck_4630_ = !lean_is_exclusive(v___x_4614_);
if (v_isSharedCheck_4630_ == 0)
{
v___x_4625_ = v___x_4614_;
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
else
{
lean_inc(v_a_4623_);
lean_dec(v___x_4614_);
v___x_4625_ = lean_box(0);
v_isShared_4626_ = v_isSharedCheck_4630_;
goto v_resetjp_4624_;
}
v_resetjp_4624_:
{
lean_object* v___x_4628_; 
if (v_isShared_4626_ == 0)
{
lean_ctor_set_tag(v___x_4625_, 0);
v___x_4628_ = v___x_4625_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v_a_4623_);
v___x_4628_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
v___y_4579_ = v___x_4613_;
v___y_4580_ = v_a_4592_;
v_a_4581_ = v___x_4628_;
goto v___jp_4578_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__10___boxed(lean_object* v___x_4634_, lean_object* v_hasTrace_4635_, lean_object* v_phase_4636_, lean_object* v_k_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_){
_start:
{
uint8_t v_hasTrace_boxed_4643_; lean_object* v_res_4644_; 
v_hasTrace_boxed_4643_ = lean_unbox(v_hasTrace_4635_);
v_res_4644_ = l_Lean_Elab_Tactic_NormCast_derive___lam__10(v___x_4634_, v_hasTrace_boxed_4643_, v_phase_4636_, v_k_4637_, v___y_4638_, v___y_4639_, v___y_4640_, v___y_4641_);
lean_dec(v___y_4641_);
lean_dec_ref(v___y_4640_);
lean_dec(v___y_4639_);
lean_dec_ref(v___y_4638_);
return v_res_4644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__9(lean_object* v___x_4645_, uint8_t v_hasTrace_4646_, lean_object* v_e_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_){
_start:
{
lean_object* v_a_4657_; lean_object* v___y_4661_; lean_object* v___x_4671_; 
lean_inc_ref(v_e_4647_);
v___x_4671_ = l_Lean_Elab_Tactic_NormCast_numeralToCoe(v_e_4647_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_);
if (lean_obj_tag(v___x_4671_) == 0)
{
lean_dec_ref(v_e_4647_);
lean_dec(v___x_4645_);
v___y_4661_ = v___x_4671_;
goto v___jp_4660_;
}
else
{
lean_object* v_a_4672_; uint8_t v___y_4674_; uint8_t v___x_4676_; 
v_a_4672_ = lean_ctor_get(v___x_4671_, 0);
lean_inc(v_a_4672_);
v___x_4676_ = l_Lean_Exception_isInterrupt(v_a_4672_);
if (v___x_4676_ == 0)
{
uint8_t v___x_4677_; 
v___x_4677_ = l_Lean_Exception_isRuntime(v_a_4672_);
v___y_4674_ = v___x_4677_;
goto v___jp_4673_;
}
else
{
lean_dec(v_a_4672_);
v___y_4674_ = v___x_4676_;
goto v___jp_4673_;
}
v___jp_4673_:
{
if (v___y_4674_ == 0)
{
lean_object* v___x_4675_; 
lean_dec_ref(v___x_4671_);
v___x_4675_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4675_, 0, v_e_4647_);
lean_ctor_set(v___x_4675_, 1, v___x_4645_);
lean_ctor_set_uint8(v___x_4675_, sizeof(void*)*2, v_hasTrace_4646_);
v_a_4657_ = v___x_4675_;
goto v___jp_4656_;
}
else
{
lean_dec_ref(v_e_4647_);
lean_dec(v___x_4645_);
v___y_4661_ = v___x_4671_;
goto v___jp_4660_;
}
}
}
v___jp_4656_:
{
lean_object* v___x_4658_; lean_object* v___x_4659_; 
v___x_4658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4658_, 0, v_a_4657_);
v___x_4659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4659_, 0, v___x_4658_);
return v___x_4659_;
}
v___jp_4660_:
{
if (lean_obj_tag(v___y_4661_) == 0)
{
lean_object* v_a_4662_; 
v_a_4662_ = lean_ctor_get(v___y_4661_, 0);
lean_inc(v_a_4662_);
lean_dec_ref(v___y_4661_);
v_a_4657_ = v_a_4662_;
goto v___jp_4656_;
}
else
{
lean_object* v_a_4663_; lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4670_; 
v_a_4663_ = lean_ctor_get(v___y_4661_, 0);
v_isSharedCheck_4670_ = !lean_is_exclusive(v___y_4661_);
if (v_isSharedCheck_4670_ == 0)
{
v___x_4665_ = v___y_4661_;
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
else
{
lean_inc(v_a_4663_);
lean_dec(v___y_4661_);
v___x_4665_ = lean_box(0);
v_isShared_4666_ = v_isSharedCheck_4670_;
goto v_resetjp_4664_;
}
v_resetjp_4664_:
{
lean_object* v___x_4668_; 
if (v_isShared_4666_ == 0)
{
v___x_4668_ = v___x_4665_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4669_; 
v_reuseFailAlloc_4669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4669_, 0, v_a_4663_);
v___x_4668_ = v_reuseFailAlloc_4669_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
return v___x_4668_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__9___boxed(lean_object* v___x_4678_, lean_object* v_hasTrace_4679_, lean_object* v_e_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_){
_start:
{
uint8_t v_hasTrace_boxed_4689_; lean_object* v_res_4690_; 
v_hasTrace_boxed_4689_ = lean_unbox(v_hasTrace_4679_);
v_res_4690_ = l_Lean_Elab_Tactic_NormCast_derive___lam__9(v___x_4678_, v_hasTrace_boxed_4689_, v_e_4680_, v___y_4681_, v___y_4682_, v___y_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_);
lean_dec(v___y_4687_);
lean_dec_ref(v___y_4686_);
lean_dec(v___y_4685_);
lean_dec_ref(v___y_4684_);
lean_dec(v___y_4683_);
lean_dec_ref(v___y_4682_);
lean_dec(v___y_4681_);
return v_res_4690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__14(lean_object* v_config_4691_, lean_object* v___x_4692_, lean_object* v_a_4693_, lean_object* v___x_4694_, lean_object* v___f_4695_, lean_object* v___f_4696_, lean_object* v___f_4697_, lean_object* v___f_4698_, lean_object* v___f_4699_, uint8_t v_hasTrace_4700_, lean_object* v_a_4701_, lean_object* v___x_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_){
_start:
{
lean_object* v___x_4708_; 
v___x_4708_ = l_Lean_Meta_Simp_mkContext___redArg(v_config_4691_, v___x_4692_, v_a_4693_, v___y_4703_, v___y_4705_, v___y_4706_);
if (lean_obj_tag(v___x_4708_) == 0)
{
lean_object* v_a_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; size_t v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; 
v_a_4709_ = lean_ctor_get(v___x_4708_, 0);
lean_inc(v_a_4709_);
lean_dec_ref(v___x_4708_);
v___x_4710_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1, &l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1);
lean_inc_n(v___x_4694_, 2);
v___x_4711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4711_, 0, v___x_4710_);
lean_ctor_set(v___x_4711_, 1, v___x_4694_);
v___x_4712_ = lean_unsigned_to_nat(32u);
v___x_4713_ = lean_mk_empty_array_with_capacity(v___x_4712_);
v___x_4714_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8);
v___x_4715_ = ((size_t)5ULL);
v___x_4716_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4716_, 0, v___x_4714_);
lean_ctor_set(v___x_4716_, 1, v___x_4713_);
lean_ctor_set(v___x_4716_, 2, v___x_4694_);
lean_ctor_set(v___x_4716_, 3, v___x_4694_);
lean_ctor_set_usize(v___x_4716_, 4, v___x_4715_);
v___x_4717_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4717_, 0, v___x_4710_);
lean_ctor_set(v___x_4717_, 1, v___x_4710_);
lean_ctor_set(v___x_4717_, 2, v___x_4710_);
lean_ctor_set(v___x_4717_, 3, v___x_4716_);
v___x_4718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4718_, 0, v___x_4711_);
lean_ctor_set(v___x_4718_, 1, v___x_4717_);
v___x_4719_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4719_, 0, v___f_4695_);
lean_ctor_set(v___x_4719_, 1, v___f_4696_);
lean_ctor_set(v___x_4719_, 2, v___f_4697_);
lean_ctor_set(v___x_4719_, 3, v___f_4698_);
lean_ctor_set(v___x_4719_, 4, v___f_4699_);
lean_ctor_set_uint8(v___x_4719_, sizeof(void*)*5, v_hasTrace_4700_);
v___x_4720_ = l_Lean_Meta_Simp_main(v_a_4701_, v_a_4709_, v___x_4718_, v___x_4719_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_);
if (lean_obj_tag(v___x_4720_) == 0)
{
lean_object* v_a_4721_; lean_object* v_fst_4722_; lean_object* v___x_4723_; 
v_a_4721_ = lean_ctor_get(v___x_4720_, 0);
lean_inc(v_a_4721_);
lean_dec_ref(v___x_4720_);
v_fst_4722_ = lean_ctor_get(v_a_4721_, 0);
lean_inc(v_fst_4722_);
lean_dec(v_a_4721_);
v___x_4723_ = l_Lean_Meta_Simp_Result_mkEqTrans(v___x_4702_, v_fst_4722_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_);
return v___x_4723_;
}
else
{
lean_object* v_a_4724_; lean_object* v___x_4726_; uint8_t v_isShared_4727_; uint8_t v_isSharedCheck_4731_; 
lean_dec_ref(v___x_4702_);
v_a_4724_ = lean_ctor_get(v___x_4720_, 0);
v_isSharedCheck_4731_ = !lean_is_exclusive(v___x_4720_);
if (v_isSharedCheck_4731_ == 0)
{
v___x_4726_ = v___x_4720_;
v_isShared_4727_ = v_isSharedCheck_4731_;
goto v_resetjp_4725_;
}
else
{
lean_inc(v_a_4724_);
lean_dec(v___x_4720_);
v___x_4726_ = lean_box(0);
v_isShared_4727_ = v_isSharedCheck_4731_;
goto v_resetjp_4725_;
}
v_resetjp_4725_:
{
lean_object* v___x_4729_; 
if (v_isShared_4727_ == 0)
{
v___x_4729_ = v___x_4726_;
goto v_reusejp_4728_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v_a_4724_);
v___x_4729_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4728_;
}
v_reusejp_4728_:
{
return v___x_4729_;
}
}
}
}
else
{
lean_object* v_a_4732_; lean_object* v___x_4734_; uint8_t v_isShared_4735_; uint8_t v_isSharedCheck_4739_; 
lean_dec_ref(v___x_4702_);
lean_dec_ref(v_a_4701_);
lean_dec_ref(v___f_4699_);
lean_dec_ref(v___f_4698_);
lean_dec_ref(v___f_4697_);
lean_dec_ref(v___f_4696_);
lean_dec_ref(v___f_4695_);
lean_dec(v___x_4694_);
v_a_4732_ = lean_ctor_get(v___x_4708_, 0);
v_isSharedCheck_4739_ = !lean_is_exclusive(v___x_4708_);
if (v_isSharedCheck_4739_ == 0)
{
v___x_4734_ = v___x_4708_;
v_isShared_4735_ = v_isSharedCheck_4739_;
goto v_resetjp_4733_;
}
else
{
lean_inc(v_a_4732_);
lean_dec(v___x_4708_);
v___x_4734_ = lean_box(0);
v_isShared_4735_ = v_isSharedCheck_4739_;
goto v_resetjp_4733_;
}
v_resetjp_4733_:
{
lean_object* v___x_4737_; 
if (v_isShared_4735_ == 0)
{
v___x_4737_ = v___x_4734_;
goto v_reusejp_4736_;
}
else
{
lean_object* v_reuseFailAlloc_4738_; 
v_reuseFailAlloc_4738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4738_, 0, v_a_4732_);
v___x_4737_ = v_reuseFailAlloc_4738_;
goto v_reusejp_4736_;
}
v_reusejp_4736_:
{
return v___x_4737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__14___boxed(lean_object** _args){
lean_object* v_config_4740_ = _args[0];
lean_object* v___x_4741_ = _args[1];
lean_object* v_a_4742_ = _args[2];
lean_object* v___x_4743_ = _args[3];
lean_object* v___f_4744_ = _args[4];
lean_object* v___f_4745_ = _args[5];
lean_object* v___f_4746_ = _args[6];
lean_object* v___f_4747_ = _args[7];
lean_object* v___f_4748_ = _args[8];
lean_object* v_hasTrace_4749_ = _args[9];
lean_object* v_a_4750_ = _args[10];
lean_object* v___x_4751_ = _args[11];
lean_object* v___y_4752_ = _args[12];
lean_object* v___y_4753_ = _args[13];
lean_object* v___y_4754_ = _args[14];
lean_object* v___y_4755_ = _args[15];
lean_object* v___y_4756_ = _args[16];
_start:
{
uint8_t v_hasTrace_boxed_4757_; lean_object* v_res_4758_; 
v_hasTrace_boxed_4757_ = lean_unbox(v_hasTrace_4749_);
v_res_4758_ = l_Lean_Elab_Tactic_NormCast_derive___lam__14(v_config_4740_, v___x_4741_, v_a_4742_, v___x_4743_, v___f_4744_, v___f_4745_, v___f_4746_, v___f_4747_, v___f_4748_, v_hasTrace_boxed_4757_, v_a_4750_, v___x_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_);
lean_dec(v___y_4755_);
lean_dec_ref(v___y_4754_);
lean_dec(v___y_4753_);
lean_dec_ref(v___y_4752_);
return v_res_4758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__15(lean_object* v_up_4759_, lean_object* v_config_4760_, lean_object* v___x_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v___x_4764_, lean_object* v___f_4765_, lean_object* v___f_4766_, lean_object* v___f_4767_, lean_object* v___f_4768_, uint8_t v_hasTrace_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_){
_start:
{
lean_object* v___x_4775_; 
v___x_4775_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v_up_4759_, v___y_4773_);
if (lean_obj_tag(v___x_4775_) == 0)
{
lean_object* v_a_4776_; lean_object* v___x_4777_; 
v_a_4776_ = lean_ctor_get(v___x_4775_, 0);
lean_inc(v_a_4776_);
lean_dec_ref(v___x_4775_);
v___x_4777_ = l_Lean_Meta_Simp_mkContext___redArg(v_config_4760_, v___x_4761_, v_a_4762_, v___y_4770_, v___y_4772_, v___y_4773_);
if (lean_obj_tag(v___x_4777_) == 0)
{
lean_object* v_a_4778_; lean_object* v_expr_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; size_t v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; 
v_a_4778_ = lean_ctor_get(v___x_4777_, 0);
lean_inc(v_a_4778_);
lean_dec_ref(v___x_4777_);
v_expr_4779_ = lean_ctor_get(v_a_4763_, 0);
v___x_4780_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_upwardAndElim___boxed), 10, 1);
lean_closure_set(v___x_4780_, 0, v_a_4776_);
v___x_4781_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1, &l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1_once, _init_l_Lean_Elab_Tactic_NormCast_derive___lam__7___closed__1);
lean_inc_n(v___x_4764_, 2);
v___x_4782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4782_, 0, v___x_4781_);
lean_ctor_set(v___x_4782_, 1, v___x_4764_);
v___x_4783_ = lean_unsigned_to_nat(32u);
v___x_4784_ = lean_mk_empty_array_with_capacity(v___x_4783_);
v___x_4785_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8, &l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsing___closed__8);
v___x_4786_ = ((size_t)5ULL);
v___x_4787_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4787_, 0, v___x_4785_);
lean_ctor_set(v___x_4787_, 1, v___x_4784_);
lean_ctor_set(v___x_4787_, 2, v___x_4764_);
lean_ctor_set(v___x_4787_, 3, v___x_4764_);
lean_ctor_set_usize(v___x_4787_, 4, v___x_4786_);
v___x_4788_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4788_, 0, v___x_4781_);
lean_ctor_set(v___x_4788_, 1, v___x_4781_);
lean_ctor_set(v___x_4788_, 2, v___x_4781_);
lean_ctor_set(v___x_4788_, 3, v___x_4787_);
v___x_4789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4789_, 0, v___x_4782_);
lean_ctor_set(v___x_4789_, 1, v___x_4788_);
v___x_4790_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4790_, 0, v___f_4765_);
lean_ctor_set(v___x_4790_, 1, v___x_4780_);
lean_ctor_set(v___x_4790_, 2, v___f_4766_);
lean_ctor_set(v___x_4790_, 3, v___f_4767_);
lean_ctor_set(v___x_4790_, 4, v___f_4768_);
lean_ctor_set_uint8(v___x_4790_, sizeof(void*)*5, v_hasTrace_4769_);
lean_inc_ref(v_expr_4779_);
v___x_4791_ = l_Lean_Meta_Simp_main(v_expr_4779_, v_a_4778_, v___x_4789_, v___x_4790_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_);
if (lean_obj_tag(v___x_4791_) == 0)
{
lean_object* v_a_4792_; lean_object* v_fst_4793_; lean_object* v___x_4794_; 
v_a_4792_ = lean_ctor_get(v___x_4791_, 0);
lean_inc(v_a_4792_);
lean_dec_ref(v___x_4791_);
v_fst_4793_ = lean_ctor_get(v_a_4792_, 0);
lean_inc(v_fst_4793_);
lean_dec(v_a_4792_);
v___x_4794_ = l_Lean_Meta_Simp_Result_mkEqTrans(v_a_4763_, v_fst_4793_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_);
return v___x_4794_;
}
else
{
lean_object* v_a_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_4802_; 
lean_dec_ref(v_a_4763_);
v_a_4795_ = lean_ctor_get(v___x_4791_, 0);
v_isSharedCheck_4802_ = !lean_is_exclusive(v___x_4791_);
if (v_isSharedCheck_4802_ == 0)
{
v___x_4797_ = v___x_4791_;
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_a_4795_);
lean_dec(v___x_4791_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_4802_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v___x_4800_; 
if (v_isShared_4798_ == 0)
{
v___x_4800_ = v___x_4797_;
goto v_reusejp_4799_;
}
else
{
lean_object* v_reuseFailAlloc_4801_; 
v_reuseFailAlloc_4801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4801_, 0, v_a_4795_);
v___x_4800_ = v_reuseFailAlloc_4801_;
goto v_reusejp_4799_;
}
v_reusejp_4799_:
{
return v___x_4800_;
}
}
}
}
else
{
lean_object* v_a_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4810_; 
lean_dec(v_a_4776_);
lean_dec_ref(v___f_4768_);
lean_dec_ref(v___f_4767_);
lean_dec_ref(v___f_4766_);
lean_dec_ref(v___f_4765_);
lean_dec(v___x_4764_);
lean_dec_ref(v_a_4763_);
v_a_4803_ = lean_ctor_get(v___x_4777_, 0);
v_isSharedCheck_4810_ = !lean_is_exclusive(v___x_4777_);
if (v_isSharedCheck_4810_ == 0)
{
v___x_4805_ = v___x_4777_;
v_isShared_4806_ = v_isSharedCheck_4810_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_a_4803_);
lean_dec(v___x_4777_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4810_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
lean_object* v___x_4808_; 
if (v_isShared_4806_ == 0)
{
v___x_4808_ = v___x_4805_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v_a_4803_);
v___x_4808_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
return v___x_4808_;
}
}
}
}
else
{
lean_object* v_a_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4818_; 
lean_dec_ref(v___f_4768_);
lean_dec_ref(v___f_4767_);
lean_dec_ref(v___f_4766_);
lean_dec_ref(v___f_4765_);
lean_dec(v___x_4764_);
lean_dec_ref(v_a_4763_);
lean_dec_ref(v_a_4762_);
lean_dec_ref(v___x_4761_);
lean_dec_ref(v_config_4760_);
v_a_4811_ = lean_ctor_get(v___x_4775_, 0);
v_isSharedCheck_4818_ = !lean_is_exclusive(v___x_4775_);
if (v_isSharedCheck_4818_ == 0)
{
v___x_4813_ = v___x_4775_;
v_isShared_4814_ = v_isSharedCheck_4818_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_a_4811_);
lean_dec(v___x_4775_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4818_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v___x_4816_; 
if (v_isShared_4814_ == 0)
{
v___x_4816_ = v___x_4813_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v_a_4811_);
v___x_4816_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4815_;
}
v_reusejp_4815_:
{
return v___x_4816_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__15___boxed(lean_object* v_up_4819_, lean_object* v_config_4820_, lean_object* v___x_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v___x_4824_, lean_object* v___f_4825_, lean_object* v___f_4826_, lean_object* v___f_4827_, lean_object* v___f_4828_, lean_object* v_hasTrace_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_){
_start:
{
uint8_t v_hasTrace_boxed_4835_; lean_object* v_res_4836_; 
v_hasTrace_boxed_4835_ = lean_unbox(v_hasTrace_4829_);
v_res_4836_ = l_Lean_Elab_Tactic_NormCast_derive___lam__15(v_up_4819_, v_config_4820_, v___x_4821_, v_a_4822_, v_a_4823_, v___x_4824_, v___f_4825_, v___f_4826_, v___f_4827_, v___f_4828_, v_hasTrace_boxed_4835_, v___y_4830_, v___y_4831_, v___y_4832_, v___y_4833_);
lean_dec(v___y_4833_);
lean_dec_ref(v___y_4832_);
lean_dec(v___y_4831_);
lean_dec_ref(v___y_4830_);
lean_dec_ref(v_up_4819_);
return v_res_4836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__16(lean_object* v___x_4837_, uint8_t v___x_4838_, lean_object* v___x_4839_, lean_object* v___x_4840_, lean_object* v_phase_4841_, lean_object* v_k_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_){
_start:
{
lean_object* v_options_4848_; uint8_t v_hasTrace_4849_; 
v_options_4848_ = lean_ctor_get(v___y_4845_, 2);
v_hasTrace_4849_ = lean_ctor_get_uint8(v_options_4848_, sizeof(void*)*1);
if (v_hasTrace_4849_ == 0)
{
lean_object* v___x_4850_; 
lean_dec_ref(v_phase_4841_);
lean_dec_ref(v___x_4839_);
lean_dec(v___x_4837_);
lean_inc(v___y_4846_);
lean_inc_ref(v___y_4845_);
lean_inc(v___y_4844_);
lean_inc_ref(v___y_4843_);
v___x_4850_ = lean_apply_5(v_k_4842_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_, lean_box(0));
return v___x_4850_;
}
else
{
lean_object* v_inheritedTraceOptions_4851_; lean_object* v___f_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; uint8_t v___x_4855_; lean_object* v___y_4857_; lean_object* v___y_4858_; lean_object* v_a_4859_; lean_object* v___y_4872_; lean_object* v___y_4873_; lean_object* v_a_4874_; 
v_inheritedTraceOptions_4851_ = lean_ctor_get(v___y_4845_, 13);
v___f_4852_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4852_, 0, v_phase_4841_);
v___x_4853_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__2));
lean_inc(v___x_4837_);
v___x_4854_ = l_Lean_Name_append(v___x_4853_, v___x_4837_);
v___x_4855_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4851_, v_options_4848_, v___x_4854_);
lean_dec(v___x_4854_);
if (v___x_4855_ == 0)
{
lean_object* v___x_4923_; uint8_t v___x_4924_; 
v___x_4923_ = l_Lean_trace_profiler;
v___x_4924_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_4848_, v___x_4923_);
if (v___x_4924_ == 0)
{
lean_object* v___x_4925_; 
lean_dec_ref(v___f_4852_);
lean_dec_ref(v___x_4839_);
lean_dec(v___x_4837_);
lean_inc(v___y_4846_);
lean_inc_ref(v___y_4845_);
lean_inc(v___y_4844_);
lean_inc_ref(v___y_4843_);
v___x_4925_ = lean_apply_5(v_k_4842_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_, lean_box(0));
return v___x_4925_;
}
else
{
goto v___jp_4883_;
}
}
else
{
goto v___jp_4883_;
}
v___jp_4856_:
{
lean_object* v___x_4860_; double v___x_4861_; double v___x_4862_; double v___x_4863_; double v___x_4864_; double v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; 
v___x_4860_ = lean_io_mono_nanos_now();
v___x_4861_ = lean_float_of_nat(v___y_4857_);
v___x_4862_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4);
v___x_4863_ = lean_float_div(v___x_4861_, v___x_4862_);
v___x_4864_ = lean_float_of_nat(v___x_4860_);
v___x_4865_ = lean_float_div(v___x_4864_, v___x_4862_);
v___x_4866_ = lean_box_float(v___x_4863_);
v___x_4867_ = lean_box_float(v___x_4865_);
v___x_4868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4868_, 0, v___x_4866_);
lean_ctor_set(v___x_4868_, 1, v___x_4867_);
v___x_4869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4869_, 0, v_a_4859_);
lean_ctor_set(v___x_4869_, 1, v___x_4868_);
v___x_4870_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4837_, v___x_4838_, v___x_4839_, v_options_4848_, v___x_4855_, v___y_4858_, v___f_4852_, v___x_4869_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_);
return v___x_4870_;
}
v___jp_4871_:
{
lean_object* v___x_4875_; double v___x_4876_; double v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; 
v___x_4875_ = lean_io_get_num_heartbeats();
v___x_4876_ = lean_float_of_nat(v___y_4873_);
v___x_4877_ = lean_float_of_nat(v___x_4875_);
v___x_4878_ = lean_box_float(v___x_4876_);
v___x_4879_ = lean_box_float(v___x_4877_);
v___x_4880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4880_, 0, v___x_4878_);
lean_ctor_set(v___x_4880_, 1, v___x_4879_);
v___x_4881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4881_, 0, v_a_4874_);
lean_ctor_set(v___x_4881_, 1, v___x_4880_);
v___x_4882_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4837_, v___x_4838_, v___x_4839_, v_options_4848_, v___x_4855_, v___y_4872_, v___f_4852_, v___x_4881_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_);
return v___x_4882_;
}
v___jp_4883_:
{
lean_object* v___x_4884_; lean_object* v_a_4885_; uint8_t v___x_4886_; 
v___x_4884_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___y_4846_);
v_a_4885_ = lean_ctor_get(v___x_4884_, 0);
lean_inc(v_a_4885_);
lean_dec_ref(v___x_4884_);
v___x_4886_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_4848_, v___x_4840_);
if (v___x_4886_ == 0)
{
lean_object* v___x_4887_; lean_object* v___x_4888_; 
v___x_4887_ = lean_io_mono_nanos_now();
lean_inc(v___y_4846_);
lean_inc_ref(v___y_4845_);
lean_inc(v___y_4844_);
lean_inc_ref(v___y_4843_);
v___x_4888_ = lean_apply_5(v_k_4842_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_, lean_box(0));
if (lean_obj_tag(v___x_4888_) == 0)
{
lean_object* v_a_4889_; lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_4896_; 
v_a_4889_ = lean_ctor_get(v___x_4888_, 0);
v_isSharedCheck_4896_ = !lean_is_exclusive(v___x_4888_);
if (v_isSharedCheck_4896_ == 0)
{
v___x_4891_ = v___x_4888_;
v_isShared_4892_ = v_isSharedCheck_4896_;
goto v_resetjp_4890_;
}
else
{
lean_inc(v_a_4889_);
lean_dec(v___x_4888_);
v___x_4891_ = lean_box(0);
v_isShared_4892_ = v_isSharedCheck_4896_;
goto v_resetjp_4890_;
}
v_resetjp_4890_:
{
lean_object* v___x_4894_; 
if (v_isShared_4892_ == 0)
{
lean_ctor_set_tag(v___x_4891_, 1);
v___x_4894_ = v___x_4891_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4895_; 
v_reuseFailAlloc_4895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4895_, 0, v_a_4889_);
v___x_4894_ = v_reuseFailAlloc_4895_;
goto v_reusejp_4893_;
}
v_reusejp_4893_:
{
v___y_4857_ = v___x_4887_;
v___y_4858_ = v_a_4885_;
v_a_4859_ = v___x_4894_;
goto v___jp_4856_;
}
}
}
else
{
lean_object* v_a_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4904_; 
v_a_4897_ = lean_ctor_get(v___x_4888_, 0);
v_isSharedCheck_4904_ = !lean_is_exclusive(v___x_4888_);
if (v_isSharedCheck_4904_ == 0)
{
v___x_4899_ = v___x_4888_;
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
else
{
lean_inc(v_a_4897_);
lean_dec(v___x_4888_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
lean_object* v___x_4902_; 
if (v_isShared_4900_ == 0)
{
lean_ctor_set_tag(v___x_4899_, 0);
v___x_4902_ = v___x_4899_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_a_4897_);
v___x_4902_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
v___y_4857_ = v___x_4887_;
v___y_4858_ = v_a_4885_;
v_a_4859_ = v___x_4902_;
goto v___jp_4856_;
}
}
}
}
else
{
lean_object* v___x_4905_; lean_object* v___x_4906_; 
v___x_4905_ = lean_io_get_num_heartbeats();
lean_inc(v___y_4846_);
lean_inc_ref(v___y_4845_);
lean_inc(v___y_4844_);
lean_inc_ref(v___y_4843_);
v___x_4906_ = lean_apply_5(v_k_4842_, v___y_4843_, v___y_4844_, v___y_4845_, v___y_4846_, lean_box(0));
if (lean_obj_tag(v___x_4906_) == 0)
{
lean_object* v_a_4907_; lean_object* v___x_4909_; uint8_t v_isShared_4910_; uint8_t v_isSharedCheck_4914_; 
v_a_4907_ = lean_ctor_get(v___x_4906_, 0);
v_isSharedCheck_4914_ = !lean_is_exclusive(v___x_4906_);
if (v_isSharedCheck_4914_ == 0)
{
v___x_4909_ = v___x_4906_;
v_isShared_4910_ = v_isSharedCheck_4914_;
goto v_resetjp_4908_;
}
else
{
lean_inc(v_a_4907_);
lean_dec(v___x_4906_);
v___x_4909_ = lean_box(0);
v_isShared_4910_ = v_isSharedCheck_4914_;
goto v_resetjp_4908_;
}
v_resetjp_4908_:
{
lean_object* v___x_4912_; 
if (v_isShared_4910_ == 0)
{
lean_ctor_set_tag(v___x_4909_, 1);
v___x_4912_ = v___x_4909_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4913_; 
v_reuseFailAlloc_4913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4913_, 0, v_a_4907_);
v___x_4912_ = v_reuseFailAlloc_4913_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
v___y_4872_ = v_a_4885_;
v___y_4873_ = v___x_4905_;
v_a_4874_ = v___x_4912_;
goto v___jp_4871_;
}
}
}
else
{
lean_object* v_a_4915_; lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4922_; 
v_a_4915_ = lean_ctor_get(v___x_4906_, 0);
v_isSharedCheck_4922_ = !lean_is_exclusive(v___x_4906_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4917_ = v___x_4906_;
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
else
{
lean_inc(v_a_4915_);
lean_dec(v___x_4906_);
v___x_4917_ = lean_box(0);
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
v_resetjp_4916_:
{
lean_object* v___x_4920_; 
if (v_isShared_4918_ == 0)
{
lean_ctor_set_tag(v___x_4917_, 0);
v___x_4920_ = v___x_4917_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v_a_4915_);
v___x_4920_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
v___y_4872_ = v_a_4885_;
v___y_4873_ = v___x_4905_;
v_a_4874_ = v___x_4920_;
goto v___jp_4871_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__16___boxed(lean_object* v___x_4926_, lean_object* v___x_4927_, lean_object* v___x_4928_, lean_object* v___x_4929_, lean_object* v_phase_4930_, lean_object* v_k_4931_, lean_object* v___y_4932_, lean_object* v___y_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_){
_start:
{
uint8_t v___x_36328__boxed_4937_; lean_object* v_res_4938_; 
v___x_36328__boxed_4937_ = lean_unbox(v___x_4927_);
v_res_4938_ = l_Lean_Elab_Tactic_NormCast_derive___lam__16(v___x_4926_, v___x_36328__boxed_4937_, v___x_4928_, v___x_4929_, v_phase_4930_, v_k_4931_, v___y_4932_, v___y_4933_, v___y_4934_, v___y_4935_);
lean_dec(v___y_4935_);
lean_dec_ref(v___y_4934_);
lean_dec(v___y_4933_);
lean_dec_ref(v___y_4932_);
lean_dec_ref(v___x_4929_);
return v_res_4938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__27(lean_object* v___x_4939_, uint8_t v_hasTrace_4940_, lean_object* v_phase_4941_, lean_object* v_k_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_, lean_object* v___y_4946_){
_start:
{
lean_object* v_options_4948_; uint8_t v_hasTrace_4949_; 
v_options_4948_ = lean_ctor_get(v___y_4945_, 2);
v_hasTrace_4949_ = lean_ctor_get_uint8(v_options_4948_, sizeof(void*)*1);
if (v_hasTrace_4949_ == 0)
{
lean_object* v___x_4950_; 
lean_dec_ref(v_phase_4941_);
lean_dec(v___x_4939_);
lean_inc(v___y_4946_);
lean_inc_ref(v___y_4945_);
lean_inc(v___y_4944_);
lean_inc_ref(v___y_4943_);
v___x_4950_ = lean_apply_5(v_k_4942_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_, lean_box(0));
return v___x_4950_;
}
else
{
lean_object* v_inheritedTraceOptions_4951_; lean_object* v___f_4952_; lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; uint8_t v___x_4956_; lean_object* v___y_4958_; lean_object* v___y_4959_; lean_object* v_a_4960_; lean_object* v___y_4973_; lean_object* v___y_4974_; lean_object* v_a_4975_; 
v_inheritedTraceOptions_4951_ = lean_ctor_get(v___y_4945_, 13);
v___f_4952_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__4___boxed), 7, 1);
lean_closure_set(v___f_4952_, 0, v_phase_4941_);
v___x_4953_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_4954_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__2));
lean_inc(v___x_4939_);
v___x_4955_ = l_Lean_Name_append(v___x_4954_, v___x_4939_);
v___x_4956_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4951_, v_options_4948_, v___x_4955_);
lean_dec(v___x_4955_);
if (v___x_4956_ == 0)
{
lean_object* v___x_5025_; uint8_t v___x_5026_; 
v___x_5025_ = l_Lean_trace_profiler;
v___x_5026_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_4948_, v___x_5025_);
if (v___x_5026_ == 0)
{
lean_object* v___x_5027_; 
lean_dec_ref(v___f_4952_);
lean_dec(v___x_4939_);
lean_inc(v___y_4946_);
lean_inc_ref(v___y_4945_);
lean_inc(v___y_4944_);
lean_inc_ref(v___y_4943_);
v___x_5027_ = lean_apply_5(v_k_4942_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_, lean_box(0));
return v___x_5027_;
}
else
{
goto v___jp_4984_;
}
}
else
{
goto v___jp_4984_;
}
v___jp_4957_:
{
lean_object* v___x_4961_; double v___x_4962_; double v___x_4963_; double v___x_4964_; double v___x_4965_; double v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; 
v___x_4961_ = lean_io_mono_nanos_now();
v___x_4962_ = lean_float_of_nat(v___y_4959_);
v___x_4963_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4);
v___x_4964_ = lean_float_div(v___x_4962_, v___x_4963_);
v___x_4965_ = lean_float_of_nat(v___x_4961_);
v___x_4966_ = lean_float_div(v___x_4965_, v___x_4963_);
v___x_4967_ = lean_box_float(v___x_4964_);
v___x_4968_ = lean_box_float(v___x_4966_);
v___x_4969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4969_, 0, v___x_4967_);
lean_ctor_set(v___x_4969_, 1, v___x_4968_);
v___x_4970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4970_, 0, v_a_4960_);
lean_ctor_set(v___x_4970_, 1, v___x_4969_);
v___x_4971_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4939_, v_hasTrace_4940_, v___x_4953_, v_options_4948_, v___x_4956_, v___y_4958_, v___f_4952_, v___x_4970_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_);
return v___x_4971_;
}
v___jp_4972_:
{
lean_object* v___x_4976_; double v___x_4977_; double v___x_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; 
v___x_4976_ = lean_io_get_num_heartbeats();
v___x_4977_ = lean_float_of_nat(v___y_4973_);
v___x_4978_ = lean_float_of_nat(v___x_4976_);
v___x_4979_ = lean_box_float(v___x_4977_);
v___x_4980_ = lean_box_float(v___x_4978_);
v___x_4981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4981_, 0, v___x_4979_);
lean_ctor_set(v___x_4981_, 1, v___x_4980_);
v___x_4982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4982_, 0, v_a_4975_);
lean_ctor_set(v___x_4982_, 1, v___x_4981_);
v___x_4983_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_4939_, v_hasTrace_4940_, v___x_4953_, v_options_4948_, v___x_4956_, v___y_4974_, v___f_4952_, v___x_4982_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_);
return v___x_4983_;
}
v___jp_4984_:
{
lean_object* v___x_4985_; lean_object* v_a_4986_; lean_object* v___x_4987_; uint8_t v___x_4988_; 
v___x_4985_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v___y_4946_);
v_a_4986_ = lean_ctor_get(v___x_4985_, 0);
lean_inc(v_a_4986_);
lean_dec_ref(v___x_4985_);
v___x_4987_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4988_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_4948_, v___x_4987_);
if (v___x_4988_ == 0)
{
lean_object* v___x_4989_; lean_object* v___x_4990_; 
v___x_4989_ = lean_io_mono_nanos_now();
lean_inc(v___y_4946_);
lean_inc_ref(v___y_4945_);
lean_inc(v___y_4944_);
lean_inc_ref(v___y_4943_);
v___x_4990_ = lean_apply_5(v_k_4942_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_, lean_box(0));
if (lean_obj_tag(v___x_4990_) == 0)
{
lean_object* v_a_4991_; lean_object* v___x_4993_; uint8_t v_isShared_4994_; uint8_t v_isSharedCheck_4998_; 
v_a_4991_ = lean_ctor_get(v___x_4990_, 0);
v_isSharedCheck_4998_ = !lean_is_exclusive(v___x_4990_);
if (v_isSharedCheck_4998_ == 0)
{
v___x_4993_ = v___x_4990_;
v_isShared_4994_ = v_isSharedCheck_4998_;
goto v_resetjp_4992_;
}
else
{
lean_inc(v_a_4991_);
lean_dec(v___x_4990_);
v___x_4993_ = lean_box(0);
v_isShared_4994_ = v_isSharedCheck_4998_;
goto v_resetjp_4992_;
}
v_resetjp_4992_:
{
lean_object* v___x_4996_; 
if (v_isShared_4994_ == 0)
{
lean_ctor_set_tag(v___x_4993_, 1);
v___x_4996_ = v___x_4993_;
goto v_reusejp_4995_;
}
else
{
lean_object* v_reuseFailAlloc_4997_; 
v_reuseFailAlloc_4997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4997_, 0, v_a_4991_);
v___x_4996_ = v_reuseFailAlloc_4997_;
goto v_reusejp_4995_;
}
v_reusejp_4995_:
{
v___y_4958_ = v_a_4986_;
v___y_4959_ = v___x_4989_;
v_a_4960_ = v___x_4996_;
goto v___jp_4957_;
}
}
}
else
{
lean_object* v_a_4999_; lean_object* v___x_5001_; uint8_t v_isShared_5002_; uint8_t v_isSharedCheck_5006_; 
v_a_4999_ = lean_ctor_get(v___x_4990_, 0);
v_isSharedCheck_5006_ = !lean_is_exclusive(v___x_4990_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_5001_ = v___x_4990_;
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
else
{
lean_inc(v_a_4999_);
lean_dec(v___x_4990_);
v___x_5001_ = lean_box(0);
v_isShared_5002_ = v_isSharedCheck_5006_;
goto v_resetjp_5000_;
}
v_resetjp_5000_:
{
lean_object* v___x_5004_; 
if (v_isShared_5002_ == 0)
{
lean_ctor_set_tag(v___x_5001_, 0);
v___x_5004_ = v___x_5001_;
goto v_reusejp_5003_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5005_, 0, v_a_4999_);
v___x_5004_ = v_reuseFailAlloc_5005_;
goto v_reusejp_5003_;
}
v_reusejp_5003_:
{
v___y_4958_ = v_a_4986_;
v___y_4959_ = v___x_4989_;
v_a_4960_ = v___x_5004_;
goto v___jp_4957_;
}
}
}
}
else
{
lean_object* v___x_5007_; lean_object* v___x_5008_; 
v___x_5007_ = lean_io_get_num_heartbeats();
lean_inc(v___y_4946_);
lean_inc_ref(v___y_4945_);
lean_inc(v___y_4944_);
lean_inc_ref(v___y_4943_);
v___x_5008_ = lean_apply_5(v_k_4942_, v___y_4943_, v___y_4944_, v___y_4945_, v___y_4946_, lean_box(0));
if (lean_obj_tag(v___x_5008_) == 0)
{
lean_object* v_a_5009_; lean_object* v___x_5011_; uint8_t v_isShared_5012_; uint8_t v_isSharedCheck_5016_; 
v_a_5009_ = lean_ctor_get(v___x_5008_, 0);
v_isSharedCheck_5016_ = !lean_is_exclusive(v___x_5008_);
if (v_isSharedCheck_5016_ == 0)
{
v___x_5011_ = v___x_5008_;
v_isShared_5012_ = v_isSharedCheck_5016_;
goto v_resetjp_5010_;
}
else
{
lean_inc(v_a_5009_);
lean_dec(v___x_5008_);
v___x_5011_ = lean_box(0);
v_isShared_5012_ = v_isSharedCheck_5016_;
goto v_resetjp_5010_;
}
v_resetjp_5010_:
{
lean_object* v___x_5014_; 
if (v_isShared_5012_ == 0)
{
lean_ctor_set_tag(v___x_5011_, 1);
v___x_5014_ = v___x_5011_;
goto v_reusejp_5013_;
}
else
{
lean_object* v_reuseFailAlloc_5015_; 
v_reuseFailAlloc_5015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5015_, 0, v_a_5009_);
v___x_5014_ = v_reuseFailAlloc_5015_;
goto v_reusejp_5013_;
}
v_reusejp_5013_:
{
v___y_4973_ = v___x_5007_;
v___y_4974_ = v_a_4986_;
v_a_4975_ = v___x_5014_;
goto v___jp_4972_;
}
}
}
else
{
lean_object* v_a_5017_; lean_object* v___x_5019_; uint8_t v_isShared_5020_; uint8_t v_isSharedCheck_5024_; 
v_a_5017_ = lean_ctor_get(v___x_5008_, 0);
v_isSharedCheck_5024_ = !lean_is_exclusive(v___x_5008_);
if (v_isSharedCheck_5024_ == 0)
{
v___x_5019_ = v___x_5008_;
v_isShared_5020_ = v_isSharedCheck_5024_;
goto v_resetjp_5018_;
}
else
{
lean_inc(v_a_5017_);
lean_dec(v___x_5008_);
v___x_5019_ = lean_box(0);
v_isShared_5020_ = v_isSharedCheck_5024_;
goto v_resetjp_5018_;
}
v_resetjp_5018_:
{
lean_object* v___x_5022_; 
if (v_isShared_5020_ == 0)
{
lean_ctor_set_tag(v___x_5019_, 0);
v___x_5022_ = v___x_5019_;
goto v_reusejp_5021_;
}
else
{
lean_object* v_reuseFailAlloc_5023_; 
v_reuseFailAlloc_5023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5023_, 0, v_a_5017_);
v___x_5022_ = v_reuseFailAlloc_5023_;
goto v_reusejp_5021_;
}
v_reusejp_5021_:
{
v___y_4973_ = v___x_5007_;
v___y_4974_ = v_a_4986_;
v_a_4975_ = v___x_5022_;
goto v___jp_4972_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___lam__27___boxed(lean_object* v___x_5028_, lean_object* v_hasTrace_5029_, lean_object* v_phase_5030_, lean_object* v_k_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_){
_start:
{
uint8_t v_hasTrace_boxed_5037_; lean_object* v_res_5038_; 
v_hasTrace_boxed_5037_ = lean_unbox(v_hasTrace_5029_);
v_res_5038_ = l_Lean_Elab_Tactic_NormCast_derive___lam__27(v___x_5028_, v_hasTrace_boxed_5037_, v_phase_5030_, v_k_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_);
lean_dec(v___y_5035_);
lean_dec_ref(v___y_5034_);
lean_dec(v___y_5033_);
lean_dec_ref(v___y_5032_);
return v_res_5038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive(lean_object* v_e_5057_, lean_object* v_config_5058_, lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_){
_start:
{
lean_object* v_options_5064_; lean_object* v_inheritedTraceOptions_5065_; uint8_t v_hasTrace_5066_; lean_object* v___x_5067_; 
v_options_5064_ = lean_ctor_get(v_a_5061_, 2);
v_inheritedTraceOptions_5065_ = lean_ctor_get(v_a_5061_, 13);
v_hasTrace_5066_ = lean_ctor_get_uint8(v_options_5064_, sizeof(void*)*1);
v___x_5067_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_initFn___closed__2_00___x40_Lean_Elab_Tactic_NormCast_1508164376____hygCtx___hyg_2_));
if (v_hasTrace_5066_ == 0)
{
lean_object* v___x_5068_; lean_object* v_a_5069_; lean_object* v___x_5070_; 
v___x_5068_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_e_5057_, v_a_5060_);
v_a_5069_ = lean_ctor_get(v___x_5068_, 0);
lean_inc(v_a_5069_);
lean_dec_ref(v___x_5068_);
v___x_5070_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_5062_);
if (lean_obj_tag(v___x_5070_) == 0)
{
lean_object* v_a_5071_; lean_object* v___f_5072_; lean_object* v___f_5073_; lean_object* v___x_5074_; lean_object* v___f_5075_; lean_object* v___f_5076_; uint8_t v___x_5077_; lean_object* v___f_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; lean_object* v___f_5084_; lean_object* v___x_5085_; 
v_a_5071_ = lean_ctor_get(v___x_5070_, 0);
lean_inc_n(v_a_5071_, 2);
lean_dec_ref(v___x_5070_);
v___f_5072_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__0));
v___f_5073_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__1));
v___x_5074_ = lean_box(0);
v___f_5075_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__2));
v___f_5076_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__3));
v___x_5077_ = 1;
v___f_5078_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__4));
lean_inc(v_a_5069_);
v___x_5079_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5079_, 0, v_a_5069_);
lean_ctor_set(v___x_5079_, 1, v___x_5074_);
lean_ctor_set_uint8(v___x_5079_, sizeof(void*)*2, v___x_5077_);
v___x_5080_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__5));
v___x_5081_ = lean_unsigned_to_nat(0u);
v___x_5082_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__6));
v___x_5083_ = lean_box(v___x_5077_);
lean_inc_ref(v_config_5058_);
v___f_5084_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__7___boxed), 17, 12);
lean_closure_set(v___f_5084_, 0, v_config_5058_);
lean_closure_set(v___f_5084_, 1, v___x_5082_);
lean_closure_set(v___f_5084_, 2, v_a_5071_);
lean_closure_set(v___f_5084_, 3, v___x_5081_);
lean_closure_set(v___f_5084_, 4, v___f_5072_);
lean_closure_set(v___f_5084_, 5, v___f_5078_);
lean_closure_set(v___f_5084_, 6, v___f_5075_);
lean_closure_set(v___f_5084_, 7, v___f_5073_);
lean_closure_set(v___f_5084_, 8, v___f_5076_);
lean_closure_set(v___f_5084_, 9, v___x_5083_);
lean_closure_set(v___f_5084_, 10, v_a_5069_);
lean_closure_set(v___f_5084_, 11, v___x_5079_);
v___x_5085_ = l_Lean_Elab_Tactic_NormCast_derive___lam__5(v___x_5067_, v___x_5077_, v___x_5080_, v___f_5084_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_);
if (lean_obj_tag(v___x_5085_) == 0)
{
lean_object* v_a_5086_; lean_object* v___x_5087_; lean_object* v_up_5088_; lean_object* v_squash_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___f_5092_; lean_object* v___x_5093_; 
v_a_5086_ = lean_ctor_get(v___x_5085_, 0);
lean_inc(v_a_5086_);
lean_dec_ref(v___x_5085_);
v___x_5087_ = l_Lean_Meta_NormCast_normCastExt;
v_up_5088_ = lean_ctor_get(v___x_5087_, 0);
v_squash_5089_ = lean_ctor_get(v___x_5087_, 2);
v___x_5090_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__7));
v___x_5091_ = lean_box(v___x_5077_);
lean_inc(v_a_5071_);
lean_inc_ref(v_config_5058_);
lean_inc_ref(v_up_5088_);
v___f_5092_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__12___boxed), 16, 11);
lean_closure_set(v___f_5092_, 0, v_up_5088_);
lean_closure_set(v___f_5092_, 1, v_config_5058_);
lean_closure_set(v___f_5092_, 2, v___x_5082_);
lean_closure_set(v___f_5092_, 3, v_a_5071_);
lean_closure_set(v___f_5092_, 4, v_a_5086_);
lean_closure_set(v___f_5092_, 5, v___x_5081_);
lean_closure_set(v___f_5092_, 6, v___f_5072_);
lean_closure_set(v___f_5092_, 7, v___f_5075_);
lean_closure_set(v___f_5092_, 8, v___f_5073_);
lean_closure_set(v___f_5092_, 9, v___f_5076_);
lean_closure_set(v___f_5092_, 10, v___x_5091_);
v___x_5093_ = l_Lean_Elab_Tactic_NormCast_derive___lam__5(v___x_5067_, v___x_5077_, v___x_5090_, v___f_5092_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_);
if (lean_obj_tag(v___x_5093_) == 0)
{
lean_object* v_a_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; 
v_a_5094_ = lean_ctor_get(v___x_5093_, 0);
lean_inc(v_a_5094_);
lean_dec_ref(v___x_5093_);
v___x_5095_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__9));
v___x_5096_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_5082_, v___x_5095_, v_hasTrace_5066_, v_a_5061_, v_a_5062_);
if (lean_obj_tag(v___x_5096_) == 0)
{
lean_object* v_a_5097_; lean_object* v___f_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; 
v_a_5097_ = lean_ctor_get(v___x_5096_, 0);
lean_inc(v_a_5097_);
lean_dec_ref(v___x_5096_);
lean_inc_ref(v_squash_5089_);
v___f_5098_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__8___boxed), 11, 6);
lean_closure_set(v___f_5098_, 0, v_squash_5089_);
lean_closure_set(v___f_5098_, 1, v_config_5058_);
lean_closure_set(v___f_5098_, 2, v_a_5071_);
lean_closure_set(v___f_5098_, 3, v_a_5094_);
lean_closure_set(v___f_5098_, 4, v___x_5081_);
lean_closure_set(v___f_5098_, 5, v_a_5097_);
v___x_5099_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__10));
v___x_5100_ = l_Lean_Elab_Tactic_NormCast_derive___lam__5(v___x_5067_, v___x_5077_, v___x_5099_, v___f_5098_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_);
return v___x_5100_;
}
else
{
lean_object* v_a_5101_; lean_object* v___x_5103_; uint8_t v_isShared_5104_; uint8_t v_isSharedCheck_5108_; 
lean_dec(v_a_5094_);
lean_dec(v_a_5071_);
lean_dec_ref(v_config_5058_);
v_a_5101_ = lean_ctor_get(v___x_5096_, 0);
v_isSharedCheck_5108_ = !lean_is_exclusive(v___x_5096_);
if (v_isSharedCheck_5108_ == 0)
{
v___x_5103_ = v___x_5096_;
v_isShared_5104_ = v_isSharedCheck_5108_;
goto v_resetjp_5102_;
}
else
{
lean_inc(v_a_5101_);
lean_dec(v___x_5096_);
v___x_5103_ = lean_box(0);
v_isShared_5104_ = v_isSharedCheck_5108_;
goto v_resetjp_5102_;
}
v_resetjp_5102_:
{
lean_object* v___x_5106_; 
if (v_isShared_5104_ == 0)
{
v___x_5106_ = v___x_5103_;
goto v_reusejp_5105_;
}
else
{
lean_object* v_reuseFailAlloc_5107_; 
v_reuseFailAlloc_5107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5107_, 0, v_a_5101_);
v___x_5106_ = v_reuseFailAlloc_5107_;
goto v_reusejp_5105_;
}
v_reusejp_5105_:
{
return v___x_5106_;
}
}
}
}
else
{
lean_dec(v_a_5071_);
lean_dec_ref(v_config_5058_);
return v___x_5093_;
}
}
else
{
lean_dec(v_a_5071_);
lean_dec_ref(v_config_5058_);
return v___x_5085_;
}
}
else
{
lean_object* v_a_5109_; lean_object* v___x_5111_; uint8_t v_isShared_5112_; uint8_t v_isSharedCheck_5116_; 
lean_dec(v_a_5069_);
lean_dec_ref(v_config_5058_);
v_a_5109_ = lean_ctor_get(v___x_5070_, 0);
v_isSharedCheck_5116_ = !lean_is_exclusive(v___x_5070_);
if (v_isSharedCheck_5116_ == 0)
{
v___x_5111_ = v___x_5070_;
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
else
{
lean_inc(v_a_5109_);
lean_dec(v___x_5070_);
v___x_5111_ = lean_box(0);
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
v_resetjp_5110_:
{
lean_object* v___x_5114_; 
if (v_isShared_5112_ == 0)
{
v___x_5114_ = v___x_5111_;
goto v_reusejp_5113_;
}
else
{
lean_object* v_reuseFailAlloc_5115_; 
v_reuseFailAlloc_5115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5115_, 0, v_a_5109_);
v___x_5114_ = v_reuseFailAlloc_5115_;
goto v_reusejp_5113_;
}
v_reusejp_5113_:
{
return v___x_5114_;
}
}
}
}
else
{
lean_object* v___f_5117_; lean_object* v___f_5118_; lean_object* v___f_5119_; lean_object* v___x_5120_; lean_object* v___x_5121_; uint8_t v___x_5122_; lean_object* v___y_5124_; lean_object* v___y_5125_; lean_object* v_a_5126_; lean_object* v___y_5136_; lean_object* v___y_5137_; lean_object* v_a_5138_; lean_object* v___y_5141_; lean_object* v___y_5142_; lean_object* v_a_5143_; lean_object* v___y_5156_; lean_object* v___y_5157_; lean_object* v_a_5158_; 
v___f_5117_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__1));
v___f_5118_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__0));
lean_inc_ref(v_e_5057_);
v___f_5119_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__18___boxed), 7, 1);
lean_closure_set(v___f_5119_, 0, v_e_5057_);
v___x_5120_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__0));
v___x_5121_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__3);
v___x_5122_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5065_, v_options_5064_, v___x_5121_);
if (v___x_5122_ == 0)
{
lean_object* v___x_5256_; uint8_t v___x_5257_; 
v___x_5256_ = l_Lean_trace_profiler;
v___x_5257_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_5064_, v___x_5256_);
if (v___x_5257_ == 0)
{
lean_object* v___x_5258_; lean_object* v_a_5259_; lean_object* v___x_5260_; 
lean_dec_ref(v___f_5119_);
v___x_5258_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_e_5057_, v_a_5060_);
v_a_5259_ = lean_ctor_get(v___x_5258_, 0);
lean_inc(v_a_5259_);
lean_dec_ref(v___x_5258_);
v___x_5260_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_5062_);
if (lean_obj_tag(v___x_5260_) == 0)
{
lean_object* v_a_5261_; lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___f_5264_; lean_object* v___f_5265_; lean_object* v___f_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; lean_object* v___x_5271_; lean_object* v___f_5272_; lean_object* v___x_5273_; 
v_a_5261_ = lean_ctor_get(v___x_5260_, 0);
lean_inc_n(v_a_5261_, 2);
lean_dec_ref(v___x_5260_);
v___x_5262_ = lean_box(0);
v___x_5263_ = lean_box(v_hasTrace_5066_);
v___f_5264_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__9___boxed), 11, 2);
lean_closure_set(v___f_5264_, 0, v___x_5262_);
lean_closure_set(v___f_5264_, 1, v___x_5263_);
v___f_5265_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__2));
v___f_5266_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__3));
lean_inc(v_a_5259_);
v___x_5267_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5267_, 0, v_a_5259_);
lean_ctor_set(v___x_5267_, 1, v___x_5262_);
lean_ctor_set_uint8(v___x_5267_, sizeof(void*)*2, v_hasTrace_5066_);
v___x_5268_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__5));
v___x_5269_ = lean_unsigned_to_nat(0u);
v___x_5270_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__6));
v___x_5271_ = lean_box(v_hasTrace_5066_);
lean_inc_ref(v_config_5058_);
v___f_5272_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__14___boxed), 17, 12);
lean_closure_set(v___f_5272_, 0, v_config_5058_);
lean_closure_set(v___f_5272_, 1, v___x_5270_);
lean_closure_set(v___f_5272_, 2, v_a_5261_);
lean_closure_set(v___f_5272_, 3, v___x_5269_);
lean_closure_set(v___f_5272_, 4, v___f_5118_);
lean_closure_set(v___f_5272_, 5, v___f_5264_);
lean_closure_set(v___f_5272_, 6, v___f_5265_);
lean_closure_set(v___f_5272_, 7, v___f_5117_);
lean_closure_set(v___f_5272_, 8, v___f_5266_);
lean_closure_set(v___f_5272_, 9, v___x_5271_);
lean_closure_set(v___f_5272_, 10, v_a_5259_);
lean_closure_set(v___f_5272_, 11, v___x_5267_);
v___x_5273_ = l_Lean_Elab_Tactic_NormCast_derive___lam__27(v___x_5067_, v_hasTrace_5066_, v___x_5268_, v___f_5272_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_);
if (lean_obj_tag(v___x_5273_) == 0)
{
lean_object* v_a_5274_; lean_object* v___x_5275_; lean_object* v_up_5276_; lean_object* v_squash_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___f_5280_; lean_object* v___x_5281_; 
v_a_5274_ = lean_ctor_get(v___x_5273_, 0);
lean_inc(v_a_5274_);
lean_dec_ref(v___x_5273_);
v___x_5275_ = l_Lean_Meta_NormCast_normCastExt;
v_up_5276_ = lean_ctor_get(v___x_5275_, 0);
v_squash_5277_ = lean_ctor_get(v___x_5275_, 2);
v___x_5278_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__7));
v___x_5279_ = lean_box(v_hasTrace_5066_);
lean_inc(v_a_5261_);
lean_inc_ref(v_config_5058_);
lean_inc_ref(v_up_5276_);
v___f_5280_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__15___boxed), 16, 11);
lean_closure_set(v___f_5280_, 0, v_up_5276_);
lean_closure_set(v___f_5280_, 1, v_config_5058_);
lean_closure_set(v___f_5280_, 2, v___x_5270_);
lean_closure_set(v___f_5280_, 3, v_a_5261_);
lean_closure_set(v___f_5280_, 4, v_a_5274_);
lean_closure_set(v___f_5280_, 5, v___x_5269_);
lean_closure_set(v___f_5280_, 6, v___f_5118_);
lean_closure_set(v___f_5280_, 7, v___f_5265_);
lean_closure_set(v___f_5280_, 8, v___f_5117_);
lean_closure_set(v___f_5280_, 9, v___f_5266_);
lean_closure_set(v___f_5280_, 10, v___x_5279_);
v___x_5281_ = l_Lean_Elab_Tactic_NormCast_derive___lam__27(v___x_5067_, v_hasTrace_5066_, v___x_5278_, v___f_5280_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_);
if (lean_obj_tag(v___x_5281_) == 0)
{
lean_object* v_a_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; 
v_a_5282_ = lean_ctor_get(v___x_5281_, 0);
lean_inc(v_a_5282_);
lean_dec_ref(v___x_5281_);
v___x_5283_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__9));
v___x_5284_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_5270_, v___x_5283_, v___x_5257_, v_a_5061_, v_a_5062_);
if (lean_obj_tag(v___x_5284_) == 0)
{
lean_object* v_a_5285_; lean_object* v___f_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; 
v_a_5285_ = lean_ctor_get(v___x_5284_, 0);
lean_inc(v_a_5285_);
lean_dec_ref(v___x_5284_);
lean_inc_ref(v_squash_5277_);
v___f_5286_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__8___boxed), 11, 6);
lean_closure_set(v___f_5286_, 0, v_squash_5277_);
lean_closure_set(v___f_5286_, 1, v_config_5058_);
lean_closure_set(v___f_5286_, 2, v_a_5261_);
lean_closure_set(v___f_5286_, 3, v_a_5282_);
lean_closure_set(v___f_5286_, 4, v___x_5269_);
lean_closure_set(v___f_5286_, 5, v_a_5285_);
v___x_5287_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__10));
v___x_5288_ = l_Lean_Elab_Tactic_NormCast_derive___lam__27(v___x_5067_, v_hasTrace_5066_, v___x_5287_, v___f_5286_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_);
return v___x_5288_;
}
else
{
lean_object* v_a_5289_; lean_object* v___x_5291_; uint8_t v_isShared_5292_; uint8_t v_isSharedCheck_5296_; 
lean_dec(v_a_5282_);
lean_dec(v_a_5261_);
lean_dec_ref(v_config_5058_);
v_a_5289_ = lean_ctor_get(v___x_5284_, 0);
v_isSharedCheck_5296_ = !lean_is_exclusive(v___x_5284_);
if (v_isSharedCheck_5296_ == 0)
{
v___x_5291_ = v___x_5284_;
v_isShared_5292_ = v_isSharedCheck_5296_;
goto v_resetjp_5290_;
}
else
{
lean_inc(v_a_5289_);
lean_dec(v___x_5284_);
v___x_5291_ = lean_box(0);
v_isShared_5292_ = v_isSharedCheck_5296_;
goto v_resetjp_5290_;
}
v_resetjp_5290_:
{
lean_object* v___x_5294_; 
if (v_isShared_5292_ == 0)
{
v___x_5294_ = v___x_5291_;
goto v_reusejp_5293_;
}
else
{
lean_object* v_reuseFailAlloc_5295_; 
v_reuseFailAlloc_5295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5295_, 0, v_a_5289_);
v___x_5294_ = v_reuseFailAlloc_5295_;
goto v_reusejp_5293_;
}
v_reusejp_5293_:
{
return v___x_5294_;
}
}
}
}
else
{
lean_dec(v_a_5261_);
lean_dec_ref(v_config_5058_);
return v___x_5281_;
}
}
else
{
lean_dec(v_a_5261_);
lean_dec_ref(v_config_5058_);
return v___x_5273_;
}
}
else
{
lean_object* v_a_5297_; lean_object* v___x_5299_; uint8_t v_isShared_5300_; uint8_t v_isSharedCheck_5304_; 
lean_dec(v_a_5259_);
lean_dec_ref(v_config_5058_);
v_a_5297_ = lean_ctor_get(v___x_5260_, 0);
v_isSharedCheck_5304_ = !lean_is_exclusive(v___x_5260_);
if (v_isSharedCheck_5304_ == 0)
{
v___x_5299_ = v___x_5260_;
v_isShared_5300_ = v_isSharedCheck_5304_;
goto v_resetjp_5298_;
}
else
{
lean_inc(v_a_5297_);
lean_dec(v___x_5260_);
v___x_5299_ = lean_box(0);
v_isShared_5300_ = v_isSharedCheck_5304_;
goto v_resetjp_5298_;
}
v_resetjp_5298_:
{
lean_object* v___x_5302_; 
if (v_isShared_5300_ == 0)
{
v___x_5302_ = v___x_5299_;
goto v_reusejp_5301_;
}
else
{
lean_object* v_reuseFailAlloc_5303_; 
v_reuseFailAlloc_5303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5303_, 0, v_a_5297_);
v___x_5302_ = v_reuseFailAlloc_5303_;
goto v_reusejp_5301_;
}
v_reusejp_5301_:
{
return v___x_5302_;
}
}
}
}
else
{
goto v___jp_5160_;
}
}
else
{
goto v___jp_5160_;
}
v___jp_5123_:
{
lean_object* v___x_5127_; double v___x_5128_; double v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; 
v___x_5127_ = lean_io_get_num_heartbeats();
v___x_5128_ = lean_float_of_nat(v___y_5125_);
v___x_5129_ = lean_float_of_nat(v___x_5127_);
v___x_5130_ = lean_box_float(v___x_5128_);
v___x_5131_ = lean_box_float(v___x_5129_);
v___x_5132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5132_, 0, v___x_5130_);
lean_ctor_set(v___x_5132_, 1, v___x_5131_);
v___x_5133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5133_, 0, v_a_5126_);
lean_ctor_set(v___x_5133_, 1, v___x_5132_);
v___x_5134_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_5067_, v_hasTrace_5066_, v___x_5120_, v_options_5064_, v___x_5122_, v___y_5124_, v___f_5119_, v___x_5133_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_);
return v___x_5134_;
}
v___jp_5135_:
{
lean_object* v___x_5139_; 
v___x_5139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5139_, 0, v_a_5138_);
v___y_5124_ = v___y_5136_;
v___y_5125_ = v___y_5137_;
v_a_5126_ = v___x_5139_;
goto v___jp_5123_;
}
v___jp_5140_:
{
lean_object* v___x_5144_; double v___x_5145_; double v___x_5146_; double v___x_5147_; double v___x_5148_; double v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; 
v___x_5144_ = lean_io_mono_nanos_now();
v___x_5145_ = lean_float_of_nat(v___y_5141_);
v___x_5146_ = lean_float_once(&l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4, &l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4_once, _init_l_Lean_Elab_Tactic_NormCast_proveEqUsingDown___closed__4);
v___x_5147_ = lean_float_div(v___x_5145_, v___x_5146_);
v___x_5148_ = lean_float_of_nat(v___x_5144_);
v___x_5149_ = lean_float_div(v___x_5148_, v___x_5146_);
v___x_5150_ = lean_box_float(v___x_5147_);
v___x_5151_ = lean_box_float(v___x_5149_);
v___x_5152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5152_, 0, v___x_5150_);
lean_ctor_set(v___x_5152_, 1, v___x_5151_);
v___x_5153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5153_, 0, v_a_5143_);
lean_ctor_set(v___x_5153_, 1, v___x_5152_);
v___x_5154_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Elab_Tactic_NormCast_splittingProcedure_spec__0(v___x_5067_, v_hasTrace_5066_, v___x_5120_, v_options_5064_, v___x_5122_, v___y_5142_, v___f_5119_, v___x_5153_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_);
return v___x_5154_;
}
v___jp_5155_:
{
lean_object* v___x_5159_; 
v___x_5159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5159_, 0, v_a_5158_);
v___y_5141_ = v___y_5156_;
v___y_5142_ = v___y_5157_;
v_a_5143_ = v___x_5159_;
goto v___jp_5140_;
}
v___jp_5160_:
{
lean_object* v___x_5161_; lean_object* v_a_5162_; lean_object* v___x_5163_; uint8_t v___x_5164_; 
v___x_5161_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__0___redArg(v_a_5062_);
v_a_5162_ = lean_ctor_get(v___x_5161_, 0);
lean_inc(v_a_5162_);
lean_dec_ref(v___x_5161_);
v___x_5163_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5164_ = l_Lean_Option_get___at___00Lean_Elab_Tactic_NormCast_proveEqUsingDown_spec__1(v_options_5064_, v___x_5163_);
if (v___x_5164_ == 0)
{
lean_object* v___x_5165_; lean_object* v___x_5166_; lean_object* v_a_5167_; lean_object* v___x_5168_; 
v___x_5165_ = lean_io_mono_nanos_now();
v___x_5166_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_e_5057_, v_a_5060_);
v_a_5167_ = lean_ctor_get(v___x_5166_, 0);
lean_inc(v_a_5167_);
lean_dec_ref(v___x_5166_);
v___x_5168_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_5062_);
if (lean_obj_tag(v___x_5168_) == 0)
{
lean_object* v_a_5169_; lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___f_5172_; lean_object* v___f_5173_; lean_object* v___f_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___f_5180_; lean_object* v___x_5181_; 
v_a_5169_ = lean_ctor_get(v___x_5168_, 0);
lean_inc_n(v_a_5169_, 2);
lean_dec_ref(v___x_5168_);
v___x_5170_ = lean_box(0);
v___x_5171_ = lean_box(v_hasTrace_5066_);
v___f_5172_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__9___boxed), 11, 2);
lean_closure_set(v___f_5172_, 0, v___x_5170_);
lean_closure_set(v___f_5172_, 1, v___x_5171_);
v___f_5173_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__2));
v___f_5174_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__3));
lean_inc(v_a_5167_);
v___x_5175_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5175_, 0, v_a_5167_);
lean_ctor_set(v___x_5175_, 1, v___x_5170_);
lean_ctor_set_uint8(v___x_5175_, sizeof(void*)*2, v_hasTrace_5066_);
v___x_5176_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__5));
v___x_5177_ = lean_unsigned_to_nat(0u);
v___x_5178_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__6));
v___x_5179_ = lean_box(v_hasTrace_5066_);
lean_inc_ref(v_config_5058_);
v___f_5180_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__14___boxed), 17, 12);
lean_closure_set(v___f_5180_, 0, v_config_5058_);
lean_closure_set(v___f_5180_, 1, v___x_5178_);
lean_closure_set(v___f_5180_, 2, v_a_5169_);
lean_closure_set(v___f_5180_, 3, v___x_5177_);
lean_closure_set(v___f_5180_, 4, v___f_5118_);
lean_closure_set(v___f_5180_, 5, v___f_5172_);
lean_closure_set(v___f_5180_, 6, v___f_5173_);
lean_closure_set(v___f_5180_, 7, v___f_5117_);
lean_closure_set(v___f_5180_, 8, v___f_5174_);
lean_closure_set(v___f_5180_, 9, v___x_5179_);
lean_closure_set(v___f_5180_, 10, v_a_5167_);
lean_closure_set(v___f_5180_, 11, v___x_5175_);
v___x_5181_ = l_Lean_Elab_Tactic_NormCast_derive___lam__10(v___x_5067_, v_hasTrace_5066_, v___x_5176_, v___f_5180_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_);
if (lean_obj_tag(v___x_5181_) == 0)
{
lean_object* v_a_5182_; lean_object* v___x_5183_; lean_object* v_up_5184_; lean_object* v_squash_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___f_5188_; lean_object* v___x_5189_; 
v_a_5182_ = lean_ctor_get(v___x_5181_, 0);
lean_inc(v_a_5182_);
lean_dec_ref(v___x_5181_);
v___x_5183_ = l_Lean_Meta_NormCast_normCastExt;
v_up_5184_ = lean_ctor_get(v___x_5183_, 0);
v_squash_5185_ = lean_ctor_get(v___x_5183_, 2);
v___x_5186_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__7));
v___x_5187_ = lean_box(v_hasTrace_5066_);
lean_inc(v_a_5169_);
lean_inc_ref(v_config_5058_);
lean_inc_ref(v_up_5184_);
v___f_5188_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__15___boxed), 16, 11);
lean_closure_set(v___f_5188_, 0, v_up_5184_);
lean_closure_set(v___f_5188_, 1, v_config_5058_);
lean_closure_set(v___f_5188_, 2, v___x_5178_);
lean_closure_set(v___f_5188_, 3, v_a_5169_);
lean_closure_set(v___f_5188_, 4, v_a_5182_);
lean_closure_set(v___f_5188_, 5, v___x_5177_);
lean_closure_set(v___f_5188_, 6, v___f_5118_);
lean_closure_set(v___f_5188_, 7, v___f_5173_);
lean_closure_set(v___f_5188_, 8, v___f_5117_);
lean_closure_set(v___f_5188_, 9, v___f_5174_);
lean_closure_set(v___f_5188_, 10, v___x_5187_);
v___x_5189_ = l_Lean_Elab_Tactic_NormCast_derive___lam__10(v___x_5067_, v_hasTrace_5066_, v___x_5186_, v___f_5188_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_);
if (lean_obj_tag(v___x_5189_) == 0)
{
lean_object* v_a_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; 
v_a_5190_ = lean_ctor_get(v___x_5189_, 0);
lean_inc(v_a_5190_);
lean_dec_ref(v___x_5189_);
v___x_5191_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__9));
v___x_5192_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_5178_, v___x_5191_, v___x_5164_, v_a_5061_, v_a_5062_);
if (lean_obj_tag(v___x_5192_) == 0)
{
lean_object* v_a_5193_; lean_object* v___f_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; 
v_a_5193_ = lean_ctor_get(v___x_5192_, 0);
lean_inc(v_a_5193_);
lean_dec_ref(v___x_5192_);
lean_inc_ref(v_squash_5185_);
v___f_5194_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__8___boxed), 11, 6);
lean_closure_set(v___f_5194_, 0, v_squash_5185_);
lean_closure_set(v___f_5194_, 1, v_config_5058_);
lean_closure_set(v___f_5194_, 2, v_a_5169_);
lean_closure_set(v___f_5194_, 3, v_a_5190_);
lean_closure_set(v___f_5194_, 4, v___x_5177_);
lean_closure_set(v___f_5194_, 5, v_a_5193_);
v___x_5195_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__10));
v___x_5196_ = l_Lean_Elab_Tactic_NormCast_derive___lam__10(v___x_5067_, v_hasTrace_5066_, v___x_5195_, v___f_5194_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_);
if (lean_obj_tag(v___x_5196_) == 0)
{
lean_object* v_a_5197_; lean_object* v___x_5199_; uint8_t v_isShared_5200_; uint8_t v_isSharedCheck_5204_; 
v_a_5197_ = lean_ctor_get(v___x_5196_, 0);
v_isSharedCheck_5204_ = !lean_is_exclusive(v___x_5196_);
if (v_isSharedCheck_5204_ == 0)
{
v___x_5199_ = v___x_5196_;
v_isShared_5200_ = v_isSharedCheck_5204_;
goto v_resetjp_5198_;
}
else
{
lean_inc(v_a_5197_);
lean_dec(v___x_5196_);
v___x_5199_ = lean_box(0);
v_isShared_5200_ = v_isSharedCheck_5204_;
goto v_resetjp_5198_;
}
v_resetjp_5198_:
{
lean_object* v___x_5202_; 
if (v_isShared_5200_ == 0)
{
lean_ctor_set_tag(v___x_5199_, 1);
v___x_5202_ = v___x_5199_;
goto v_reusejp_5201_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v_a_5197_);
v___x_5202_ = v_reuseFailAlloc_5203_;
goto v_reusejp_5201_;
}
v_reusejp_5201_:
{
v___y_5141_ = v___x_5165_;
v___y_5142_ = v_a_5162_;
v_a_5143_ = v___x_5202_;
goto v___jp_5140_;
}
}
}
else
{
lean_object* v_a_5205_; 
v_a_5205_ = lean_ctor_get(v___x_5196_, 0);
lean_inc(v_a_5205_);
lean_dec_ref(v___x_5196_);
v___y_5156_ = v___x_5165_;
v___y_5157_ = v_a_5162_;
v_a_5158_ = v_a_5205_;
goto v___jp_5155_;
}
}
else
{
lean_object* v_a_5206_; 
lean_dec(v_a_5190_);
lean_dec(v_a_5169_);
lean_dec_ref(v_config_5058_);
v_a_5206_ = lean_ctor_get(v___x_5192_, 0);
lean_inc(v_a_5206_);
lean_dec_ref(v___x_5192_);
v___y_5156_ = v___x_5165_;
v___y_5157_ = v_a_5162_;
v_a_5158_ = v_a_5206_;
goto v___jp_5155_;
}
}
else
{
lean_object* v_a_5207_; 
lean_dec(v_a_5169_);
lean_dec_ref(v_config_5058_);
v_a_5207_ = lean_ctor_get(v___x_5189_, 0);
lean_inc(v_a_5207_);
lean_dec_ref(v___x_5189_);
v___y_5156_ = v___x_5165_;
v___y_5157_ = v_a_5162_;
v_a_5158_ = v_a_5207_;
goto v___jp_5155_;
}
}
else
{
lean_object* v_a_5208_; 
lean_dec(v_a_5169_);
lean_dec_ref(v_config_5058_);
v_a_5208_ = lean_ctor_get(v___x_5181_, 0);
lean_inc(v_a_5208_);
lean_dec_ref(v___x_5181_);
v___y_5156_ = v___x_5165_;
v___y_5157_ = v_a_5162_;
v_a_5158_ = v_a_5208_;
goto v___jp_5155_;
}
}
else
{
lean_object* v_a_5209_; 
lean_dec(v_a_5167_);
lean_dec_ref(v_config_5058_);
v_a_5209_ = lean_ctor_get(v___x_5168_, 0);
lean_inc(v_a_5209_);
lean_dec_ref(v___x_5168_);
v___y_5156_ = v___x_5165_;
v___y_5157_ = v_a_5162_;
v_a_5158_ = v_a_5209_;
goto v___jp_5155_;
}
}
else
{
lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v_a_5212_; lean_object* v___x_5213_; 
v___x_5210_ = lean_io_get_num_heartbeats();
v___x_5211_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_e_5057_, v_a_5060_);
v_a_5212_ = lean_ctor_get(v___x_5211_, 0);
lean_inc(v_a_5212_);
lean_dec_ref(v___x_5211_);
v___x_5213_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_5062_);
if (lean_obj_tag(v___x_5213_) == 0)
{
lean_object* v_a_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___f_5217_; lean_object* v___f_5218_; lean_object* v___f_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___f_5225_; lean_object* v___x_5226_; 
v_a_5214_ = lean_ctor_get(v___x_5213_, 0);
lean_inc_n(v_a_5214_, 2);
lean_dec_ref(v___x_5213_);
v___x_5215_ = lean_box(0);
v___x_5216_ = lean_box(v___x_5164_);
v___f_5217_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__6___boxed), 11, 2);
lean_closure_set(v___f_5217_, 0, v___x_5215_);
lean_closure_set(v___f_5217_, 1, v___x_5216_);
v___f_5218_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__2));
v___f_5219_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__3));
lean_inc(v_a_5212_);
v___x_5220_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_5220_, 0, v_a_5212_);
lean_ctor_set(v___x_5220_, 1, v___x_5215_);
lean_ctor_set_uint8(v___x_5220_, sizeof(void*)*2, v___x_5164_);
v___x_5221_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__5));
v___x_5222_ = lean_unsigned_to_nat(0u);
v___x_5223_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__6));
v___x_5224_ = lean_box(v___x_5164_);
lean_inc_ref(v_config_5058_);
v___f_5225_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__7___boxed), 17, 12);
lean_closure_set(v___f_5225_, 0, v_config_5058_);
lean_closure_set(v___f_5225_, 1, v___x_5223_);
lean_closure_set(v___f_5225_, 2, v_a_5214_);
lean_closure_set(v___f_5225_, 3, v___x_5222_);
lean_closure_set(v___f_5225_, 4, v___f_5118_);
lean_closure_set(v___f_5225_, 5, v___f_5217_);
lean_closure_set(v___f_5225_, 6, v___f_5218_);
lean_closure_set(v___f_5225_, 7, v___f_5117_);
lean_closure_set(v___f_5225_, 8, v___f_5219_);
lean_closure_set(v___f_5225_, 9, v___x_5224_);
lean_closure_set(v___f_5225_, 10, v_a_5212_);
lean_closure_set(v___f_5225_, 11, v___x_5220_);
v___x_5226_ = l_Lean_Elab_Tactic_NormCast_derive___lam__16(v___x_5067_, v___x_5164_, v___x_5120_, v___x_5163_, v___x_5221_, v___f_5225_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_);
if (lean_obj_tag(v___x_5226_) == 0)
{
lean_object* v_a_5227_; lean_object* v___x_5228_; lean_object* v_up_5229_; lean_object* v_squash_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___f_5233_; lean_object* v___x_5234_; 
v_a_5227_ = lean_ctor_get(v___x_5226_, 0);
lean_inc(v_a_5227_);
lean_dec_ref(v___x_5226_);
v___x_5228_ = l_Lean_Meta_NormCast_normCastExt;
v_up_5229_ = lean_ctor_get(v___x_5228_, 0);
v_squash_5230_ = lean_ctor_get(v___x_5228_, 2);
v___x_5231_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__7));
v___x_5232_ = lean_box(v___x_5164_);
lean_inc(v_a_5214_);
lean_inc_ref(v_config_5058_);
lean_inc_ref(v_up_5229_);
v___f_5233_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__12___boxed), 16, 11);
lean_closure_set(v___f_5233_, 0, v_up_5229_);
lean_closure_set(v___f_5233_, 1, v_config_5058_);
lean_closure_set(v___f_5233_, 2, v___x_5223_);
lean_closure_set(v___f_5233_, 3, v_a_5214_);
lean_closure_set(v___f_5233_, 4, v_a_5227_);
lean_closure_set(v___f_5233_, 5, v___x_5222_);
lean_closure_set(v___f_5233_, 6, v___f_5118_);
lean_closure_set(v___f_5233_, 7, v___f_5218_);
lean_closure_set(v___f_5233_, 8, v___f_5117_);
lean_closure_set(v___f_5233_, 9, v___f_5219_);
lean_closure_set(v___f_5233_, 10, v___x_5232_);
v___x_5234_ = l_Lean_Elab_Tactic_NormCast_derive___lam__16(v___x_5067_, v___x_5164_, v___x_5120_, v___x_5163_, v___x_5231_, v___f_5233_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_);
if (lean_obj_tag(v___x_5234_) == 0)
{
lean_object* v_a_5235_; lean_object* v___x_5236_; uint8_t v___x_5237_; lean_object* v___x_5238_; 
v_a_5235_ = lean_ctor_get(v___x_5234_, 0);
lean_inc(v_a_5235_);
lean_dec_ref(v___x_5234_);
v___x_5236_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__9));
v___x_5237_ = 0;
v___x_5238_ = l_Lean_Meta_Simp_SimprocsArray_add(v___x_5223_, v___x_5236_, v___x_5237_, v_a_5061_, v_a_5062_);
if (lean_obj_tag(v___x_5238_) == 0)
{
lean_object* v_a_5239_; lean_object* v___f_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; 
v_a_5239_ = lean_ctor_get(v___x_5238_, 0);
lean_inc(v_a_5239_);
lean_dec_ref(v___x_5238_);
lean_inc_ref(v_squash_5230_);
v___f_5240_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_derive___lam__8___boxed), 11, 6);
lean_closure_set(v___f_5240_, 0, v_squash_5230_);
lean_closure_set(v___f_5240_, 1, v_config_5058_);
lean_closure_set(v___f_5240_, 2, v_a_5214_);
lean_closure_set(v___f_5240_, 3, v_a_5235_);
lean_closure_set(v___f_5240_, 4, v___x_5222_);
lean_closure_set(v___f_5240_, 5, v_a_5239_);
v___x_5241_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_derive___closed__10));
v___x_5242_ = l_Lean_Elab_Tactic_NormCast_derive___lam__16(v___x_5067_, v___x_5164_, v___x_5120_, v___x_5163_, v___x_5241_, v___f_5240_, v_a_5059_, v_a_5060_, v_a_5061_, v_a_5062_);
if (lean_obj_tag(v___x_5242_) == 0)
{
lean_object* v_a_5243_; lean_object* v___x_5245_; uint8_t v_isShared_5246_; uint8_t v_isSharedCheck_5250_; 
v_a_5243_ = lean_ctor_get(v___x_5242_, 0);
v_isSharedCheck_5250_ = !lean_is_exclusive(v___x_5242_);
if (v_isSharedCheck_5250_ == 0)
{
v___x_5245_ = v___x_5242_;
v_isShared_5246_ = v_isSharedCheck_5250_;
goto v_resetjp_5244_;
}
else
{
lean_inc(v_a_5243_);
lean_dec(v___x_5242_);
v___x_5245_ = lean_box(0);
v_isShared_5246_ = v_isSharedCheck_5250_;
goto v_resetjp_5244_;
}
v_resetjp_5244_:
{
lean_object* v___x_5248_; 
if (v_isShared_5246_ == 0)
{
lean_ctor_set_tag(v___x_5245_, 1);
v___x_5248_ = v___x_5245_;
goto v_reusejp_5247_;
}
else
{
lean_object* v_reuseFailAlloc_5249_; 
v_reuseFailAlloc_5249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5249_, 0, v_a_5243_);
v___x_5248_ = v_reuseFailAlloc_5249_;
goto v_reusejp_5247_;
}
v_reusejp_5247_:
{
v___y_5124_ = v_a_5162_;
v___y_5125_ = v___x_5210_;
v_a_5126_ = v___x_5248_;
goto v___jp_5123_;
}
}
}
else
{
lean_object* v_a_5251_; 
v_a_5251_ = lean_ctor_get(v___x_5242_, 0);
lean_inc(v_a_5251_);
lean_dec_ref(v___x_5242_);
v___y_5136_ = v_a_5162_;
v___y_5137_ = v___x_5210_;
v_a_5138_ = v_a_5251_;
goto v___jp_5135_;
}
}
else
{
lean_object* v_a_5252_; 
lean_dec(v_a_5235_);
lean_dec(v_a_5214_);
lean_dec_ref(v_config_5058_);
v_a_5252_ = lean_ctor_get(v___x_5238_, 0);
lean_inc(v_a_5252_);
lean_dec_ref(v___x_5238_);
v___y_5136_ = v_a_5162_;
v___y_5137_ = v___x_5210_;
v_a_5138_ = v_a_5252_;
goto v___jp_5135_;
}
}
else
{
lean_object* v_a_5253_; 
lean_dec(v_a_5214_);
lean_dec_ref(v_config_5058_);
v_a_5253_ = lean_ctor_get(v___x_5234_, 0);
lean_inc(v_a_5253_);
lean_dec_ref(v___x_5234_);
v___y_5136_ = v_a_5162_;
v___y_5137_ = v___x_5210_;
v_a_5138_ = v_a_5253_;
goto v___jp_5135_;
}
}
else
{
lean_object* v_a_5254_; 
lean_dec(v_a_5214_);
lean_dec_ref(v_config_5058_);
v_a_5254_ = lean_ctor_get(v___x_5226_, 0);
lean_inc(v_a_5254_);
lean_dec_ref(v___x_5226_);
v___y_5136_ = v_a_5162_;
v___y_5137_ = v___x_5210_;
v_a_5138_ = v_a_5254_;
goto v___jp_5135_;
}
}
else
{
lean_object* v_a_5255_; 
lean_dec(v_a_5212_);
lean_dec_ref(v_config_5058_);
v_a_5255_ = lean_ctor_get(v___x_5213_, 0);
lean_inc(v_a_5255_);
lean_dec_ref(v___x_5213_);
v___y_5136_ = v_a_5162_;
v___y_5137_ = v___x_5210_;
v_a_5138_ = v_a_5255_;
goto v___jp_5135_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_derive___boxed(lean_object* v_e_5305_, lean_object* v_config_5306_, lean_object* v_a_5307_, lean_object* v_a_5308_, lean_object* v_a_5309_, lean_object* v_a_5310_, lean_object* v_a_5311_){
_start:
{
lean_object* v_res_5312_; 
v_res_5312_ = l_Lean_Elab_Tactic_NormCast_derive(v_e_5305_, v_config_5306_, v_a_5307_, v_a_5308_, v_a_5309_, v_a_5310_);
lean_dec(v_a_5310_);
lean_dec_ref(v_a_5309_);
lean_dec(v_a_5308_);
lean_dec_ref(v_a_5307_);
return v_res_5312_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; 
v___x_5313_ = lean_box(0);
v___x_5314_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_5315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5315_, 0, v___x_5314_);
lean_ctor_set(v___x_5315_, 1, v___x_5313_);
return v___x_5315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg(){
_start:
{
lean_object* v___x_5317_; lean_object* v___x_5318_; 
v___x_5317_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0);
v___x_5318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5318_, 0, v___x_5317_);
return v___x_5318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___boxed(lean_object* v___y_5319_){
_start:
{
lean_object* v_res_5320_; 
v_res_5320_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg();
return v_res_5320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0(lean_object* v_00_u03b1_5321_, lean_object* v___y_5322_, lean_object* v___y_5323_, lean_object* v___y_5324_, lean_object* v___y_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_){
_start:
{
lean_object* v___x_5329_; 
v___x_5329_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg();
return v___x_5329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___boxed(lean_object* v_00_u03b1_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_, lean_object* v___y_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_){
_start:
{
lean_object* v_res_5338_; 
v_res_5338_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0(v_00_u03b1_5330_, v___y_5331_, v___y_5332_, v___y_5333_, v___y_5334_, v___y_5335_, v___y_5336_);
lean_dec(v___y_5336_);
lean_dec_ref(v___y_5335_);
lean_dec(v___y_5334_);
lean_dec_ref(v___y_5333_);
lean_dec(v___y_5332_);
lean_dec_ref(v___y_5331_);
return v_res_5338_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg(lean_object* v_e_5339_, lean_object* v___y_5340_){
_start:
{
uint8_t v___x_5342_; 
v___x_5342_ = l_Lean_Expr_hasMVar(v_e_5339_);
if (v___x_5342_ == 0)
{
lean_object* v___x_5343_; 
v___x_5343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5343_, 0, v_e_5339_);
return v___x_5343_;
}
else
{
lean_object* v___x_5344_; lean_object* v_mctx_5345_; lean_object* v___x_5346_; lean_object* v_fst_5347_; lean_object* v_snd_5348_; lean_object* v___x_5349_; lean_object* v_cache_5350_; lean_object* v_zetaDeltaFVarIds_5351_; lean_object* v_postponed_5352_; lean_object* v_diag_5353_; lean_object* v___x_5355_; uint8_t v_isShared_5356_; uint8_t v_isSharedCheck_5362_; 
v___x_5344_ = lean_st_ref_get(v___y_5340_);
v_mctx_5345_ = lean_ctor_get(v___x_5344_, 0);
lean_inc_ref(v_mctx_5345_);
lean_dec(v___x_5344_);
v___x_5346_ = l_Lean_instantiateMVarsCore(v_mctx_5345_, v_e_5339_);
v_fst_5347_ = lean_ctor_get(v___x_5346_, 0);
lean_inc(v_fst_5347_);
v_snd_5348_ = lean_ctor_get(v___x_5346_, 1);
lean_inc(v_snd_5348_);
lean_dec_ref(v___x_5346_);
v___x_5349_ = lean_st_ref_take(v___y_5340_);
v_cache_5350_ = lean_ctor_get(v___x_5349_, 1);
v_zetaDeltaFVarIds_5351_ = lean_ctor_get(v___x_5349_, 2);
v_postponed_5352_ = lean_ctor_get(v___x_5349_, 3);
v_diag_5353_ = lean_ctor_get(v___x_5349_, 4);
v_isSharedCheck_5362_ = !lean_is_exclusive(v___x_5349_);
if (v_isSharedCheck_5362_ == 0)
{
lean_object* v_unused_5363_; 
v_unused_5363_ = lean_ctor_get(v___x_5349_, 0);
lean_dec(v_unused_5363_);
v___x_5355_ = v___x_5349_;
v_isShared_5356_ = v_isSharedCheck_5362_;
goto v_resetjp_5354_;
}
else
{
lean_inc(v_diag_5353_);
lean_inc(v_postponed_5352_);
lean_inc(v_zetaDeltaFVarIds_5351_);
lean_inc(v_cache_5350_);
lean_dec(v___x_5349_);
v___x_5355_ = lean_box(0);
v_isShared_5356_ = v_isSharedCheck_5362_;
goto v_resetjp_5354_;
}
v_resetjp_5354_:
{
lean_object* v___x_5358_; 
if (v_isShared_5356_ == 0)
{
lean_ctor_set(v___x_5355_, 0, v_snd_5348_);
v___x_5358_ = v___x_5355_;
goto v_reusejp_5357_;
}
else
{
lean_object* v_reuseFailAlloc_5361_; 
v_reuseFailAlloc_5361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5361_, 0, v_snd_5348_);
lean_ctor_set(v_reuseFailAlloc_5361_, 1, v_cache_5350_);
lean_ctor_set(v_reuseFailAlloc_5361_, 2, v_zetaDeltaFVarIds_5351_);
lean_ctor_set(v_reuseFailAlloc_5361_, 3, v_postponed_5352_);
lean_ctor_set(v_reuseFailAlloc_5361_, 4, v_diag_5353_);
v___x_5358_ = v_reuseFailAlloc_5361_;
goto v_reusejp_5357_;
}
v_reusejp_5357_:
{
lean_object* v___x_5359_; lean_object* v___x_5360_; 
v___x_5359_ = lean_st_ref_set(v___y_5340_, v___x_5358_);
v___x_5360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5360_, 0, v_fst_5347_);
return v___x_5360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg___boxed(lean_object* v_e_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_){
_start:
{
lean_object* v_res_5367_; 
v_res_5367_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg(v_e_5364_, v___y_5365_);
lean_dec(v___y_5365_);
return v_res_5367_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1(lean_object* v_e_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_){
_start:
{
lean_object* v___x_5376_; 
v___x_5376_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg(v_e_5368_, v___y_5372_);
return v___x_5376_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___boxed(lean_object* v_e_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_){
_start:
{
lean_object* v_res_5385_; 
v_res_5385_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1(v_e_5377_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_);
lean_dec(v___y_5383_);
lean_dec_ref(v___y_5382_);
lean_dec(v___y_5381_);
lean_dec_ref(v___y_5380_);
lean_dec(v___y_5379_);
lean_dec_ref(v___y_5378_);
return v_res_5385_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__2(void){
_start:
{
lean_object* v___x_5389_; lean_object* v___x_5390_; 
v___x_5389_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__1));
v___x_5390_ = l_Lean_MessageData_ofFormat(v___x_5389_);
return v___x_5390_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5391_; lean_object* v___x_5392_; 
v___x_5391_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__2, &l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__2_once, _init_l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__2);
v___x_5392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5392_, 0, v___x_5391_);
return v___x_5392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0(uint8_t v___x_5393_, lean_object* v___x_5394_, lean_object* v_expectedType_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_){
_start:
{
lean_object* v___y_5404_; lean_object* v___y_5405_; lean_object* v___y_5406_; lean_object* v___y_5407_; lean_object* v___y_5408_; lean_object* v___y_5409_; lean_object* v___y_5410_; lean_object* v___y_5433_; lean_object* v___y_5434_; lean_object* v___y_5435_; lean_object* v___y_5436_; lean_object* v___y_5437_; lean_object* v___y_5438_; lean_object* v___y_5439_; lean_object* v___y_5440_; lean_object* v___y_5441_; lean_object* v___y_5476_; lean_object* v___y_5477_; lean_object* v___y_5478_; lean_object* v___y_5479_; lean_object* v___y_5480_; lean_object* v___y_5481_; lean_object* v___x_5526_; lean_object* v_a_5527_; uint8_t v___x_5528_; 
lean_inc_ref(v_expectedType_5395_);
v___x_5526_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg(v_expectedType_5395_, v___y_5399_);
v_a_5527_ = lean_ctor_get(v___x_5526_, 0);
lean_inc(v_a_5527_);
lean_dec_ref(v___x_5526_);
v___x_5528_ = l_Lean_Expr_hasExprMVar(v_a_5527_);
lean_dec(v_a_5527_);
if (v___x_5528_ == 0)
{
v___y_5476_ = v___y_5396_;
v___y_5477_ = v___y_5397_;
v___y_5478_ = v___y_5398_;
v___y_5479_ = v___y_5399_;
v___y_5480_ = v___y_5400_;
v___y_5481_ = v___y_5401_;
goto v___jp_5475_;
}
else
{
lean_object* v___x_5529_; 
v___x_5529_ = l_Lean_Elab_Term_tryPostpone(v___y_5396_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_);
if (lean_obj_tag(v___x_5529_) == 0)
{
lean_dec_ref(v___x_5529_);
v___y_5476_ = v___y_5396_;
v___y_5477_ = v___y_5397_;
v___y_5478_ = v___y_5398_;
v___y_5479_ = v___y_5399_;
v___y_5480_ = v___y_5400_;
v___y_5481_ = v___y_5401_;
goto v___jp_5475_;
}
else
{
lean_object* v_a_5530_; lean_object* v___x_5532_; uint8_t v_isShared_5533_; uint8_t v_isSharedCheck_5537_; 
lean_dec_ref(v_expectedType_5395_);
lean_dec(v___x_5394_);
v_a_5530_ = lean_ctor_get(v___x_5529_, 0);
v_isSharedCheck_5537_ = !lean_is_exclusive(v___x_5529_);
if (v_isSharedCheck_5537_ == 0)
{
v___x_5532_ = v___x_5529_;
v_isShared_5533_ = v_isSharedCheck_5537_;
goto v_resetjp_5531_;
}
else
{
lean_inc(v_a_5530_);
lean_dec(v___x_5529_);
v___x_5532_ = lean_box(0);
v_isShared_5533_ = v_isSharedCheck_5537_;
goto v_resetjp_5531_;
}
v_resetjp_5531_:
{
lean_object* v___x_5535_; 
if (v_isShared_5533_ == 0)
{
v___x_5535_ = v___x_5532_;
goto v_reusejp_5534_;
}
else
{
lean_object* v_reuseFailAlloc_5536_; 
v_reuseFailAlloc_5536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5536_, 0, v_a_5530_);
v___x_5535_ = v_reuseFailAlloc_5536_;
goto v_reusejp_5534_;
}
v_reusejp_5534_:
{
return v___x_5535_;
}
}
}
}
v___jp_5403_:
{
lean_object* v___x_5411_; 
v___x_5411_ = l_Lean_Meta_Simp_Result_mkEqSymm(v_expectedType_5395_, v___y_5406_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_);
if (lean_obj_tag(v___x_5411_) == 0)
{
lean_object* v_a_5412_; lean_object* v___x_5413_; 
v_a_5412_ = lean_ctor_get(v___x_5411_, 0);
lean_inc(v_a_5412_);
lean_dec_ref(v___x_5411_);
v___x_5413_ = l_Lean_Meta_Simp_Result_mkEqTrans(v___y_5404_, v_a_5412_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_);
if (lean_obj_tag(v___x_5413_) == 0)
{
lean_object* v_a_5414_; lean_object* v___x_5415_; 
v_a_5414_ = lean_ctor_get(v___x_5413_, 0);
lean_inc(v_a_5414_);
lean_dec_ref(v___x_5413_);
v___x_5415_ = l_Lean_Meta_Simp_Result_mkCast(v_a_5414_, v___y_5405_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_);
return v___x_5415_;
}
else
{
lean_object* v_a_5416_; lean_object* v___x_5418_; uint8_t v_isShared_5419_; uint8_t v_isSharedCheck_5423_; 
lean_dec_ref(v___y_5405_);
v_a_5416_ = lean_ctor_get(v___x_5413_, 0);
v_isSharedCheck_5423_ = !lean_is_exclusive(v___x_5413_);
if (v_isSharedCheck_5423_ == 0)
{
v___x_5418_ = v___x_5413_;
v_isShared_5419_ = v_isSharedCheck_5423_;
goto v_resetjp_5417_;
}
else
{
lean_inc(v_a_5416_);
lean_dec(v___x_5413_);
v___x_5418_ = lean_box(0);
v_isShared_5419_ = v_isSharedCheck_5423_;
goto v_resetjp_5417_;
}
v_resetjp_5417_:
{
lean_object* v___x_5421_; 
if (v_isShared_5419_ == 0)
{
v___x_5421_ = v___x_5418_;
goto v_reusejp_5420_;
}
else
{
lean_object* v_reuseFailAlloc_5422_; 
v_reuseFailAlloc_5422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5422_, 0, v_a_5416_);
v___x_5421_ = v_reuseFailAlloc_5422_;
goto v_reusejp_5420_;
}
v_reusejp_5420_:
{
return v___x_5421_;
}
}
}
}
else
{
lean_object* v_a_5424_; lean_object* v___x_5426_; uint8_t v_isShared_5427_; uint8_t v_isSharedCheck_5431_; 
lean_dec_ref(v___y_5405_);
lean_dec_ref(v___y_5404_);
v_a_5424_ = lean_ctor_get(v___x_5411_, 0);
v_isSharedCheck_5431_ = !lean_is_exclusive(v___x_5411_);
if (v_isSharedCheck_5431_ == 0)
{
v___x_5426_ = v___x_5411_;
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
else
{
lean_inc(v_a_5424_);
lean_dec(v___x_5411_);
v___x_5426_ = lean_box(0);
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
v_resetjp_5425_:
{
lean_object* v___x_5429_; 
if (v_isShared_5427_ == 0)
{
v___x_5429_ = v___x_5426_;
goto v_reusejp_5428_;
}
else
{
lean_object* v_reuseFailAlloc_5430_; 
v_reuseFailAlloc_5430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5430_, 0, v_a_5424_);
v___x_5429_ = v_reuseFailAlloc_5430_;
goto v_reusejp_5428_;
}
v_reusejp_5428_:
{
return v___x_5429_;
}
}
}
}
v___jp_5432_:
{
lean_object* v___x_5442_; 
v___x_5442_ = l_Lean_Elab_Tactic_NormCast_derive(v___y_5437_, v___y_5434_, v___y_5438_, v___y_5439_, v___y_5440_, v___y_5441_);
if (lean_obj_tag(v___x_5442_) == 0)
{
lean_object* v_a_5443_; lean_object* v_expr_5444_; lean_object* v___x_5445_; 
v_a_5443_ = lean_ctor_get(v___x_5442_, 0);
lean_inc(v_a_5443_);
lean_dec_ref(v___x_5442_);
v_expr_5444_ = lean_ctor_get(v_a_5443_, 0);
lean_inc_ref(v___y_5435_);
lean_inc_ref(v_expr_5444_);
v___x_5445_ = l_Lean_Meta_isExprDefEq(v_expr_5444_, v___y_5435_, v___y_5438_, v___y_5439_, v___y_5440_, v___y_5441_);
if (lean_obj_tag(v___x_5445_) == 0)
{
lean_object* v_a_5446_; uint8_t v___x_5447_; 
v_a_5446_ = lean_ctor_get(v___x_5445_, 0);
lean_inc(v_a_5446_);
lean_dec_ref(v___x_5445_);
v___x_5447_ = lean_unbox(v_a_5446_);
lean_dec(v_a_5446_);
if (v___x_5447_ == 0)
{
lean_object* v___x_5448_; lean_object* v___x_5449_; lean_object* v___x_5450_; 
v___x_5448_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__3, &l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__3_once, _init_l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___closed__3);
v___x_5449_ = lean_box(0);
lean_inc_ref(v___y_5433_);
lean_inc_ref(v_expr_5444_);
v___x_5450_ = l_Lean_Elab_Term_throwTypeMismatchError___redArg(v___x_5448_, v___y_5435_, v_expr_5444_, v___y_5433_, v___x_5449_, v___y_5438_, v___y_5439_, v___y_5440_, v___y_5441_);
if (lean_obj_tag(v___x_5450_) == 0)
{
lean_dec_ref(v___x_5450_);
v___y_5404_ = v_a_5443_;
v___y_5405_ = v___y_5433_;
v___y_5406_ = v___y_5436_;
v___y_5407_ = v___y_5438_;
v___y_5408_ = v___y_5439_;
v___y_5409_ = v___y_5440_;
v___y_5410_ = v___y_5441_;
goto v___jp_5403_;
}
else
{
lean_object* v_a_5451_; lean_object* v___x_5453_; uint8_t v_isShared_5454_; uint8_t v_isSharedCheck_5458_; 
lean_dec(v_a_5443_);
lean_dec_ref(v___y_5436_);
lean_dec_ref(v___y_5433_);
lean_dec_ref(v_expectedType_5395_);
v_a_5451_ = lean_ctor_get(v___x_5450_, 0);
v_isSharedCheck_5458_ = !lean_is_exclusive(v___x_5450_);
if (v_isSharedCheck_5458_ == 0)
{
v___x_5453_ = v___x_5450_;
v_isShared_5454_ = v_isSharedCheck_5458_;
goto v_resetjp_5452_;
}
else
{
lean_inc(v_a_5451_);
lean_dec(v___x_5450_);
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
lean_dec_ref(v___y_5435_);
v___y_5404_ = v_a_5443_;
v___y_5405_ = v___y_5433_;
v___y_5406_ = v___y_5436_;
v___y_5407_ = v___y_5438_;
v___y_5408_ = v___y_5439_;
v___y_5409_ = v___y_5440_;
v___y_5410_ = v___y_5441_;
goto v___jp_5403_;
}
}
else
{
lean_object* v_a_5459_; lean_object* v___x_5461_; uint8_t v_isShared_5462_; uint8_t v_isSharedCheck_5466_; 
lean_dec(v_a_5443_);
lean_dec_ref(v___y_5436_);
lean_dec_ref(v___y_5435_);
lean_dec_ref(v___y_5433_);
lean_dec_ref(v_expectedType_5395_);
v_a_5459_ = lean_ctor_get(v___x_5445_, 0);
v_isSharedCheck_5466_ = !lean_is_exclusive(v___x_5445_);
if (v_isSharedCheck_5466_ == 0)
{
v___x_5461_ = v___x_5445_;
v_isShared_5462_ = v_isSharedCheck_5466_;
goto v_resetjp_5460_;
}
else
{
lean_inc(v_a_5459_);
lean_dec(v___x_5445_);
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
lean_object* v_a_5467_; lean_object* v___x_5469_; uint8_t v_isShared_5470_; uint8_t v_isSharedCheck_5474_; 
lean_dec_ref(v___y_5436_);
lean_dec_ref(v___y_5435_);
lean_dec_ref(v___y_5433_);
lean_dec_ref(v_expectedType_5395_);
v_a_5467_ = lean_ctor_get(v___x_5442_, 0);
v_isSharedCheck_5474_ = !lean_is_exclusive(v___x_5442_);
if (v_isSharedCheck_5474_ == 0)
{
v___x_5469_ = v___x_5442_;
v_isShared_5470_ = v_isSharedCheck_5474_;
goto v_resetjp_5468_;
}
else
{
lean_inc(v_a_5467_);
lean_dec(v___x_5442_);
v___x_5469_ = lean_box(0);
v_isShared_5470_ = v_isSharedCheck_5474_;
goto v_resetjp_5468_;
}
v_resetjp_5468_:
{
lean_object* v___x_5472_; 
if (v_isShared_5470_ == 0)
{
v___x_5472_ = v___x_5469_;
goto v_reusejp_5471_;
}
else
{
lean_object* v_reuseFailAlloc_5473_; 
v_reuseFailAlloc_5473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5473_, 0, v_a_5467_);
v___x_5472_ = v_reuseFailAlloc_5473_;
goto v_reusejp_5471_;
}
v_reusejp_5471_:
{
return v___x_5472_;
}
}
}
}
v___jp_5475_:
{
lean_object* v___x_5482_; lean_object* v___x_5483_; uint8_t v___x_5484_; uint8_t v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; 
v___x_5482_ = lean_unsigned_to_nat(100000u);
v___x_5483_ = lean_unsigned_to_nat(2u);
v___x_5484_ = 0;
v___x_5485_ = 0;
v___x_5486_ = lean_box(0);
v___x_5487_ = lean_alloc_ctor(0, 3, 29);
lean_ctor_set(v___x_5487_, 0, v___x_5482_);
lean_ctor_set(v___x_5487_, 1, v___x_5483_);
lean_ctor_set(v___x_5487_, 2, v___x_5486_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3, v___x_5484_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 1, v___x_5393_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 2, v___x_5484_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 3, v___x_5484_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 4, v___x_5484_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 5, v___x_5484_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 6, v___x_5485_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 7, v___x_5484_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 8, v___x_5484_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 9, v___x_5484_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 10, v___x_5484_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 11, v___x_5484_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 12, v___x_5393_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 13, v___x_5393_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 14, v___x_5484_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 15, v___x_5484_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 16, v___x_5484_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 17, v___x_5393_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 18, v___x_5393_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 19, v___x_5393_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 20, v___x_5393_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 21, v___x_5393_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 22, v___x_5393_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 23, v___x_5393_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 24, v___x_5393_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 25, v___x_5393_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 26, v___x_5484_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 27, v___x_5484_);
lean_ctor_set_uint8(v___x_5487_, sizeof(void*)*3 + 28, v___x_5484_);
lean_inc_ref(v___x_5487_);
lean_inc_ref(v_expectedType_5395_);
v___x_5488_ = l_Lean_Elab_Tactic_NormCast_derive(v_expectedType_5395_, v___x_5487_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_);
if (lean_obj_tag(v___x_5488_) == 0)
{
lean_object* v_a_5489_; lean_object* v_expr_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; 
v_a_5489_ = lean_ctor_get(v___x_5488_, 0);
lean_inc(v_a_5489_);
lean_dec_ref(v___x_5488_);
v_expr_5490_ = lean_ctor_get(v_a_5489_, 0);
lean_inc_ref_n(v_expr_5490_, 2);
v___x_5491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5491_, 0, v_expr_5490_);
v___x_5492_ = l_Lean_Elab_Term_elabTerm(v___x_5394_, v___x_5491_, v___x_5393_, v___x_5393_, v___y_5476_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_);
if (lean_obj_tag(v___x_5492_) == 0)
{
lean_object* v_a_5493_; uint8_t v___x_5494_; lean_object* v___x_5495_; 
v_a_5493_ = lean_ctor_get(v___x_5492_, 0);
lean_inc(v_a_5493_);
lean_dec_ref(v___x_5492_);
v___x_5494_ = 0;
v___x_5495_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(v___x_5494_, v___x_5484_, v___y_5476_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_);
if (lean_obj_tag(v___x_5495_) == 0)
{
lean_object* v___x_5496_; 
lean_dec_ref(v___x_5495_);
lean_inc(v___y_5481_);
lean_inc_ref(v___y_5480_);
lean_inc(v___y_5479_);
lean_inc_ref(v___y_5478_);
lean_inc(v_a_5493_);
v___x_5496_ = lean_infer_type(v_a_5493_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_);
if (lean_obj_tag(v___x_5496_) == 0)
{
lean_object* v_a_5497_; lean_object* v___x_5498_; lean_object* v_a_5499_; uint8_t v___x_5500_; 
v_a_5497_ = lean_ctor_get(v___x_5496_, 0);
lean_inc(v_a_5497_);
lean_dec_ref(v___x_5496_);
v___x_5498_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__1___redArg(v_a_5497_, v___y_5479_);
v_a_5499_ = lean_ctor_get(v___x_5498_, 0);
lean_inc(v_a_5499_);
lean_dec_ref(v___x_5498_);
v___x_5500_ = l_Lean_Expr_hasExprMVar(v_a_5499_);
if (v___x_5500_ == 0)
{
v___y_5433_ = v_a_5493_;
v___y_5434_ = v___x_5487_;
v___y_5435_ = v_expr_5490_;
v___y_5436_ = v_a_5489_;
v___y_5437_ = v_a_5499_;
v___y_5438_ = v___y_5478_;
v___y_5439_ = v___y_5479_;
v___y_5440_ = v___y_5480_;
v___y_5441_ = v___y_5481_;
goto v___jp_5432_;
}
else
{
lean_object* v___x_5501_; 
v___x_5501_ = l_Lean_Elab_Term_tryPostpone(v___y_5476_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_);
if (lean_obj_tag(v___x_5501_) == 0)
{
lean_dec_ref(v___x_5501_);
v___y_5433_ = v_a_5493_;
v___y_5434_ = v___x_5487_;
v___y_5435_ = v_expr_5490_;
v___y_5436_ = v_a_5489_;
v___y_5437_ = v_a_5499_;
v___y_5438_ = v___y_5478_;
v___y_5439_ = v___y_5479_;
v___y_5440_ = v___y_5480_;
v___y_5441_ = v___y_5481_;
goto v___jp_5432_;
}
else
{
lean_object* v_a_5502_; lean_object* v___x_5504_; uint8_t v_isShared_5505_; uint8_t v_isSharedCheck_5509_; 
lean_dec(v_a_5499_);
lean_dec(v_a_5493_);
lean_dec_ref(v_expr_5490_);
lean_dec(v_a_5489_);
lean_dec_ref(v___x_5487_);
lean_dec_ref(v_expectedType_5395_);
v_a_5502_ = lean_ctor_get(v___x_5501_, 0);
v_isSharedCheck_5509_ = !lean_is_exclusive(v___x_5501_);
if (v_isSharedCheck_5509_ == 0)
{
v___x_5504_ = v___x_5501_;
v_isShared_5505_ = v_isSharedCheck_5509_;
goto v_resetjp_5503_;
}
else
{
lean_inc(v_a_5502_);
lean_dec(v___x_5501_);
v___x_5504_ = lean_box(0);
v_isShared_5505_ = v_isSharedCheck_5509_;
goto v_resetjp_5503_;
}
v_resetjp_5503_:
{
lean_object* v___x_5507_; 
if (v_isShared_5505_ == 0)
{
v___x_5507_ = v___x_5504_;
goto v_reusejp_5506_;
}
else
{
lean_object* v_reuseFailAlloc_5508_; 
v_reuseFailAlloc_5508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5508_, 0, v_a_5502_);
v___x_5507_ = v_reuseFailAlloc_5508_;
goto v_reusejp_5506_;
}
v_reusejp_5506_:
{
return v___x_5507_;
}
}
}
}
}
else
{
lean_dec(v_a_5493_);
lean_dec_ref(v_expr_5490_);
lean_dec(v_a_5489_);
lean_dec_ref(v___x_5487_);
lean_dec_ref(v_expectedType_5395_);
return v___x_5496_;
}
}
else
{
lean_object* v_a_5510_; lean_object* v___x_5512_; uint8_t v_isShared_5513_; uint8_t v_isSharedCheck_5517_; 
lean_dec(v_a_5493_);
lean_dec_ref(v_expr_5490_);
lean_dec(v_a_5489_);
lean_dec_ref(v___x_5487_);
lean_dec_ref(v_expectedType_5395_);
v_a_5510_ = lean_ctor_get(v___x_5495_, 0);
v_isSharedCheck_5517_ = !lean_is_exclusive(v___x_5495_);
if (v_isSharedCheck_5517_ == 0)
{
v___x_5512_ = v___x_5495_;
v_isShared_5513_ = v_isSharedCheck_5517_;
goto v_resetjp_5511_;
}
else
{
lean_inc(v_a_5510_);
lean_dec(v___x_5495_);
v___x_5512_ = lean_box(0);
v_isShared_5513_ = v_isSharedCheck_5517_;
goto v_resetjp_5511_;
}
v_resetjp_5511_:
{
lean_object* v___x_5515_; 
if (v_isShared_5513_ == 0)
{
v___x_5515_ = v___x_5512_;
goto v_reusejp_5514_;
}
else
{
lean_object* v_reuseFailAlloc_5516_; 
v_reuseFailAlloc_5516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5516_, 0, v_a_5510_);
v___x_5515_ = v_reuseFailAlloc_5516_;
goto v_reusejp_5514_;
}
v_reusejp_5514_:
{
return v___x_5515_;
}
}
}
}
else
{
lean_dec_ref(v_expr_5490_);
lean_dec(v_a_5489_);
lean_dec_ref(v___x_5487_);
lean_dec_ref(v_expectedType_5395_);
return v___x_5492_;
}
}
else
{
lean_object* v_a_5518_; lean_object* v___x_5520_; uint8_t v_isShared_5521_; uint8_t v_isSharedCheck_5525_; 
lean_dec_ref(v___x_5487_);
lean_dec_ref(v_expectedType_5395_);
lean_dec(v___x_5394_);
v_a_5518_ = lean_ctor_get(v___x_5488_, 0);
v_isSharedCheck_5525_ = !lean_is_exclusive(v___x_5488_);
if (v_isSharedCheck_5525_ == 0)
{
v___x_5520_ = v___x_5488_;
v_isShared_5521_ = v_isSharedCheck_5525_;
goto v_resetjp_5519_;
}
else
{
lean_inc(v_a_5518_);
lean_dec(v___x_5488_);
v___x_5520_ = lean_box(0);
v_isShared_5521_ = v_isSharedCheck_5525_;
goto v_resetjp_5519_;
}
v_resetjp_5519_:
{
lean_object* v___x_5523_; 
if (v_isShared_5521_ == 0)
{
v___x_5523_ = v___x_5520_;
goto v_reusejp_5522_;
}
else
{
lean_object* v_reuseFailAlloc_5524_; 
v_reuseFailAlloc_5524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5524_, 0, v_a_5518_);
v___x_5523_ = v_reuseFailAlloc_5524_;
goto v_reusejp_5522_;
}
v_reusejp_5522_:
{
return v___x_5523_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___boxed(lean_object* v___x_5538_, lean_object* v___x_5539_, lean_object* v_expectedType_5540_, lean_object* v___y_5541_, lean_object* v___y_5542_, lean_object* v___y_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_, lean_object* v___y_5546_, lean_object* v___y_5547_){
_start:
{
uint8_t v___x_4153__boxed_5548_; lean_object* v_res_5549_; 
v___x_4153__boxed_5548_ = lean_unbox(v___x_5538_);
v_res_5549_ = l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0(v___x_4153__boxed_5548_, v___x_5539_, v_expectedType_5540_, v___y_5541_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_, v___y_5546_);
lean_dec(v___y_5546_);
lean_dec_ref(v___y_5545_);
lean_dec(v___y_5544_);
lean_dec_ref(v___y_5543_);
lean_dec(v___y_5542_);
lean_dec_ref(v___y_5541_);
return v_res_5549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast(lean_object* v_stx_5554_, lean_object* v_expectedType_x3f_5555_, lean_object* v_a_5556_, lean_object* v_a_5557_, lean_object* v_a_5558_, lean_object* v_a_5559_, lean_object* v_a_5560_, lean_object* v_a_5561_){
_start:
{
lean_object* v___x_5563_; uint8_t v___x_5564_; 
v___x_5563_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabModCast___closed__1));
lean_inc(v_stx_5554_);
v___x_5564_ = l_Lean_Syntax_isOfKind(v_stx_5554_, v___x_5563_);
if (v___x_5564_ == 0)
{
lean_object* v___x_5565_; 
lean_dec(v_expectedType_x3f_5555_);
lean_dec(v_stx_5554_);
v___x_5565_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg();
return v___x_5565_;
}
else
{
lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___f_5569_; lean_object* v___x_5570_; 
v___x_5566_ = lean_unsigned_to_nat(1u);
v___x_5567_ = l_Lean_Syntax_getArg(v_stx_5554_, v___x_5566_);
lean_dec(v_stx_5554_);
v___x_5568_ = lean_box(v___x_5564_);
v___f_5569_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_elabModCast___lam__0___boxed), 10, 2);
lean_closure_set(v___f_5569_, 0, v___x_5568_);
lean_closure_set(v___f_5569_, 1, v___x_5567_);
v___x_5570_ = l_Lean_Elab_Term_withExpectedType(v_expectedType_x3f_5555_, v___f_5569_, v_a_5556_, v_a_5557_, v_a_5558_, v_a_5559_, v_a_5560_, v_a_5561_);
return v___x_5570_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabModCast___boxed(lean_object* v_stx_5571_, lean_object* v_expectedType_x3f_5572_, lean_object* v_a_5573_, lean_object* v_a_5574_, lean_object* v_a_5575_, lean_object* v_a_5576_, lean_object* v_a_5577_, lean_object* v_a_5578_, lean_object* v_a_5579_){
_start:
{
lean_object* v_res_5580_; 
v_res_5580_ = l_Lean_Elab_Tactic_NormCast_elabModCast(v_stx_5571_, v_expectedType_x3f_5572_, v_a_5573_, v_a_5574_, v_a_5575_, v_a_5576_, v_a_5577_, v_a_5578_);
lean_dec(v_a_5578_);
lean_dec_ref(v_a_5577_);
lean_dec(v_a_5576_);
lean_dec_ref(v_a_5575_);
lean_dec(v_a_5574_);
lean_dec_ref(v_a_5573_);
return v_res_5580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1(){
_start:
{
lean_object* v___x_5589_; lean_object* v___x_5590_; lean_object* v___x_5591_; lean_object* v___x_5592_; lean_object* v___x_5593_; 
v___x_5589_ = l_Lean_Elab_Term_termElabAttribute;
v___x_5590_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabModCast___closed__1));
v___x_5591_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1));
v___x_5592_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_elabModCast___boxed), 9, 0);
v___x_5593_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_5589_, v___x_5590_, v___x_5591_, v___x_5592_);
return v___x_5593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___boxed(lean_object* v_a_5594_){
_start:
{
lean_object* v_res_5595_; 
v_res_5595_ = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1();
return v_res_5595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3(){
_start:
{
lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; 
v___x_5622_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast__1___closed__1));
v___x_5623_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___closed__6));
v___x_5624_ = l_Lean_addBuiltinDeclarationRanges(v___x_5622_, v___x_5623_);
return v___x_5624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3___boxed(lean_object* v_a_5625_){
_start:
{
lean_object* v_res_5626_; 
v_res_5626_ = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabModCast___regBuiltin_Lean_Elab_Tactic_NormCast_elabModCast_declRange__3();
return v_res_5626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___lam__0(lean_object* v_cfg_5627_, lean_object* v___y_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_){
_start:
{
lean_object* v___x_5637_; 
v___x_5637_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_5629_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_);
if (lean_obj_tag(v___x_5637_) == 0)
{
lean_object* v_a_5638_; lean_object* v___x_5639_; 
v_a_5638_ = lean_ctor_get(v___x_5637_, 0);
lean_inc_n(v_a_5638_, 2);
lean_dec_ref(v___x_5637_);
v___x_5639_ = l_Lean_MVarId_getType(v_a_5638_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_);
if (lean_obj_tag(v___x_5639_) == 0)
{
lean_object* v_a_5640_; lean_object* v___x_5641_; lean_object* v_a_5642_; lean_object* v___x_5643_; 
v_a_5640_ = lean_ctor_get(v___x_5639_, 0);
lean_inc(v_a_5640_);
lean_dec_ref(v___x_5639_);
v___x_5641_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v_a_5640_, v___y_5633_);
v_a_5642_ = lean_ctor_get(v___x_5641_, 0);
lean_inc_n(v_a_5642_, 2);
lean_dec_ref(v___x_5641_);
v___x_5643_ = l_Lean_Elab_Tactic_NormCast_derive(v_a_5642_, v_cfg_5627_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_);
if (lean_obj_tag(v___x_5643_) == 0)
{
lean_object* v_a_5644_; lean_object* v___x_5645_; 
v_a_5644_ = lean_ctor_get(v___x_5643_, 0);
lean_inc(v_a_5644_);
lean_dec_ref(v___x_5643_);
v___x_5645_ = l_Lean_Meta_applySimpResultToTarget(v_a_5638_, v_a_5642_, v_a_5644_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_);
lean_dec(v_a_5642_);
if (lean_obj_tag(v___x_5645_) == 0)
{
lean_object* v_a_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; 
v_a_5646_ = lean_ctor_get(v___x_5645_, 0);
lean_inc(v_a_5646_);
lean_dec_ref(v___x_5645_);
v___x_5647_ = lean_box(0);
v___x_5648_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5648_, 0, v_a_5646_);
lean_ctor_set(v___x_5648_, 1, v___x_5647_);
v___x_5649_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_5648_, v___y_5629_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_);
return v___x_5649_;
}
else
{
lean_object* v_a_5650_; lean_object* v___x_5652_; uint8_t v_isShared_5653_; uint8_t v_isSharedCheck_5657_; 
v_a_5650_ = lean_ctor_get(v___x_5645_, 0);
v_isSharedCheck_5657_ = !lean_is_exclusive(v___x_5645_);
if (v_isSharedCheck_5657_ == 0)
{
v___x_5652_ = v___x_5645_;
v_isShared_5653_ = v_isSharedCheck_5657_;
goto v_resetjp_5651_;
}
else
{
lean_inc(v_a_5650_);
lean_dec(v___x_5645_);
v___x_5652_ = lean_box(0);
v_isShared_5653_ = v_isSharedCheck_5657_;
goto v_resetjp_5651_;
}
v_resetjp_5651_:
{
lean_object* v___x_5655_; 
if (v_isShared_5653_ == 0)
{
v___x_5655_ = v___x_5652_;
goto v_reusejp_5654_;
}
else
{
lean_object* v_reuseFailAlloc_5656_; 
v_reuseFailAlloc_5656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5656_, 0, v_a_5650_);
v___x_5655_ = v_reuseFailAlloc_5656_;
goto v_reusejp_5654_;
}
v_reusejp_5654_:
{
return v___x_5655_;
}
}
}
}
else
{
lean_object* v_a_5658_; lean_object* v___x_5660_; uint8_t v_isShared_5661_; uint8_t v_isSharedCheck_5665_; 
lean_dec(v_a_5642_);
lean_dec(v_a_5638_);
v_a_5658_ = lean_ctor_get(v___x_5643_, 0);
v_isSharedCheck_5665_ = !lean_is_exclusive(v___x_5643_);
if (v_isSharedCheck_5665_ == 0)
{
v___x_5660_ = v___x_5643_;
v_isShared_5661_ = v_isSharedCheck_5665_;
goto v_resetjp_5659_;
}
else
{
lean_inc(v_a_5658_);
lean_dec(v___x_5643_);
v___x_5660_ = lean_box(0);
v_isShared_5661_ = v_isSharedCheck_5665_;
goto v_resetjp_5659_;
}
v_resetjp_5659_:
{
lean_object* v___x_5663_; 
if (v_isShared_5661_ == 0)
{
v___x_5663_ = v___x_5660_;
goto v_reusejp_5662_;
}
else
{
lean_object* v_reuseFailAlloc_5664_; 
v_reuseFailAlloc_5664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5664_, 0, v_a_5658_);
v___x_5663_ = v_reuseFailAlloc_5664_;
goto v_reusejp_5662_;
}
v_reusejp_5662_:
{
return v___x_5663_;
}
}
}
}
else
{
lean_object* v_a_5666_; lean_object* v___x_5668_; uint8_t v_isShared_5669_; uint8_t v_isSharedCheck_5673_; 
lean_dec(v_a_5638_);
lean_dec_ref(v_cfg_5627_);
v_a_5666_ = lean_ctor_get(v___x_5639_, 0);
v_isSharedCheck_5673_ = !lean_is_exclusive(v___x_5639_);
if (v_isSharedCheck_5673_ == 0)
{
v___x_5668_ = v___x_5639_;
v_isShared_5669_ = v_isSharedCheck_5673_;
goto v_resetjp_5667_;
}
else
{
lean_inc(v_a_5666_);
lean_dec(v___x_5639_);
v___x_5668_ = lean_box(0);
v_isShared_5669_ = v_isSharedCheck_5673_;
goto v_resetjp_5667_;
}
v_resetjp_5667_:
{
lean_object* v___x_5671_; 
if (v_isShared_5669_ == 0)
{
v___x_5671_ = v___x_5668_;
goto v_reusejp_5670_;
}
else
{
lean_object* v_reuseFailAlloc_5672_; 
v_reuseFailAlloc_5672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5672_, 0, v_a_5666_);
v___x_5671_ = v_reuseFailAlloc_5672_;
goto v_reusejp_5670_;
}
v_reusejp_5670_:
{
return v___x_5671_;
}
}
}
}
else
{
lean_object* v_a_5674_; lean_object* v___x_5676_; uint8_t v_isShared_5677_; uint8_t v_isSharedCheck_5681_; 
lean_dec_ref(v_cfg_5627_);
v_a_5674_ = lean_ctor_get(v___x_5637_, 0);
v_isSharedCheck_5681_ = !lean_is_exclusive(v___x_5637_);
if (v_isSharedCheck_5681_ == 0)
{
v___x_5676_ = v___x_5637_;
v_isShared_5677_ = v_isSharedCheck_5681_;
goto v_resetjp_5675_;
}
else
{
lean_inc(v_a_5674_);
lean_dec(v___x_5637_);
v___x_5676_ = lean_box(0);
v_isShared_5677_ = v_isSharedCheck_5681_;
goto v_resetjp_5675_;
}
v_resetjp_5675_:
{
lean_object* v___x_5679_; 
if (v_isShared_5677_ == 0)
{
v___x_5679_ = v___x_5676_;
goto v_reusejp_5678_;
}
else
{
lean_object* v_reuseFailAlloc_5680_; 
v_reuseFailAlloc_5680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5680_, 0, v_a_5674_);
v___x_5679_ = v_reuseFailAlloc_5680_;
goto v_reusejp_5678_;
}
v_reusejp_5678_:
{
return v___x_5679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___lam__0___boxed(lean_object* v_cfg_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_, lean_object* v___y_5686_, lean_object* v___y_5687_, lean_object* v___y_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_){
_start:
{
lean_object* v_res_5692_; 
v_res_5692_ = l_Lean_Elab_Tactic_NormCast_normCastTarget___lam__0(v_cfg_5682_, v___y_5683_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_);
lean_dec(v___y_5690_);
lean_dec_ref(v___y_5689_);
lean_dec(v___y_5688_);
lean_dec_ref(v___y_5687_);
lean_dec(v___y_5686_);
lean_dec_ref(v___y_5685_);
lean_dec(v___y_5684_);
lean_dec_ref(v___y_5683_);
return v_res_5692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget(lean_object* v_cfg_5693_, lean_object* v_a_5694_, lean_object* v_a_5695_, lean_object* v_a_5696_, lean_object* v_a_5697_, lean_object* v_a_5698_, lean_object* v_a_5699_, lean_object* v_a_5700_, lean_object* v_a_5701_){
_start:
{
lean_object* v___f_5703_; lean_object* v___x_5704_; 
v___f_5703_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_normCastTarget___lam__0___boxed), 10, 1);
lean_closure_set(v___f_5703_, 0, v_cfg_5693_);
v___x_5704_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_5703_, v_a_5694_, v_a_5695_, v_a_5696_, v_a_5697_, v_a_5698_, v_a_5699_, v_a_5700_, v_a_5701_);
return v___x_5704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastTarget___boxed(lean_object* v_cfg_5705_, lean_object* v_a_5706_, lean_object* v_a_5707_, lean_object* v_a_5708_, lean_object* v_a_5709_, lean_object* v_a_5710_, lean_object* v_a_5711_, lean_object* v_a_5712_, lean_object* v_a_5713_, lean_object* v_a_5714_){
_start:
{
lean_object* v_res_5715_; 
v_res_5715_ = l_Lean_Elab_Tactic_NormCast_normCastTarget(v_cfg_5705_, v_a_5706_, v_a_5707_, v_a_5708_, v_a_5709_, v_a_5710_, v_a_5711_, v_a_5712_, v_a_5713_);
lean_dec(v_a_5713_);
lean_dec_ref(v_a_5712_);
lean_dec(v_a_5711_);
lean_dec_ref(v_a_5710_);
lean_dec(v_a_5709_);
lean_dec_ref(v_a_5708_);
lean_dec(v_a_5707_);
lean_dec_ref(v_a_5706_);
return v_res_5715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp___lam__0(lean_object* v_fvarId_5716_, lean_object* v_cfg_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_){
_start:
{
lean_object* v___x_5727_; 
v___x_5727_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_5719_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_);
if (lean_obj_tag(v___x_5727_) == 0)
{
lean_object* v_a_5728_; lean_object* v___x_5729_; 
v_a_5728_ = lean_ctor_get(v___x_5727_, 0);
lean_inc(v_a_5728_);
lean_dec_ref(v___x_5727_);
lean_inc(v_fvarId_5716_);
v___x_5729_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_5716_, v___y_5722_, v___y_5724_, v___y_5725_);
if (lean_obj_tag(v___x_5729_) == 0)
{
lean_object* v_a_5730_; lean_object* v___x_5731_; lean_object* v___x_5732_; lean_object* v_a_5733_; lean_object* v___x_5734_; 
v_a_5730_ = lean_ctor_get(v___x_5729_, 0);
lean_inc(v_a_5730_);
lean_dec_ref(v___x_5729_);
v___x_5731_ = l_Lean_LocalDecl_type(v_a_5730_);
lean_dec(v_a_5730_);
v___x_5732_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_NormCast_derive_spec__0___redArg(v___x_5731_, v___y_5723_);
v_a_5733_ = lean_ctor_get(v___x_5732_, 0);
lean_inc(v_a_5733_);
lean_dec_ref(v___x_5732_);
v___x_5734_ = l_Lean_Elab_Tactic_NormCast_derive(v_a_5733_, v_cfg_5717_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_);
if (lean_obj_tag(v___x_5734_) == 0)
{
lean_object* v_a_5735_; uint8_t v___x_5736_; lean_object* v___x_5737_; 
v_a_5735_ = lean_ctor_get(v___x_5734_, 0);
lean_inc(v_a_5735_);
lean_dec_ref(v___x_5734_);
v___x_5736_ = 0;
v___x_5737_ = l_Lean_Meta_applySimpResultToLocalDecl(v_a_5728_, v_fvarId_5716_, v_a_5735_, v___x_5736_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_);
if (lean_obj_tag(v___x_5737_) == 0)
{
lean_object* v_a_5738_; 
v_a_5738_ = lean_ctor_get(v___x_5737_, 0);
lean_inc(v_a_5738_);
lean_dec_ref(v___x_5737_);
if (lean_obj_tag(v_a_5738_) == 0)
{
lean_object* v___x_5739_; lean_object* v___x_5740_; 
v___x_5739_ = lean_box(0);
v___x_5740_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_5739_, v___y_5719_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_);
return v___x_5740_;
}
else
{
lean_object* v_val_5741_; lean_object* v_snd_5742_; lean_object* v___x_5744_; uint8_t v_isShared_5745_; uint8_t v_isSharedCheck_5751_; 
v_val_5741_ = lean_ctor_get(v_a_5738_, 0);
lean_inc(v_val_5741_);
lean_dec_ref(v_a_5738_);
v_snd_5742_ = lean_ctor_get(v_val_5741_, 1);
v_isSharedCheck_5751_ = !lean_is_exclusive(v_val_5741_);
if (v_isSharedCheck_5751_ == 0)
{
lean_object* v_unused_5752_; 
v_unused_5752_ = lean_ctor_get(v_val_5741_, 0);
lean_dec(v_unused_5752_);
v___x_5744_ = v_val_5741_;
v_isShared_5745_ = v_isSharedCheck_5751_;
goto v_resetjp_5743_;
}
else
{
lean_inc(v_snd_5742_);
lean_dec(v_val_5741_);
v___x_5744_ = lean_box(0);
v_isShared_5745_ = v_isSharedCheck_5751_;
goto v_resetjp_5743_;
}
v_resetjp_5743_:
{
lean_object* v___x_5746_; lean_object* v___x_5748_; 
v___x_5746_ = lean_box(0);
if (v_isShared_5745_ == 0)
{
lean_ctor_set_tag(v___x_5744_, 1);
lean_ctor_set(v___x_5744_, 1, v___x_5746_);
lean_ctor_set(v___x_5744_, 0, v_snd_5742_);
v___x_5748_ = v___x_5744_;
goto v_reusejp_5747_;
}
else
{
lean_object* v_reuseFailAlloc_5750_; 
v_reuseFailAlloc_5750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5750_, 0, v_snd_5742_);
lean_ctor_set(v_reuseFailAlloc_5750_, 1, v___x_5746_);
v___x_5748_ = v_reuseFailAlloc_5750_;
goto v_reusejp_5747_;
}
v_reusejp_5747_:
{
lean_object* v___x_5749_; 
v___x_5749_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(v___x_5748_, v___y_5719_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_);
return v___x_5749_;
}
}
}
}
else
{
lean_object* v_a_5753_; lean_object* v___x_5755_; uint8_t v_isShared_5756_; uint8_t v_isSharedCheck_5760_; 
v_a_5753_ = lean_ctor_get(v___x_5737_, 0);
v_isSharedCheck_5760_ = !lean_is_exclusive(v___x_5737_);
if (v_isSharedCheck_5760_ == 0)
{
v___x_5755_ = v___x_5737_;
v_isShared_5756_ = v_isSharedCheck_5760_;
goto v_resetjp_5754_;
}
else
{
lean_inc(v_a_5753_);
lean_dec(v___x_5737_);
v___x_5755_ = lean_box(0);
v_isShared_5756_ = v_isSharedCheck_5760_;
goto v_resetjp_5754_;
}
v_resetjp_5754_:
{
lean_object* v___x_5758_; 
if (v_isShared_5756_ == 0)
{
v___x_5758_ = v___x_5755_;
goto v_reusejp_5757_;
}
else
{
lean_object* v_reuseFailAlloc_5759_; 
v_reuseFailAlloc_5759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5759_, 0, v_a_5753_);
v___x_5758_ = v_reuseFailAlloc_5759_;
goto v_reusejp_5757_;
}
v_reusejp_5757_:
{
return v___x_5758_;
}
}
}
}
else
{
lean_object* v_a_5761_; lean_object* v___x_5763_; uint8_t v_isShared_5764_; uint8_t v_isSharedCheck_5768_; 
lean_dec(v_a_5728_);
lean_dec(v_fvarId_5716_);
v_a_5761_ = lean_ctor_get(v___x_5734_, 0);
v_isSharedCheck_5768_ = !lean_is_exclusive(v___x_5734_);
if (v_isSharedCheck_5768_ == 0)
{
v___x_5763_ = v___x_5734_;
v_isShared_5764_ = v_isSharedCheck_5768_;
goto v_resetjp_5762_;
}
else
{
lean_inc(v_a_5761_);
lean_dec(v___x_5734_);
v___x_5763_ = lean_box(0);
v_isShared_5764_ = v_isSharedCheck_5768_;
goto v_resetjp_5762_;
}
v_resetjp_5762_:
{
lean_object* v___x_5766_; 
if (v_isShared_5764_ == 0)
{
v___x_5766_ = v___x_5763_;
goto v_reusejp_5765_;
}
else
{
lean_object* v_reuseFailAlloc_5767_; 
v_reuseFailAlloc_5767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5767_, 0, v_a_5761_);
v___x_5766_ = v_reuseFailAlloc_5767_;
goto v_reusejp_5765_;
}
v_reusejp_5765_:
{
return v___x_5766_;
}
}
}
}
else
{
lean_object* v_a_5769_; lean_object* v___x_5771_; uint8_t v_isShared_5772_; uint8_t v_isSharedCheck_5776_; 
lean_dec(v_a_5728_);
lean_dec_ref(v_cfg_5717_);
lean_dec(v_fvarId_5716_);
v_a_5769_ = lean_ctor_get(v___x_5729_, 0);
v_isSharedCheck_5776_ = !lean_is_exclusive(v___x_5729_);
if (v_isSharedCheck_5776_ == 0)
{
v___x_5771_ = v___x_5729_;
v_isShared_5772_ = v_isSharedCheck_5776_;
goto v_resetjp_5770_;
}
else
{
lean_inc(v_a_5769_);
lean_dec(v___x_5729_);
v___x_5771_ = lean_box(0);
v_isShared_5772_ = v_isSharedCheck_5776_;
goto v_resetjp_5770_;
}
v_resetjp_5770_:
{
lean_object* v___x_5774_; 
if (v_isShared_5772_ == 0)
{
v___x_5774_ = v___x_5771_;
goto v_reusejp_5773_;
}
else
{
lean_object* v_reuseFailAlloc_5775_; 
v_reuseFailAlloc_5775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5775_, 0, v_a_5769_);
v___x_5774_ = v_reuseFailAlloc_5775_;
goto v_reusejp_5773_;
}
v_reusejp_5773_:
{
return v___x_5774_;
}
}
}
}
else
{
lean_object* v_a_5777_; lean_object* v___x_5779_; uint8_t v_isShared_5780_; uint8_t v_isSharedCheck_5784_; 
lean_dec_ref(v_cfg_5717_);
lean_dec(v_fvarId_5716_);
v_a_5777_ = lean_ctor_get(v___x_5727_, 0);
v_isSharedCheck_5784_ = !lean_is_exclusive(v___x_5727_);
if (v_isSharedCheck_5784_ == 0)
{
v___x_5779_ = v___x_5727_;
v_isShared_5780_ = v_isSharedCheck_5784_;
goto v_resetjp_5778_;
}
else
{
lean_inc(v_a_5777_);
lean_dec(v___x_5727_);
v___x_5779_ = lean_box(0);
v_isShared_5780_ = v_isSharedCheck_5784_;
goto v_resetjp_5778_;
}
v_resetjp_5778_:
{
lean_object* v___x_5782_; 
if (v_isShared_5780_ == 0)
{
v___x_5782_ = v___x_5779_;
goto v_reusejp_5781_;
}
else
{
lean_object* v_reuseFailAlloc_5783_; 
v_reuseFailAlloc_5783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5783_, 0, v_a_5777_);
v___x_5782_ = v_reuseFailAlloc_5783_;
goto v_reusejp_5781_;
}
v_reusejp_5781_:
{
return v___x_5782_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp___lam__0___boxed(lean_object* v_fvarId_5785_, lean_object* v_cfg_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_, lean_object* v___y_5789_, lean_object* v___y_5790_, lean_object* v___y_5791_, lean_object* v___y_5792_, lean_object* v___y_5793_, lean_object* v___y_5794_, lean_object* v___y_5795_){
_start:
{
lean_object* v_res_5796_; 
v_res_5796_ = l_Lean_Elab_Tactic_NormCast_normCastHyp___lam__0(v_fvarId_5785_, v_cfg_5786_, v___y_5787_, v___y_5788_, v___y_5789_, v___y_5790_, v___y_5791_, v___y_5792_, v___y_5793_, v___y_5794_);
lean_dec(v___y_5794_);
lean_dec_ref(v___y_5793_);
lean_dec(v___y_5792_);
lean_dec_ref(v___y_5791_);
lean_dec(v___y_5790_);
lean_dec_ref(v___y_5789_);
lean_dec(v___y_5788_);
lean_dec_ref(v___y_5787_);
return v_res_5796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp(lean_object* v_cfg_5797_, lean_object* v_fvarId_5798_, lean_object* v_a_5799_, lean_object* v_a_5800_, lean_object* v_a_5801_, lean_object* v_a_5802_, lean_object* v_a_5803_, lean_object* v_a_5804_, lean_object* v_a_5805_, lean_object* v_a_5806_){
_start:
{
lean_object* v___f_5808_; lean_object* v___x_5809_; 
v___f_5808_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_normCastHyp___lam__0___boxed), 11, 2);
lean_closure_set(v___f_5808_, 0, v_fvarId_5798_);
lean_closure_set(v___f_5808_, 1, v_cfg_5797_);
v___x_5809_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_5808_, v_a_5799_, v_a_5800_, v_a_5801_, v_a_5802_, v_a_5803_, v_a_5804_, v_a_5805_, v_a_5806_);
return v___x_5809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_normCastHyp___boxed(lean_object* v_cfg_5810_, lean_object* v_fvarId_5811_, lean_object* v_a_5812_, lean_object* v_a_5813_, lean_object* v_a_5814_, lean_object* v_a_5815_, lean_object* v_a_5816_, lean_object* v_a_5817_, lean_object* v_a_5818_, lean_object* v_a_5819_, lean_object* v_a_5820_){
_start:
{
lean_object* v_res_5821_; 
v_res_5821_ = l_Lean_Elab_Tactic_NormCast_normCastHyp(v_cfg_5810_, v_fvarId_5811_, v_a_5812_, v_a_5813_, v_a_5814_, v_a_5815_, v_a_5816_, v_a_5817_, v_a_5818_, v_a_5819_);
lean_dec(v_a_5819_);
lean_dec_ref(v_a_5818_);
lean_dec(v_a_5817_);
lean_dec_ref(v_a_5816_);
lean_dec(v_a_5815_);
lean_dec_ref(v_a_5814_);
lean_dec(v_a_5813_);
lean_dec_ref(v_a_5812_);
return v_res_5821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg(){
_start:
{
lean_object* v___x_5823_; lean_object* v___x_5824_; 
v___x_5823_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0);
v___x_5824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5824_, 0, v___x_5823_);
return v___x_5824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg___boxed(lean_object* v___y_5825_){
_start:
{
lean_object* v_res_5826_; 
v_res_5826_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg();
return v_res_5826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0(lean_object* v_00_u03b1_5827_, lean_object* v___y_5828_, lean_object* v___y_5829_, lean_object* v___y_5830_, lean_object* v___y_5831_, lean_object* v___y_5832_, lean_object* v___y_5833_, lean_object* v___y_5834_, lean_object* v___y_5835_){
_start:
{
lean_object* v___x_5837_; 
v___x_5837_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg();
return v___x_5837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___boxed(lean_object* v_00_u03b1_5838_, lean_object* v___y_5839_, lean_object* v___y_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_, lean_object* v___y_5844_, lean_object* v___y_5845_, lean_object* v___y_5846_, lean_object* v___y_5847_){
_start:
{
lean_object* v_res_5848_; 
v_res_5848_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0(v_00_u03b1_5838_, v___y_5839_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_, v___y_5845_, v___y_5846_);
lean_dec(v___y_5846_);
lean_dec_ref(v___y_5845_);
lean_dec(v___y_5844_);
lean_dec_ref(v___y_5843_);
lean_dec(v___y_5842_);
lean_dec_ref(v___y_5841_);
lean_dec(v___y_5840_);
lean_dec_ref(v___y_5839_);
return v_res_5848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1(lean_object* v_a_5849_, lean_object* v_as_5850_, size_t v_i_5851_, size_t v_stop_5852_, lean_object* v_b_5853_, lean_object* v___y_5854_, lean_object* v___y_5855_, lean_object* v___y_5856_, lean_object* v___y_5857_, lean_object* v___y_5858_, lean_object* v___y_5859_, lean_object* v___y_5860_, lean_object* v___y_5861_){
_start:
{
uint8_t v___x_5863_; 
v___x_5863_ = lean_usize_dec_eq(v_i_5851_, v_stop_5852_);
if (v___x_5863_ == 0)
{
lean_object* v___x_5864_; lean_object* v___x_5865_; 
v___x_5864_ = lean_array_uget_borrowed(v_as_5850_, v_i_5851_);
lean_inc(v___x_5864_);
lean_inc_ref(v_a_5849_);
v___x_5865_ = l_Lean_Elab_Tactic_NormCast_normCastHyp(v_a_5849_, v___x_5864_, v___y_5854_, v___y_5855_, v___y_5856_, v___y_5857_, v___y_5858_, v___y_5859_, v___y_5860_, v___y_5861_);
if (lean_obj_tag(v___x_5865_) == 0)
{
lean_object* v_a_5866_; size_t v___x_5867_; size_t v___x_5868_; 
v_a_5866_ = lean_ctor_get(v___x_5865_, 0);
lean_inc(v_a_5866_);
lean_dec_ref(v___x_5865_);
v___x_5867_ = ((size_t)1ULL);
v___x_5868_ = lean_usize_add(v_i_5851_, v___x_5867_);
v_i_5851_ = v___x_5868_;
v_b_5853_ = v_a_5866_;
goto _start;
}
else
{
lean_dec_ref(v_a_5849_);
return v___x_5865_;
}
}
else
{
lean_object* v___x_5870_; 
lean_dec_ref(v_a_5849_);
v___x_5870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5870_, 0, v_b_5853_);
return v___x_5870_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1___boxed(lean_object* v_a_5871_, lean_object* v_as_5872_, lean_object* v_i_5873_, lean_object* v_stop_5874_, lean_object* v_b_5875_, lean_object* v___y_5876_, lean_object* v___y_5877_, lean_object* v___y_5878_, lean_object* v___y_5879_, lean_object* v___y_5880_, lean_object* v___y_5881_, lean_object* v___y_5882_, lean_object* v___y_5883_, lean_object* v___y_5884_){
_start:
{
size_t v_i_boxed_5885_; size_t v_stop_boxed_5886_; lean_object* v_res_5887_; 
v_i_boxed_5885_ = lean_unbox_usize(v_i_5873_);
lean_dec(v_i_5873_);
v_stop_boxed_5886_ = lean_unbox_usize(v_stop_5874_);
lean_dec(v_stop_5874_);
v_res_5887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1(v_a_5871_, v_as_5872_, v_i_boxed_5885_, v_stop_boxed_5886_, v_b_5875_, v___y_5876_, v___y_5877_, v___y_5878_, v___y_5879_, v___y_5880_, v___y_5881_, v___y_5882_, v___y_5883_);
lean_dec(v___y_5883_);
lean_dec_ref(v___y_5882_);
lean_dec(v___y_5881_);
lean_dec_ref(v___y_5880_);
lean_dec(v___y_5879_);
lean_dec_ref(v___y_5878_);
lean_dec(v___y_5877_);
lean_dec_ref(v___y_5876_);
lean_dec_ref(v_as_5872_);
return v_res_5887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lam__0(lean_object* v___y_5888_, lean_object* v_a_5889_, lean_object* v___x_5890_, lean_object* v___y_5891_, lean_object* v___y_5892_, lean_object* v___y_5893_, lean_object* v___y_5894_, lean_object* v___y_5895_, lean_object* v___y_5896_, lean_object* v___y_5897_, lean_object* v___y_5898_){
_start:
{
if (lean_obj_tag(v___y_5888_) == 0)
{
lean_object* v___x_5900_; 
lean_inc_ref(v_a_5889_);
v___x_5900_ = l_Lean_Elab_Tactic_NormCast_normCastTarget(v_a_5889_, v___y_5891_, v___y_5892_, v___y_5893_, v___y_5894_, v___y_5895_, v___y_5896_, v___y_5897_, v___y_5898_);
if (lean_obj_tag(v___x_5900_) == 0)
{
lean_object* v___x_5901_; 
lean_dec_ref(v___x_5900_);
v___x_5901_ = l_Lean_Elab_Tactic_getMainGoal___redArg(v___y_5892_, v___y_5895_, v___y_5896_, v___y_5897_, v___y_5898_);
if (lean_obj_tag(v___x_5901_) == 0)
{
lean_object* v_a_5902_; lean_object* v___x_5903_; 
v_a_5902_ = lean_ctor_get(v___x_5901_, 0);
lean_inc(v_a_5902_);
lean_dec_ref(v___x_5901_);
v___x_5903_ = l_Lean_MVarId_getNondepPropHyps(v_a_5902_, v___y_5895_, v___y_5896_, v___y_5897_, v___y_5898_);
if (lean_obj_tag(v___x_5903_) == 0)
{
lean_object* v_a_5904_; lean_object* v___x_5906_; uint8_t v_isShared_5907_; uint8_t v_isSharedCheck_5924_; 
v_a_5904_ = lean_ctor_get(v___x_5903_, 0);
v_isSharedCheck_5924_ = !lean_is_exclusive(v___x_5903_);
if (v_isSharedCheck_5924_ == 0)
{
v___x_5906_ = v___x_5903_;
v_isShared_5907_ = v_isSharedCheck_5924_;
goto v_resetjp_5905_;
}
else
{
lean_inc(v_a_5904_);
lean_dec(v___x_5903_);
v___x_5906_ = lean_box(0);
v_isShared_5907_ = v_isSharedCheck_5924_;
goto v_resetjp_5905_;
}
v_resetjp_5905_:
{
lean_object* v___x_5908_; lean_object* v___x_5909_; uint8_t v___x_5910_; 
v___x_5908_ = lean_array_get_size(v_a_5904_);
v___x_5909_ = lean_box(0);
v___x_5910_ = lean_nat_dec_lt(v___x_5890_, v___x_5908_);
if (v___x_5910_ == 0)
{
lean_object* v___x_5912_; 
lean_dec(v_a_5904_);
lean_dec_ref(v_a_5889_);
if (v_isShared_5907_ == 0)
{
lean_ctor_set(v___x_5906_, 0, v___x_5909_);
v___x_5912_ = v___x_5906_;
goto v_reusejp_5911_;
}
else
{
lean_object* v_reuseFailAlloc_5913_; 
v_reuseFailAlloc_5913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5913_, 0, v___x_5909_);
v___x_5912_ = v_reuseFailAlloc_5913_;
goto v_reusejp_5911_;
}
v_reusejp_5911_:
{
return v___x_5912_;
}
}
else
{
uint8_t v___x_5914_; 
v___x_5914_ = lean_nat_dec_le(v___x_5908_, v___x_5908_);
if (v___x_5914_ == 0)
{
if (v___x_5910_ == 0)
{
lean_object* v___x_5916_; 
lean_dec(v_a_5904_);
lean_dec_ref(v_a_5889_);
if (v_isShared_5907_ == 0)
{
lean_ctor_set(v___x_5906_, 0, v___x_5909_);
v___x_5916_ = v___x_5906_;
goto v_reusejp_5915_;
}
else
{
lean_object* v_reuseFailAlloc_5917_; 
v_reuseFailAlloc_5917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5917_, 0, v___x_5909_);
v___x_5916_ = v_reuseFailAlloc_5917_;
goto v_reusejp_5915_;
}
v_reusejp_5915_:
{
return v___x_5916_;
}
}
else
{
size_t v___x_5918_; size_t v___x_5919_; lean_object* v___x_5920_; 
lean_del_object(v___x_5906_);
v___x_5918_ = ((size_t)0ULL);
v___x_5919_ = lean_usize_of_nat(v___x_5908_);
v___x_5920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1(v_a_5889_, v_a_5904_, v___x_5918_, v___x_5919_, v___x_5909_, v___y_5891_, v___y_5892_, v___y_5893_, v___y_5894_, v___y_5895_, v___y_5896_, v___y_5897_, v___y_5898_);
lean_dec(v_a_5904_);
return v___x_5920_;
}
}
else
{
size_t v___x_5921_; size_t v___x_5922_; lean_object* v___x_5923_; 
lean_del_object(v___x_5906_);
v___x_5921_ = ((size_t)0ULL);
v___x_5922_ = lean_usize_of_nat(v___x_5908_);
v___x_5923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1(v_a_5889_, v_a_5904_, v___x_5921_, v___x_5922_, v___x_5909_, v___y_5891_, v___y_5892_, v___y_5893_, v___y_5894_, v___y_5895_, v___y_5896_, v___y_5897_, v___y_5898_);
lean_dec(v_a_5904_);
return v___x_5923_;
}
}
}
}
else
{
lean_object* v_a_5925_; lean_object* v___x_5927_; uint8_t v_isShared_5928_; uint8_t v_isSharedCheck_5932_; 
lean_dec_ref(v_a_5889_);
v_a_5925_ = lean_ctor_get(v___x_5903_, 0);
v_isSharedCheck_5932_ = !lean_is_exclusive(v___x_5903_);
if (v_isSharedCheck_5932_ == 0)
{
v___x_5927_ = v___x_5903_;
v_isShared_5928_ = v_isSharedCheck_5932_;
goto v_resetjp_5926_;
}
else
{
lean_inc(v_a_5925_);
lean_dec(v___x_5903_);
v___x_5927_ = lean_box(0);
v_isShared_5928_ = v_isSharedCheck_5932_;
goto v_resetjp_5926_;
}
v_resetjp_5926_:
{
lean_object* v___x_5930_; 
if (v_isShared_5928_ == 0)
{
v___x_5930_ = v___x_5927_;
goto v_reusejp_5929_;
}
else
{
lean_object* v_reuseFailAlloc_5931_; 
v_reuseFailAlloc_5931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5931_, 0, v_a_5925_);
v___x_5930_ = v_reuseFailAlloc_5931_;
goto v_reusejp_5929_;
}
v_reusejp_5929_:
{
return v___x_5930_;
}
}
}
}
else
{
lean_object* v_a_5933_; lean_object* v___x_5935_; uint8_t v_isShared_5936_; uint8_t v_isSharedCheck_5940_; 
lean_dec_ref(v_a_5889_);
v_a_5933_ = lean_ctor_get(v___x_5901_, 0);
v_isSharedCheck_5940_ = !lean_is_exclusive(v___x_5901_);
if (v_isSharedCheck_5940_ == 0)
{
v___x_5935_ = v___x_5901_;
v_isShared_5936_ = v_isSharedCheck_5940_;
goto v_resetjp_5934_;
}
else
{
lean_inc(v_a_5933_);
lean_dec(v___x_5901_);
v___x_5935_ = lean_box(0);
v_isShared_5936_ = v_isSharedCheck_5940_;
goto v_resetjp_5934_;
}
v_resetjp_5934_:
{
lean_object* v___x_5938_; 
if (v_isShared_5936_ == 0)
{
v___x_5938_ = v___x_5935_;
goto v_reusejp_5937_;
}
else
{
lean_object* v_reuseFailAlloc_5939_; 
v_reuseFailAlloc_5939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5939_, 0, v_a_5933_);
v___x_5938_ = v_reuseFailAlloc_5939_;
goto v_reusejp_5937_;
}
v_reusejp_5937_:
{
return v___x_5938_;
}
}
}
}
else
{
lean_dec_ref(v_a_5889_);
return v___x_5900_;
}
}
else
{
lean_object* v_hypotheses_5941_; uint8_t v_type_5942_; lean_object* v___y_5944_; lean_object* v___y_5945_; lean_object* v___y_5946_; lean_object* v___y_5947_; lean_object* v___y_5948_; lean_object* v___y_5949_; lean_object* v___y_5950_; lean_object* v___y_5951_; 
v_hypotheses_5941_ = lean_ctor_get(v___y_5888_, 0);
lean_inc_ref(v_hypotheses_5941_);
v_type_5942_ = lean_ctor_get_uint8(v___y_5888_, sizeof(void*)*1);
lean_dec_ref(v___y_5888_);
if (v_type_5942_ == 0)
{
v___y_5944_ = v___y_5891_;
v___y_5945_ = v___y_5892_;
v___y_5946_ = v___y_5893_;
v___y_5947_ = v___y_5894_;
v___y_5948_ = v___y_5895_;
v___y_5949_ = v___y_5896_;
v___y_5950_ = v___y_5897_;
v___y_5951_ = v___y_5898_;
goto v___jp_5943_;
}
else
{
lean_object* v___x_5982_; 
lean_inc_ref(v_a_5889_);
v___x_5982_ = l_Lean_Elab_Tactic_NormCast_normCastTarget(v_a_5889_, v___y_5891_, v___y_5892_, v___y_5893_, v___y_5894_, v___y_5895_, v___y_5896_, v___y_5897_, v___y_5898_);
if (lean_obj_tag(v___x_5982_) == 0)
{
lean_dec_ref(v___x_5982_);
v___y_5944_ = v___y_5891_;
v___y_5945_ = v___y_5892_;
v___y_5946_ = v___y_5893_;
v___y_5947_ = v___y_5894_;
v___y_5948_ = v___y_5895_;
v___y_5949_ = v___y_5896_;
v___y_5950_ = v___y_5897_;
v___y_5951_ = v___y_5898_;
goto v___jp_5943_;
}
else
{
lean_dec_ref(v_hypotheses_5941_);
lean_dec_ref(v_a_5889_);
return v___x_5982_;
}
}
v___jp_5943_:
{
lean_object* v___x_5952_; 
v___x_5952_ = l_Lean_Elab_Tactic_getFVarIds(v_hypotheses_5941_, v___y_5944_, v___y_5945_, v___y_5946_, v___y_5947_, v___y_5948_, v___y_5949_, v___y_5950_, v___y_5951_);
if (lean_obj_tag(v___x_5952_) == 0)
{
lean_object* v_a_5953_; lean_object* v___x_5955_; uint8_t v_isShared_5956_; uint8_t v_isSharedCheck_5973_; 
v_a_5953_ = lean_ctor_get(v___x_5952_, 0);
v_isSharedCheck_5973_ = !lean_is_exclusive(v___x_5952_);
if (v_isSharedCheck_5973_ == 0)
{
v___x_5955_ = v___x_5952_;
v_isShared_5956_ = v_isSharedCheck_5973_;
goto v_resetjp_5954_;
}
else
{
lean_inc(v_a_5953_);
lean_dec(v___x_5952_);
v___x_5955_ = lean_box(0);
v_isShared_5956_ = v_isSharedCheck_5973_;
goto v_resetjp_5954_;
}
v_resetjp_5954_:
{
lean_object* v___x_5957_; lean_object* v___x_5958_; uint8_t v___x_5959_; 
v___x_5957_ = lean_array_get_size(v_a_5953_);
v___x_5958_ = lean_box(0);
v___x_5959_ = lean_nat_dec_lt(v___x_5890_, v___x_5957_);
if (v___x_5959_ == 0)
{
lean_object* v___x_5961_; 
lean_dec(v_a_5953_);
lean_dec_ref(v_a_5889_);
if (v_isShared_5956_ == 0)
{
lean_ctor_set(v___x_5955_, 0, v___x_5958_);
v___x_5961_ = v___x_5955_;
goto v_reusejp_5960_;
}
else
{
lean_object* v_reuseFailAlloc_5962_; 
v_reuseFailAlloc_5962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5962_, 0, v___x_5958_);
v___x_5961_ = v_reuseFailAlloc_5962_;
goto v_reusejp_5960_;
}
v_reusejp_5960_:
{
return v___x_5961_;
}
}
else
{
uint8_t v___x_5963_; 
v___x_5963_ = lean_nat_dec_le(v___x_5957_, v___x_5957_);
if (v___x_5963_ == 0)
{
if (v___x_5959_ == 0)
{
lean_object* v___x_5965_; 
lean_dec(v_a_5953_);
lean_dec_ref(v_a_5889_);
if (v_isShared_5956_ == 0)
{
lean_ctor_set(v___x_5955_, 0, v___x_5958_);
v___x_5965_ = v___x_5955_;
goto v_reusejp_5964_;
}
else
{
lean_object* v_reuseFailAlloc_5966_; 
v_reuseFailAlloc_5966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5966_, 0, v___x_5958_);
v___x_5965_ = v_reuseFailAlloc_5966_;
goto v_reusejp_5964_;
}
v_reusejp_5964_:
{
return v___x_5965_;
}
}
else
{
size_t v___x_5967_; size_t v___x_5968_; lean_object* v___x_5969_; 
lean_del_object(v___x_5955_);
v___x_5967_ = ((size_t)0ULL);
v___x_5968_ = lean_usize_of_nat(v___x_5957_);
v___x_5969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1(v_a_5889_, v_a_5953_, v___x_5967_, v___x_5968_, v___x_5958_, v___y_5944_, v___y_5945_, v___y_5946_, v___y_5947_, v___y_5948_, v___y_5949_, v___y_5950_, v___y_5951_);
lean_dec(v_a_5953_);
return v___x_5969_;
}
}
else
{
size_t v___x_5970_; size_t v___x_5971_; lean_object* v___x_5972_; 
lean_del_object(v___x_5955_);
v___x_5970_ = ((size_t)0ULL);
v___x_5971_ = lean_usize_of_nat(v___x_5957_);
v___x_5972_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__1(v_a_5889_, v_a_5953_, v___x_5970_, v___x_5971_, v___x_5958_, v___y_5944_, v___y_5945_, v___y_5946_, v___y_5947_, v___y_5948_, v___y_5949_, v___y_5950_, v___y_5951_);
lean_dec(v_a_5953_);
return v___x_5972_;
}
}
}
}
else
{
lean_object* v_a_5974_; lean_object* v___x_5976_; uint8_t v_isShared_5977_; uint8_t v_isSharedCheck_5981_; 
lean_dec_ref(v_a_5889_);
v_a_5974_ = lean_ctor_get(v___x_5952_, 0);
v_isSharedCheck_5981_ = !lean_is_exclusive(v___x_5952_);
if (v_isSharedCheck_5981_ == 0)
{
v___x_5976_ = v___x_5952_;
v_isShared_5977_ = v_isSharedCheck_5981_;
goto v_resetjp_5975_;
}
else
{
lean_inc(v_a_5974_);
lean_dec(v___x_5952_);
v___x_5976_ = lean_box(0);
v_isShared_5977_ = v_isSharedCheck_5981_;
goto v_resetjp_5975_;
}
v_resetjp_5975_:
{
lean_object* v___x_5979_; 
if (v_isShared_5977_ == 0)
{
v___x_5979_ = v___x_5976_;
goto v_reusejp_5978_;
}
else
{
lean_object* v_reuseFailAlloc_5980_; 
v_reuseFailAlloc_5980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5980_, 0, v_a_5974_);
v___x_5979_ = v_reuseFailAlloc_5980_;
goto v_reusejp_5978_;
}
v_reusejp_5978_:
{
return v___x_5979_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___lam__0___boxed(lean_object* v___y_5983_, lean_object* v_a_5984_, lean_object* v___x_5985_, lean_object* v___y_5986_, lean_object* v___y_5987_, lean_object* v___y_5988_, lean_object* v___y_5989_, lean_object* v___y_5990_, lean_object* v___y_5991_, lean_object* v___y_5992_, lean_object* v___y_5993_, lean_object* v___y_5994_){
_start:
{
lean_object* v_res_5995_; 
v_res_5995_ = l_Lean_Elab_Tactic_NormCast_evalNormCast0___lam__0(v___y_5983_, v_a_5984_, v___x_5985_, v___y_5986_, v___y_5987_, v___y_5988_, v___y_5989_, v___y_5990_, v___y_5991_, v___y_5992_, v___y_5993_);
lean_dec(v___y_5993_);
lean_dec_ref(v___y_5992_);
lean_dec(v___y_5991_);
lean_dec_ref(v___y_5990_);
lean_dec(v___y_5989_);
lean_dec_ref(v___y_5988_);
lean_dec(v___y_5987_);
lean_dec_ref(v___y_5986_);
lean_dec(v___x_5985_);
return v_res_5995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0(lean_object* v_stx_6005_, lean_object* v_a_6006_, lean_object* v_a_6007_, lean_object* v_a_6008_, lean_object* v_a_6009_, lean_object* v_a_6010_, lean_object* v_a_6011_, lean_object* v_a_6012_, lean_object* v_a_6013_){
_start:
{
lean_object* v___x_6015_; uint8_t v___x_6016_; 
v___x_6015_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__2));
lean_inc(v_stx_6005_);
v___x_6016_ = l_Lean_Syntax_isOfKind(v_stx_6005_, v___x_6015_);
if (v___x_6016_ == 0)
{
lean_object* v___x_6017_; 
lean_dec(v_stx_6005_);
v___x_6017_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg();
return v___x_6017_;
}
else
{
lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___y_6022_; lean_object* v___y_6023_; lean_object* v___y_6024_; lean_object* v___y_6025_; lean_object* v___y_6026_; lean_object* v___y_6027_; lean_object* v___y_6028_; lean_object* v___y_6029_; lean_object* v___y_6030_; lean_object* v___x_6043_; lean_object* v___x_6044_; uint8_t v___x_6045_; 
v___x_6018_ = lean_unsigned_to_nat(0u);
v___x_6019_ = lean_unsigned_to_nat(1u);
v___x_6020_ = l_Lean_Syntax_getArg(v_stx_6005_, v___x_6019_);
v___x_6043_ = lean_unsigned_to_nat(2u);
v___x_6044_ = l_Lean_Syntax_getArg(v_stx_6005_, v___x_6043_);
lean_dec(v_stx_6005_);
v___x_6045_ = l_Lean_Syntax_isNone(v___x_6044_);
if (v___x_6045_ == 0)
{
uint8_t v___x_6046_; 
lean_inc(v___x_6044_);
v___x_6046_ = l_Lean_Syntax_matchesNull(v___x_6044_, v___x_6019_);
if (v___x_6046_ == 0)
{
lean_object* v___x_6047_; 
lean_dec(v___x_6044_);
lean_dec(v___x_6020_);
v___x_6047_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_evalNormCast0_spec__0___redArg();
return v___x_6047_;
}
else
{
lean_object* v_loc_x3f_6048_; lean_object* v___x_6049_; 
v_loc_x3f_6048_ = l_Lean_Syntax_getArg(v___x_6044_, v___x_6018_);
lean_dec(v___x_6044_);
v___x_6049_ = l_Lean_Elab_Tactic_expandLocation(v_loc_x3f_6048_);
lean_dec(v_loc_x3f_6048_);
v___y_6022_ = v_a_6008_;
v___y_6023_ = v_a_6011_;
v___y_6024_ = v_a_6012_;
v___y_6025_ = v_a_6009_;
v___y_6026_ = v_a_6010_;
v___y_6027_ = v_a_6007_;
v___y_6028_ = v_a_6006_;
v___y_6029_ = v_a_6013_;
v___y_6030_ = v___x_6049_;
goto v___jp_6021_;
}
}
else
{
lean_object* v___x_6050_; lean_object* v___x_6051_; 
lean_dec(v___x_6044_);
v___x_6050_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__3));
v___x_6051_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_6051_, 0, v___x_6050_);
lean_ctor_set_uint8(v___x_6051_, sizeof(void*)*1, v___x_6016_);
v___y_6022_ = v_a_6008_;
v___y_6023_ = v_a_6011_;
v___y_6024_ = v_a_6012_;
v___y_6025_ = v_a_6009_;
v___y_6026_ = v_a_6010_;
v___y_6027_ = v_a_6007_;
v___y_6028_ = v_a_6006_;
v___y_6029_ = v_a_6013_;
v___y_6030_ = v___x_6051_;
goto v___jp_6021_;
}
v___jp_6021_:
{
lean_object* v___x_6031_; 
v___x_6031_ = l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg(v___x_6020_, v___y_6028_, v___y_6022_, v___y_6025_, v___y_6026_, v___y_6023_, v___y_6024_, v___y_6029_);
if (lean_obj_tag(v___x_6031_) == 0)
{
lean_object* v_a_6032_; lean_object* v___y_6033_; lean_object* v___x_6034_; 
v_a_6032_ = lean_ctor_get(v___x_6031_, 0);
lean_inc(v_a_6032_);
lean_dec_ref(v___x_6031_);
v___y_6033_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___lam__0___boxed), 12, 3);
lean_closure_set(v___y_6033_, 0, v___y_6030_);
lean_closure_set(v___y_6033_, 1, v_a_6032_);
lean_closure_set(v___y_6033_, 2, v___x_6018_);
v___x_6034_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___y_6033_, v___y_6028_, v___y_6027_, v___y_6022_, v___y_6025_, v___y_6026_, v___y_6023_, v___y_6024_, v___y_6029_);
return v___x_6034_;
}
else
{
lean_object* v_a_6035_; lean_object* v___x_6037_; uint8_t v_isShared_6038_; uint8_t v_isSharedCheck_6042_; 
lean_dec(v___y_6030_);
v_a_6035_ = lean_ctor_get(v___x_6031_, 0);
v_isSharedCheck_6042_ = !lean_is_exclusive(v___x_6031_);
if (v_isSharedCheck_6042_ == 0)
{
v___x_6037_ = v___x_6031_;
v_isShared_6038_ = v_isSharedCheck_6042_;
goto v_resetjp_6036_;
}
else
{
lean_inc(v_a_6035_);
lean_dec(v___x_6031_);
v___x_6037_ = lean_box(0);
v_isShared_6038_ = v_isSharedCheck_6042_;
goto v_resetjp_6036_;
}
v_resetjp_6036_:
{
lean_object* v___x_6040_; 
if (v_isShared_6038_ == 0)
{
v___x_6040_ = v___x_6037_;
goto v_reusejp_6039_;
}
else
{
lean_object* v_reuseFailAlloc_6041_; 
v_reuseFailAlloc_6041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6041_, 0, v_a_6035_);
v___x_6040_ = v_reuseFailAlloc_6041_;
goto v_reusejp_6039_;
}
v_reusejp_6039_:
{
return v___x_6040_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalNormCast0___boxed(lean_object* v_stx_6052_, lean_object* v_a_6053_, lean_object* v_a_6054_, lean_object* v_a_6055_, lean_object* v_a_6056_, lean_object* v_a_6057_, lean_object* v_a_6058_, lean_object* v_a_6059_, lean_object* v_a_6060_, lean_object* v_a_6061_){
_start:
{
lean_object* v_res_6062_; 
v_res_6062_ = l_Lean_Elab_Tactic_NormCast_evalNormCast0(v_stx_6052_, v_a_6053_, v_a_6054_, v_a_6055_, v_a_6056_, v_a_6057_, v_a_6058_, v_a_6059_, v_a_6060_);
lean_dec(v_a_6060_);
lean_dec_ref(v_a_6059_);
lean_dec(v_a_6058_);
lean_dec_ref(v_a_6057_);
lean_dec(v_a_6056_);
lean_dec_ref(v_a_6055_);
lean_dec(v_a_6054_);
lean_dec_ref(v_a_6053_);
return v_res_6062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1(){
_start:
{
lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; 
v___x_6071_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6072_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___closed__2));
v___x_6073_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1));
v___x_6074_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalNormCast0___boxed), 10, 0);
v___x_6075_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6071_, v___x_6072_, v___x_6073_, v___x_6074_);
return v___x_6075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___boxed(lean_object* v_a_6076_){
_start:
{
lean_object* v_res_6077_; 
v_res_6077_ = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1();
return v_res_6077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3(){
_start:
{
lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; 
v___x_6104_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0__1___closed__1));
v___x_6105_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___closed__6));
v___x_6106_ = l_Lean_addBuiltinDeclarationRanges(v___x_6104_, v___x_6105_);
return v___x_6106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3___boxed(lean_object* v_a_6107_){
_start:
{
lean_object* v_res_6108_; 
v_res_6108_ = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalNormCast0___regBuiltin_Lean_Elab_Tactic_NormCast_evalNormCast0_declRange__3();
return v_res_6108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___lam__0(lean_object* v___y_6109_, lean_object* v___y_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_, lean_object* v___y_6115_, lean_object* v___y_6116_){
_start:
{
lean_object* v___x_6118_; 
v___x_6118_ = l_Lean_Elab_Tactic_Conv_getLhs___redArg(v___y_6110_, v___y_6113_, v___y_6114_, v___y_6115_, v___y_6116_);
if (lean_obj_tag(v___x_6118_) == 0)
{
lean_object* v_a_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; 
v_a_6119_ = lean_ctor_get(v___x_6118_, 0);
lean_inc(v_a_6119_);
lean_dec_ref(v___x_6118_);
v___x_6120_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabNormCastConfig___redArg___closed__10));
v___x_6121_ = l_Lean_Elab_Tactic_NormCast_derive(v_a_6119_, v___x_6120_, v___y_6113_, v___y_6114_, v___y_6115_, v___y_6116_);
if (lean_obj_tag(v___x_6121_) == 0)
{
lean_object* v_a_6122_; lean_object* v___x_6123_; 
v_a_6122_ = lean_ctor_get(v___x_6121_, 0);
lean_inc(v_a_6122_);
lean_dec_ref(v___x_6121_);
v___x_6123_ = l_Lean_Elab_Tactic_Conv_applySimpResult(v_a_6122_, v___y_6109_, v___y_6110_, v___y_6111_, v___y_6112_, v___y_6113_, v___y_6114_, v___y_6115_, v___y_6116_);
return v___x_6123_;
}
else
{
lean_object* v_a_6124_; lean_object* v___x_6126_; uint8_t v_isShared_6127_; uint8_t v_isSharedCheck_6131_; 
v_a_6124_ = lean_ctor_get(v___x_6121_, 0);
v_isSharedCheck_6131_ = !lean_is_exclusive(v___x_6121_);
if (v_isSharedCheck_6131_ == 0)
{
v___x_6126_ = v___x_6121_;
v_isShared_6127_ = v_isSharedCheck_6131_;
goto v_resetjp_6125_;
}
else
{
lean_inc(v_a_6124_);
lean_dec(v___x_6121_);
v___x_6126_ = lean_box(0);
v_isShared_6127_ = v_isSharedCheck_6131_;
goto v_resetjp_6125_;
}
v_resetjp_6125_:
{
lean_object* v___x_6129_; 
if (v_isShared_6127_ == 0)
{
v___x_6129_ = v___x_6126_;
goto v_reusejp_6128_;
}
else
{
lean_object* v_reuseFailAlloc_6130_; 
v_reuseFailAlloc_6130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6130_, 0, v_a_6124_);
v___x_6129_ = v_reuseFailAlloc_6130_;
goto v_reusejp_6128_;
}
v_reusejp_6128_:
{
return v___x_6129_;
}
}
}
}
else
{
lean_object* v_a_6132_; lean_object* v___x_6134_; uint8_t v_isShared_6135_; uint8_t v_isSharedCheck_6139_; 
v_a_6132_ = lean_ctor_get(v___x_6118_, 0);
v_isSharedCheck_6139_ = !lean_is_exclusive(v___x_6118_);
if (v_isSharedCheck_6139_ == 0)
{
v___x_6134_ = v___x_6118_;
v_isShared_6135_ = v_isSharedCheck_6139_;
goto v_resetjp_6133_;
}
else
{
lean_inc(v_a_6132_);
lean_dec(v___x_6118_);
v___x_6134_ = lean_box(0);
v_isShared_6135_ = v_isSharedCheck_6139_;
goto v_resetjp_6133_;
}
v_resetjp_6133_:
{
lean_object* v___x_6137_; 
if (v_isShared_6135_ == 0)
{
v___x_6137_ = v___x_6134_;
goto v_reusejp_6136_;
}
else
{
lean_object* v_reuseFailAlloc_6138_; 
v_reuseFailAlloc_6138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6138_, 0, v_a_6132_);
v___x_6137_ = v_reuseFailAlloc_6138_;
goto v_reusejp_6136_;
}
v_reusejp_6136_:
{
return v___x_6137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___lam__0___boxed(lean_object* v___y_6140_, lean_object* v___y_6141_, lean_object* v___y_6142_, lean_object* v___y_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_, lean_object* v___y_6147_, lean_object* v___y_6148_){
_start:
{
lean_object* v_res_6149_; 
v_res_6149_ = l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___lam__0(v___y_6140_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_, v___y_6146_, v___y_6147_);
lean_dec(v___y_6147_);
lean_dec_ref(v___y_6146_);
lean_dec(v___y_6145_);
lean_dec_ref(v___y_6144_);
lean_dec(v___y_6143_);
lean_dec_ref(v___y_6142_);
lean_dec(v___y_6141_);
lean_dec_ref(v___y_6140_);
return v_res_6149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg(lean_object* v_a_6151_, lean_object* v_a_6152_, lean_object* v_a_6153_, lean_object* v_a_6154_, lean_object* v_a_6155_, lean_object* v_a_6156_, lean_object* v_a_6157_, lean_object* v_a_6158_){
_start:
{
lean_object* v___f_6160_; lean_object* v___x_6161_; 
v___f_6160_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___closed__0));
v___x_6161_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___f_6160_, v_a_6151_, v_a_6152_, v_a_6153_, v_a_6154_, v_a_6155_, v_a_6156_, v_a_6157_, v_a_6158_);
return v___x_6161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg___boxed(lean_object* v_a_6162_, lean_object* v_a_6163_, lean_object* v_a_6164_, lean_object* v_a_6165_, lean_object* v_a_6166_, lean_object* v_a_6167_, lean_object* v_a_6168_, lean_object* v_a_6169_, lean_object* v_a_6170_){
_start:
{
lean_object* v_res_6171_; 
v_res_6171_ = l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg(v_a_6162_, v_a_6163_, v_a_6164_, v_a_6165_, v_a_6166_, v_a_6167_, v_a_6168_, v_a_6169_);
lean_dec(v_a_6169_);
lean_dec_ref(v_a_6168_);
lean_dec(v_a_6167_);
lean_dec_ref(v_a_6166_);
lean_dec(v_a_6165_);
lean_dec_ref(v_a_6164_);
lean_dec(v_a_6163_);
lean_dec_ref(v_a_6162_);
return v_res_6171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast(lean_object* v_x_6172_, lean_object* v_a_6173_, lean_object* v_a_6174_, lean_object* v_a_6175_, lean_object* v_a_6176_, lean_object* v_a_6177_, lean_object* v_a_6178_, lean_object* v_a_6179_, lean_object* v_a_6180_){
_start:
{
lean_object* v___x_6182_; 
v___x_6182_ = l_Lean_Elab_Tactic_NormCast_evalConvNormCast___redArg(v_a_6173_, v_a_6174_, v_a_6175_, v_a_6176_, v_a_6177_, v_a_6178_, v_a_6179_, v_a_6180_);
return v___x_6182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalConvNormCast___boxed(lean_object* v_x_6183_, lean_object* v_a_6184_, lean_object* v_a_6185_, lean_object* v_a_6186_, lean_object* v_a_6187_, lean_object* v_a_6188_, lean_object* v_a_6189_, lean_object* v_a_6190_, lean_object* v_a_6191_, lean_object* v_a_6192_){
_start:
{
lean_object* v_res_6193_; 
v_res_6193_ = l_Lean_Elab_Tactic_NormCast_evalConvNormCast(v_x_6183_, v_a_6184_, v_a_6185_, v_a_6186_, v_a_6187_, v_a_6188_, v_a_6189_, v_a_6190_, v_a_6191_);
lean_dec(v_a_6191_);
lean_dec_ref(v_a_6190_);
lean_dec(v_a_6189_);
lean_dec_ref(v_a_6188_);
lean_dec(v_a_6187_);
lean_dec_ref(v_a_6186_);
lean_dec(v_a_6185_);
lean_dec_ref(v_a_6184_);
lean_dec(v_x_6183_);
return v_res_6193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1(){
_start:
{
lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; lean_object* v___x_6213_; lean_object* v___x_6214_; 
v___x_6210_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6211_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__2));
v___x_6212_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4));
v___x_6213_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalConvNormCast___boxed), 10, 0);
v___x_6214_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6210_, v___x_6211_, v___x_6212_, v___x_6213_);
return v___x_6214_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___boxed(lean_object* v_a_6215_){
_start:
{
lean_object* v_res_6216_; 
v_res_6216_ = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1();
return v_res_6216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3(){
_start:
{
lean_object* v___x_6243_; lean_object* v___x_6244_; lean_object* v___x_6245_; 
v___x_6243_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast__1___closed__4));
v___x_6244_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___closed__6));
v___x_6245_ = l_Lean_addBuiltinDeclarationRanges(v___x_6243_, v___x_6244_);
return v___x_6245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3___boxed(lean_object* v_a_6246_){
_start:
{
lean_object* v_res_6247_; 
v_res_6247_ = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalConvNormCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalConvNormCast_declRange__3();
return v_res_6247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0(lean_object* v_stx_6248_, lean_object* v___x_6249_, lean_object* v_simprocs_6250_, lean_object* v_discharge_x3f_6251_, lean_object* v___y_6252_, lean_object* v___y_6253_, lean_object* v___y_6254_, lean_object* v___y_6255_, lean_object* v___y_6256_, lean_object* v___y_6257_, lean_object* v___y_6258_, lean_object* v___y_6259_){
_start:
{
lean_object* v___x_6261_; lean_object* v___x_6262_; lean_object* v___x_6263_; lean_object* v___x_6264_; 
v___x_6261_ = lean_unsigned_to_nat(5u);
v___x_6262_ = l_Lean_Syntax_getArg(v_stx_6248_, v___x_6261_);
v___x_6263_ = l_Lean_Elab_Tactic_expandOptLocation(v___x_6262_);
lean_dec(v___x_6262_);
v___x_6264_ = l_Lean_Elab_Tactic_simpLocation(v___x_6249_, v_simprocs_6250_, v_discharge_x3f_6251_, v___x_6263_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_, v___y_6256_, v___y_6257_, v___y_6258_, v___y_6259_);
if (lean_obj_tag(v___x_6264_) == 0)
{
lean_object* v___x_6266_; uint8_t v_isShared_6267_; uint8_t v_isSharedCheck_6272_; 
v_isSharedCheck_6272_ = !lean_is_exclusive(v___x_6264_);
if (v_isSharedCheck_6272_ == 0)
{
lean_object* v_unused_6273_; 
v_unused_6273_ = lean_ctor_get(v___x_6264_, 0);
lean_dec(v_unused_6273_);
v___x_6266_ = v___x_6264_;
v_isShared_6267_ = v_isSharedCheck_6272_;
goto v_resetjp_6265_;
}
else
{
lean_dec(v___x_6264_);
v___x_6266_ = lean_box(0);
v_isShared_6267_ = v_isSharedCheck_6272_;
goto v_resetjp_6265_;
}
v_resetjp_6265_:
{
lean_object* v___x_6268_; lean_object* v___x_6270_; 
v___x_6268_ = lean_box(0);
if (v_isShared_6267_ == 0)
{
lean_ctor_set(v___x_6266_, 0, v___x_6268_);
v___x_6270_ = v___x_6266_;
goto v_reusejp_6269_;
}
else
{
lean_object* v_reuseFailAlloc_6271_; 
v_reuseFailAlloc_6271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6271_, 0, v___x_6268_);
v___x_6270_ = v_reuseFailAlloc_6271_;
goto v_reusejp_6269_;
}
v_reusejp_6269_:
{
return v___x_6270_;
}
}
}
else
{
lean_object* v_a_6274_; lean_object* v___x_6276_; uint8_t v_isShared_6277_; uint8_t v_isSharedCheck_6281_; 
v_a_6274_ = lean_ctor_get(v___x_6264_, 0);
v_isSharedCheck_6281_ = !lean_is_exclusive(v___x_6264_);
if (v_isSharedCheck_6281_ == 0)
{
v___x_6276_ = v___x_6264_;
v_isShared_6277_ = v_isSharedCheck_6281_;
goto v_resetjp_6275_;
}
else
{
lean_inc(v_a_6274_);
lean_dec(v___x_6264_);
v___x_6276_ = lean_box(0);
v_isShared_6277_ = v_isSharedCheck_6281_;
goto v_resetjp_6275_;
}
v_resetjp_6275_:
{
lean_object* v___x_6279_; 
if (v_isShared_6277_ == 0)
{
v___x_6279_ = v___x_6276_;
goto v_reusejp_6278_;
}
else
{
lean_object* v_reuseFailAlloc_6280_; 
v_reuseFailAlloc_6280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6280_, 0, v_a_6274_);
v___x_6279_ = v_reuseFailAlloc_6280_;
goto v_reusejp_6278_;
}
v_reusejp_6278_:
{
return v___x_6279_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0___boxed(lean_object* v_stx_6282_, lean_object* v___x_6283_, lean_object* v_simprocs_6284_, lean_object* v_discharge_x3f_6285_, lean_object* v___y_6286_, lean_object* v___y_6287_, lean_object* v___y_6288_, lean_object* v___y_6289_, lean_object* v___y_6290_, lean_object* v___y_6291_, lean_object* v___y_6292_, lean_object* v___y_6293_, lean_object* v___y_6294_){
_start:
{
lean_object* v_res_6295_; 
v_res_6295_ = l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0(v_stx_6282_, v___x_6283_, v_simprocs_6284_, v_discharge_x3f_6285_, v___y_6286_, v___y_6287_, v___y_6288_, v___y_6289_, v___y_6290_, v___y_6291_, v___y_6292_, v___y_6293_);
lean_dec(v___y_6293_);
lean_dec_ref(v___y_6292_);
lean_dec(v___y_6291_);
lean_dec_ref(v___y_6290_);
lean_dec(v___y_6289_);
lean_dec_ref(v___y_6288_);
lean_dec(v___y_6287_);
lean_dec_ref(v___y_6286_);
lean_dec(v_stx_6282_);
return v_res_6295_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__0(void){
_start:
{
lean_object* v___x_6296_; lean_object* v___x_6297_; 
v___x_6296_ = l_Lean_Meta_NormCast_pushCastExt;
v___x_6297_ = lean_alloc_closure((void*)(l_Lean_Meta_SimpExtension_getTheorems___boxed), 4, 1);
lean_closure_set(v___x_6297_, 0, v___x_6296_);
return v___x_6297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast(lean_object* v_stx_6298_, lean_object* v_a_6299_, lean_object* v_a_6300_, lean_object* v_a_6301_, lean_object* v_a_6302_, lean_object* v_a_6303_, lean_object* v_a_6304_, lean_object* v_a_6305_, lean_object* v_a_6306_){
_start:
{
uint8_t v___x_6308_; uint8_t v___x_6309_; lean_object* v___x_6310_; lean_object* v___x_6311_; lean_object* v___x_6312_; lean_object* v___x_6313_; lean_object* v___x_6314_; lean_object* v___x_6315_; 
v___x_6308_ = 0;
v___x_6309_ = 0;
v___x_6310_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__0, &l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__0_once, _init_l_Lean_Elab_Tactic_NormCast_evalPushCast___closed__0);
v___x_6311_ = lean_box(v___x_6308_);
v___x_6312_ = lean_box(v___x_6309_);
v___x_6313_ = lean_box(v___x_6308_);
lean_inc(v_stx_6298_);
v___x_6314_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_mkSimpContext___boxed), 14, 5);
lean_closure_set(v___x_6314_, 0, v_stx_6298_);
lean_closure_set(v___x_6314_, 1, v___x_6311_);
lean_closure_set(v___x_6314_, 2, v___x_6312_);
lean_closure_set(v___x_6314_, 3, v___x_6313_);
lean_closure_set(v___x_6314_, 4, v___x_6310_);
v___x_6315_ = l_Lean_Elab_Tactic_withMainContext___redArg(v___x_6314_, v_a_6299_, v_a_6300_, v_a_6301_, v_a_6302_, v_a_6303_, v_a_6304_, v_a_6305_, v_a_6306_);
if (lean_obj_tag(v___x_6315_) == 0)
{
lean_object* v_a_6316_; lean_object* v_ctx_6317_; lean_object* v_simprocs_6318_; lean_object* v_dischargeWrapper_6319_; lean_object* v___x_6320_; lean_object* v___f_6321_; lean_object* v___x_6322_; 
v_a_6316_ = lean_ctor_get(v___x_6315_, 0);
lean_inc(v_a_6316_);
lean_dec_ref(v___x_6315_);
v_ctx_6317_ = lean_ctor_get(v_a_6316_, 0);
lean_inc_ref(v_ctx_6317_);
v_simprocs_6318_ = lean_ctor_get(v_a_6316_, 1);
lean_inc_ref(v_simprocs_6318_);
v_dischargeWrapper_6319_ = lean_ctor_get(v_a_6316_, 2);
lean_inc(v_dischargeWrapper_6319_);
lean_dec(v_a_6316_);
v___x_6320_ = l_Lean_Meta_Simp_Context_setFailIfUnchanged(v_ctx_6317_, v___x_6308_);
v___f_6321_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalPushCast___lam__0___boxed), 13, 3);
lean_closure_set(v___f_6321_, 0, v_stx_6298_);
lean_closure_set(v___f_6321_, 1, v___x_6320_);
lean_closure_set(v___f_6321_, 2, v_simprocs_6318_);
v___x_6322_ = l_Lean_Elab_Tactic_Simp_DischargeWrapper_with___redArg(v_dischargeWrapper_6319_, v___f_6321_, v_a_6299_, v_a_6300_, v_a_6301_, v_a_6302_, v_a_6303_, v_a_6304_, v_a_6305_, v_a_6306_);
lean_dec(v_dischargeWrapper_6319_);
return v___x_6322_;
}
else
{
lean_object* v_a_6323_; lean_object* v___x_6325_; uint8_t v_isShared_6326_; uint8_t v_isSharedCheck_6330_; 
lean_dec(v_stx_6298_);
v_a_6323_ = lean_ctor_get(v___x_6315_, 0);
v_isSharedCheck_6330_ = !lean_is_exclusive(v___x_6315_);
if (v_isSharedCheck_6330_ == 0)
{
v___x_6325_ = v___x_6315_;
v_isShared_6326_ = v_isSharedCheck_6330_;
goto v_resetjp_6324_;
}
else
{
lean_inc(v_a_6323_);
lean_dec(v___x_6315_);
v___x_6325_ = lean_box(0);
v_isShared_6326_ = v_isSharedCheck_6330_;
goto v_resetjp_6324_;
}
v_resetjp_6324_:
{
lean_object* v___x_6328_; 
if (v_isShared_6326_ == 0)
{
v___x_6328_ = v___x_6325_;
goto v_reusejp_6327_;
}
else
{
lean_object* v_reuseFailAlloc_6329_; 
v_reuseFailAlloc_6329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6329_, 0, v_a_6323_);
v___x_6328_ = v_reuseFailAlloc_6329_;
goto v_reusejp_6327_;
}
v_reusejp_6327_:
{
return v___x_6328_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_evalPushCast___boxed(lean_object* v_stx_6331_, lean_object* v_a_6332_, lean_object* v_a_6333_, lean_object* v_a_6334_, lean_object* v_a_6335_, lean_object* v_a_6336_, lean_object* v_a_6337_, lean_object* v_a_6338_, lean_object* v_a_6339_, lean_object* v_a_6340_){
_start:
{
lean_object* v_res_6341_; 
v_res_6341_ = l_Lean_Elab_Tactic_NormCast_evalPushCast(v_stx_6331_, v_a_6332_, v_a_6333_, v_a_6334_, v_a_6335_, v_a_6336_, v_a_6337_, v_a_6338_, v_a_6339_);
lean_dec(v_a_6339_);
lean_dec_ref(v_a_6338_);
lean_dec(v_a_6337_);
lean_dec_ref(v_a_6336_);
lean_dec(v_a_6335_);
lean_dec_ref(v_a_6334_);
lean_dec(v_a_6333_);
lean_dec_ref(v_a_6332_);
return v_res_6341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1(){
_start:
{
lean_object* v___x_6356_; lean_object* v___x_6357_; lean_object* v___x_6358_; lean_object* v___x_6359_; lean_object* v___x_6360_; 
v___x_6356_ = l_Lean_Elab_Tactic_tacticElabAttribute;
v___x_6357_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__1));
v___x_6358_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3));
v___x_6359_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_evalPushCast___boxed), 10, 0);
v___x_6360_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6356_, v___x_6357_, v___x_6358_, v___x_6359_);
return v___x_6360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___boxed(lean_object* v_a_6361_){
_start:
{
lean_object* v_res_6362_; 
v_res_6362_ = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1();
return v_res_6362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3(){
_start:
{
lean_object* v___x_6389_; lean_object* v___x_6390_; lean_object* v___x_6391_; 
v___x_6389_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast__1___closed__3));
v___x_6390_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___closed__6));
v___x_6391_ = l_Lean_addBuiltinDeclarationRanges(v___x_6389_, v___x_6390_);
return v___x_6391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3___boxed(lean_object* v_a_6392_){
_start:
{
lean_object* v_res_6393_; 
v_res_6393_ = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_evalPushCast___regBuiltin_Lean_Elab_Tactic_NormCast_evalPushCast_declRange__3();
return v_res_6393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg(){
_start:
{
lean_object* v___x_6395_; lean_object* v___x_6396_; 
v___x_6395_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabModCast_spec__0___redArg___closed__0);
v___x_6396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6396_, 0, v___x_6395_);
return v___x_6396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg___boxed(lean_object* v___y_6397_){
_start:
{
lean_object* v_res_6398_; 
v_res_6398_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg();
return v_res_6398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0(lean_object* v_00_u03b1_6399_, lean_object* v___y_6400_, lean_object* v___y_6401_){
_start:
{
lean_object* v___x_6403_; 
v___x_6403_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg();
return v___x_6403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___boxed(lean_object* v_00_u03b1_6404_, lean_object* v___y_6405_, lean_object* v___y_6406_, lean_object* v___y_6407_){
_start:
{
lean_object* v_res_6408_; 
v_res_6408_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0(v_00_u03b1_6404_, v___y_6405_, v___y_6406_);
lean_dec(v___y_6406_);
lean_dec_ref(v___y_6405_);
return v_res_6408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___lam__0(lean_object* v___x_6409_, lean_object* v___x_6410_, lean_object* v___x_6411_, lean_object* v___y_6412_, lean_object* v___y_6413_){
_start:
{
lean_object* v___x_6415_; lean_object* v___x_6416_; 
v___x_6415_ = lean_st_mk_ref(v___x_6409_);
v___x_6416_ = l_Lean_realizeGlobalConstNoOverload(v___x_6410_, v___y_6412_, v___y_6413_);
if (lean_obj_tag(v___x_6416_) == 0)
{
lean_object* v_a_6417_; uint8_t v___x_6418_; lean_object* v___x_6419_; lean_object* v___x_6420_; 
v_a_6417_ = lean_ctor_get(v___x_6416_, 0);
lean_inc(v_a_6417_);
lean_dec_ref(v___x_6416_);
v___x_6418_ = 0;
v___x_6419_ = lean_unsigned_to_nat(1000u);
v___x_6420_ = l_Lean_Meta_NormCast_addElim(v_a_6417_, v___x_6418_, v___x_6419_, v___x_6411_, v___x_6415_, v___y_6412_, v___y_6413_);
if (lean_obj_tag(v___x_6420_) == 0)
{
lean_object* v_a_6421_; lean_object* v___x_6423_; uint8_t v_isShared_6424_; uint8_t v_isSharedCheck_6429_; 
v_a_6421_ = lean_ctor_get(v___x_6420_, 0);
v_isSharedCheck_6429_ = !lean_is_exclusive(v___x_6420_);
if (v_isSharedCheck_6429_ == 0)
{
v___x_6423_ = v___x_6420_;
v_isShared_6424_ = v_isSharedCheck_6429_;
goto v_resetjp_6422_;
}
else
{
lean_inc(v_a_6421_);
lean_dec(v___x_6420_);
v___x_6423_ = lean_box(0);
v_isShared_6424_ = v_isSharedCheck_6429_;
goto v_resetjp_6422_;
}
v_resetjp_6422_:
{
lean_object* v___x_6425_; lean_object* v___x_6427_; 
v___x_6425_ = lean_st_ref_get(v___x_6415_);
lean_dec(v___x_6415_);
lean_dec(v___x_6425_);
if (v_isShared_6424_ == 0)
{
v___x_6427_ = v___x_6423_;
goto v_reusejp_6426_;
}
else
{
lean_object* v_reuseFailAlloc_6428_; 
v_reuseFailAlloc_6428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6428_, 0, v_a_6421_);
v___x_6427_ = v_reuseFailAlloc_6428_;
goto v_reusejp_6426_;
}
v_reusejp_6426_:
{
return v___x_6427_;
}
}
}
else
{
lean_dec(v___x_6415_);
return v___x_6420_;
}
}
else
{
lean_object* v_a_6430_; lean_object* v___x_6432_; uint8_t v_isShared_6433_; uint8_t v_isSharedCheck_6437_; 
lean_dec(v___x_6415_);
v_a_6430_ = lean_ctor_get(v___x_6416_, 0);
v_isSharedCheck_6437_ = !lean_is_exclusive(v___x_6416_);
if (v_isSharedCheck_6437_ == 0)
{
v___x_6432_ = v___x_6416_;
v_isShared_6433_ = v_isSharedCheck_6437_;
goto v_resetjp_6431_;
}
else
{
lean_inc(v_a_6430_);
lean_dec(v___x_6416_);
v___x_6432_ = lean_box(0);
v_isShared_6433_ = v_isSharedCheck_6437_;
goto v_resetjp_6431_;
}
v_resetjp_6431_:
{
lean_object* v___x_6435_; 
if (v_isShared_6433_ == 0)
{
v___x_6435_ = v___x_6432_;
goto v_reusejp_6434_;
}
else
{
lean_object* v_reuseFailAlloc_6436_; 
v_reuseFailAlloc_6436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6436_, 0, v_a_6430_);
v___x_6435_ = v_reuseFailAlloc_6436_;
goto v_reusejp_6434_;
}
v_reusejp_6434_:
{
return v___x_6435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___lam__0___boxed(lean_object* v___x_6438_, lean_object* v___x_6439_, lean_object* v___x_6440_, lean_object* v___y_6441_, lean_object* v___y_6442_, lean_object* v___y_6443_){
_start:
{
lean_object* v_res_6444_; 
v_res_6444_ = l_Lean_Elab_Tactic_NormCast_elabAddElim___lam__0(v___x_6438_, v___x_6439_, v___x_6440_, v___y_6441_, v___y_6442_);
lean_dec(v___y_6442_);
lean_dec_ref(v___y_6441_);
lean_dec_ref(v___x_6440_);
return v_res_6444_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__4(void){
_start:
{
lean_object* v___x_6454_; 
v___x_6454_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_6454_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5(void){
_start:
{
lean_object* v___x_6455_; lean_object* v___x_6456_; 
v___x_6455_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__4, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__4_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__4);
v___x_6456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6456_, 0, v___x_6455_);
return v___x_6456_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__6(void){
_start:
{
lean_object* v___x_6457_; lean_object* v___x_6458_; lean_object* v___x_6459_; 
v___x_6457_ = lean_unsigned_to_nat(32u);
v___x_6458_ = lean_mk_empty_array_with_capacity(v___x_6457_);
v___x_6459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6459_, 0, v___x_6458_);
return v___x_6459_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7(void){
_start:
{
size_t v___x_6460_; lean_object* v___x_6461_; lean_object* v___x_6462_; lean_object* v___x_6463_; lean_object* v___x_6464_; lean_object* v___x_6465_; 
v___x_6460_ = ((size_t)5ULL);
v___x_6461_ = lean_unsigned_to_nat(0u);
v___x_6462_ = lean_unsigned_to_nat(32u);
v___x_6463_ = lean_mk_empty_array_with_capacity(v___x_6462_);
v___x_6464_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__6, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__6_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__6);
v___x_6465_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6465_, 0, v___x_6464_);
lean_ctor_set(v___x_6465_, 1, v___x_6463_);
lean_ctor_set(v___x_6465_, 2, v___x_6461_);
lean_ctor_set(v___x_6465_, 3, v___x_6461_);
lean_ctor_set_usize(v___x_6465_, 4, v___x_6460_);
return v___x_6465_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__8(void){
_start:
{
lean_object* v___x_6466_; lean_object* v___x_6467_; lean_object* v___x_6468_; lean_object* v___x_6469_; 
v___x_6466_ = lean_box(1);
v___x_6467_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7);
v___x_6468_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5);
v___x_6469_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6469_, 0, v___x_6468_);
lean_ctor_set(v___x_6469_, 1, v___x_6467_);
lean_ctor_set(v___x_6469_, 2, v___x_6466_);
return v___x_6469_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__10(void){
_start:
{
lean_object* v___x_6472_; lean_object* v___x_6473_; lean_object* v___x_6474_; 
v___x_6472_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5);
v___x_6473_ = lean_unsigned_to_nat(0u);
v___x_6474_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_6474_, 0, v___x_6473_);
lean_ctor_set(v___x_6474_, 1, v___x_6473_);
lean_ctor_set(v___x_6474_, 2, v___x_6473_);
lean_ctor_set(v___x_6474_, 3, v___x_6473_);
lean_ctor_set(v___x_6474_, 4, v___x_6472_);
lean_ctor_set(v___x_6474_, 5, v___x_6472_);
lean_ctor_set(v___x_6474_, 6, v___x_6472_);
lean_ctor_set(v___x_6474_, 7, v___x_6472_);
lean_ctor_set(v___x_6474_, 8, v___x_6472_);
lean_ctor_set(v___x_6474_, 9, v___x_6472_);
return v___x_6474_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__11(void){
_start:
{
lean_object* v___x_6475_; lean_object* v___x_6476_; 
v___x_6475_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5);
v___x_6476_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_6476_, 0, v___x_6475_);
lean_ctor_set(v___x_6476_, 1, v___x_6475_);
lean_ctor_set(v___x_6476_, 2, v___x_6475_);
lean_ctor_set(v___x_6476_, 3, v___x_6475_);
lean_ctor_set(v___x_6476_, 4, v___x_6475_);
lean_ctor_set(v___x_6476_, 5, v___x_6475_);
return v___x_6476_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__12(void){
_start:
{
lean_object* v___x_6477_; lean_object* v___x_6478_; 
v___x_6477_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__5);
v___x_6478_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6478_, 0, v___x_6477_);
lean_ctor_set(v___x_6478_, 1, v___x_6477_);
lean_ctor_set(v___x_6478_, 2, v___x_6477_);
lean_ctor_set(v___x_6478_, 3, v___x_6477_);
lean_ctor_set(v___x_6478_, 4, v___x_6477_);
return v___x_6478_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__13(void){
_start:
{
lean_object* v___x_6479_; lean_object* v___x_6480_; lean_object* v___x_6481_; lean_object* v___x_6482_; lean_object* v___x_6483_; lean_object* v___x_6484_; 
v___x_6479_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__12, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__12_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__12);
v___x_6480_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__7);
v___x_6481_ = lean_box(1);
v___x_6482_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__11, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__11_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__11);
v___x_6483_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__10, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__10_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__10);
v___x_6484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6484_, 0, v___x_6483_);
lean_ctor_set(v___x_6484_, 1, v___x_6482_);
lean_ctor_set(v___x_6484_, 2, v___x_6481_);
lean_ctor_set(v___x_6484_, 3, v___x_6480_);
lean_ctor_set(v___x_6484_, 4, v___x_6479_);
return v___x_6484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim(lean_object* v_stx_6485_, lean_object* v_a_6486_, lean_object* v_a_6487_){
_start:
{
lean_object* v___x_6489_; uint8_t v___x_6490_; 
v___x_6489_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__1));
lean_inc(v_stx_6485_);
v___x_6490_ = l_Lean_Syntax_isOfKind(v_stx_6485_, v___x_6489_);
if (v___x_6490_ == 0)
{
lean_object* v___x_6491_; 
lean_dec(v_stx_6485_);
v___x_6491_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg();
return v___x_6491_;
}
else
{
lean_object* v___x_6492_; lean_object* v___x_6493_; lean_object* v___x_6494_; uint8_t v___x_6495_; 
v___x_6492_ = lean_unsigned_to_nat(1u);
v___x_6493_ = l_Lean_Syntax_getArg(v_stx_6485_, v___x_6492_);
lean_dec(v_stx_6485_);
v___x_6494_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__3));
lean_inc(v___x_6493_);
v___x_6495_ = l_Lean_Syntax_isOfKind(v___x_6493_, v___x_6494_);
if (v___x_6495_ == 0)
{
lean_object* v___x_6496_; 
lean_dec(v___x_6493_);
v___x_6496_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_NormCast_elabAddElim_spec__0___redArg();
return v___x_6496_;
}
else
{
lean_object* v___x_6497_; uint8_t v___x_6498_; uint8_t v___x_6499_; uint8_t v___x_6500_; uint8_t v___x_6501_; lean_object* v___x_6502_; uint64_t v___x_6503_; lean_object* v___x_6504_; lean_object* v___x_6505_; lean_object* v___x_6506_; lean_object* v___x_6507_; lean_object* v___x_6508_; lean_object* v___x_6509_; lean_object* v___x_6510_; lean_object* v___f_6511_; lean_object* v___x_6512_; 
v___x_6497_ = lean_unsigned_to_nat(0u);
v___x_6498_ = 0;
v___x_6499_ = 1;
v___x_6500_ = 0;
v___x_6501_ = 2;
v___x_6502_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_6502_, 0, v___x_6498_);
lean_ctor_set_uint8(v___x_6502_, 1, v___x_6498_);
lean_ctor_set_uint8(v___x_6502_, 2, v___x_6498_);
lean_ctor_set_uint8(v___x_6502_, 3, v___x_6498_);
lean_ctor_set_uint8(v___x_6502_, 4, v___x_6498_);
lean_ctor_set_uint8(v___x_6502_, 5, v___x_6495_);
lean_ctor_set_uint8(v___x_6502_, 6, v___x_6495_);
lean_ctor_set_uint8(v___x_6502_, 7, v___x_6498_);
lean_ctor_set_uint8(v___x_6502_, 8, v___x_6495_);
lean_ctor_set_uint8(v___x_6502_, 9, v___x_6499_);
lean_ctor_set_uint8(v___x_6502_, 10, v___x_6500_);
lean_ctor_set_uint8(v___x_6502_, 11, v___x_6495_);
lean_ctor_set_uint8(v___x_6502_, 12, v___x_6495_);
lean_ctor_set_uint8(v___x_6502_, 13, v___x_6495_);
lean_ctor_set_uint8(v___x_6502_, 14, v___x_6501_);
lean_ctor_set_uint8(v___x_6502_, 15, v___x_6495_);
lean_ctor_set_uint8(v___x_6502_, 16, v___x_6495_);
lean_ctor_set_uint8(v___x_6502_, 17, v___x_6495_);
lean_ctor_set_uint8(v___x_6502_, 18, v___x_6495_);
v___x_6503_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_6502_);
v___x_6504_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_6504_, 0, v___x_6502_);
lean_ctor_set_uint64(v___x_6504_, sizeof(void*)*1, v___x_6503_);
v___x_6505_ = lean_box(1);
v___x_6506_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__8, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__8_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__8);
v___x_6507_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__9));
v___x_6508_ = lean_box(0);
v___x_6509_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6509_, 0, v___x_6504_);
lean_ctor_set(v___x_6509_, 1, v___x_6505_);
lean_ctor_set(v___x_6509_, 2, v___x_6506_);
lean_ctor_set(v___x_6509_, 3, v___x_6507_);
lean_ctor_set(v___x_6509_, 4, v___x_6508_);
lean_ctor_set(v___x_6509_, 5, v___x_6497_);
lean_ctor_set(v___x_6509_, 6, v___x_6508_);
lean_ctor_set_uint8(v___x_6509_, sizeof(void*)*7, v___x_6498_);
lean_ctor_set_uint8(v___x_6509_, sizeof(void*)*7 + 1, v___x_6498_);
lean_ctor_set_uint8(v___x_6509_, sizeof(void*)*7 + 2, v___x_6498_);
lean_ctor_set_uint8(v___x_6509_, sizeof(void*)*7 + 3, v___x_6495_);
v___x_6510_ = lean_obj_once(&l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__13, &l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__13_once, _init_l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__13);
v___f_6511_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___lam__0___boxed), 6, 3);
lean_closure_set(v___f_6511_, 0, v___x_6510_);
lean_closure_set(v___f_6511_, 1, v___x_6493_);
lean_closure_set(v___f_6511_, 2, v___x_6509_);
v___x_6512_ = l_Lean_Elab_Command_liftCoreM___redArg(v___f_6511_, v_a_6486_, v_a_6487_);
return v___x_6512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_NormCast_elabAddElim___boxed(lean_object* v_stx_6513_, lean_object* v_a_6514_, lean_object* v_a_6515_, lean_object* v_a_6516_){
_start:
{
lean_object* v_res_6517_; 
v_res_6517_ = l_Lean_Elab_Tactic_NormCast_elabAddElim(v_stx_6513_, v_a_6514_, v_a_6515_);
lean_dec(v_a_6515_);
lean_dec_ref(v_a_6514_);
return v_res_6517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1(){
_start:
{
lean_object* v___x_6526_; lean_object* v___x_6527_; lean_object* v___x_6528_; lean_object* v___x_6529_; lean_object* v___x_6530_; 
v___x_6526_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_6527_ = ((lean_object*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___closed__1));
v___x_6528_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1));
v___x_6529_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_NormCast_elabAddElim___boxed), 4, 0);
v___x_6530_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_6526_, v___x_6527_, v___x_6528_, v___x_6529_);
return v___x_6530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___boxed(lean_object* v_a_6531_){
_start:
{
lean_object* v_res_6532_; 
v_res_6532_ = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1();
return v_res_6532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3(){
_start:
{
lean_object* v___x_6559_; lean_object* v___x_6560_; lean_object* v___x_6561_; 
v___x_6559_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim__1___closed__1));
v___x_6560_ = ((lean_object*)(l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___closed__6));
v___x_6561_ = l_Lean_addBuiltinDeclarationRanges(v___x_6559_, v___x_6560_);
return v___x_6561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3___boxed(lean_object* v_a_6562_){
_start:
{
lean_object* v_res_6563_; 
v_res_6563_ = l___private_Lean_Elab_Tactic_NormCast_0__Lean_Elab_Tactic_NormCast_elabAddElim___regBuiltin_Lean_Elab_Tactic_NormCast_elabAddElim_declRange__3();
return v_res_6563_;
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

// Lean compiler output
// Module: Lean.Meta.Tactic.Cbv.Main
// Imports: public import Lean.Meta.Sym.Simp.SimpM public import Lean.Meta.Tactic.Cbv.Opaque public import Lean.Meta.Tactic.Cbv.ControlFlow import Lean.Meta.Tactic.Cbv.BuiltinCbvSimprocs.Core import Lean.Meta.Tactic.Cbv.BuiltinCbvSimprocs.Array import Lean.Meta.Tactic.Cbv.BuiltinCbvSimprocs.String import Lean.Meta.Tactic.Cbv.Util import Lean.Meta.Tactic.Cbv.TheoremsLookup import Lean.Meta.Tactic.Cbv.CbvEvalExt import Lean.Meta.Tactic.Cbv.CbvSimproc import Lean.Meta.Sym import Lean.Meta.Tactic.Refl import Lean.Meta.Tactic.Replace import Lean.Meta.Tactic.Assert
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isBoolTrueExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_isBoolFalseExpr___redArg(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_preprocessMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_withContextDependent(lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_rawNatLit_x3f(lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommonInc___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkEqRefl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_reduceProj_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_inferType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
lean_object* l_Lean_Meta_Sym_isDefEqI___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_share1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Internal_Sym_assertShared(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_sym_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_div(double, double);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_dischargeNone___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorems_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_markAsDoneIfFailed(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
uint8_t l_Lean_ConstantInfo_isDefinition(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_hasValue(lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_tryMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Expr_letNondep_x21(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_expandLet(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Sym_Simp_toBetaApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_evalGround___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_getEqnTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Theorem_rewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_guardSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_simp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_Simp_Result_getResultExpr(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_SymM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Expr_isFalse(lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFalseElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assertHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_tryClearMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isTrue(lean_object*);
lean_object* l_Lean_MVarId_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_shareCommon___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "cbv"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "warning"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(97, 111, 157, 173, 138, 2, 95, 98)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(151, 83, 180, 186, 68, 143, 69, 30)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "When enabled, displays a warning that the `cbv` tactic is being used."};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Cbv"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(113, 161, 104, 89, 81, 29, 125, 142)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(163, 5, 44, 111, 124, 235, 200, 112)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(173, 215, 55, 92, 108, 32, 177, 243)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbv_warning;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "maxSteps"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(97, 111, 157, 173, 138, 2, 95, 98)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(101, 44, 76, 26, 207, 29, 243, 115)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "Controls the maximum number of steps for the `cbv` tactic."};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(7, 212, 55, 101, 104, 194, 19, 213)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(113, 161, 104, 89, 81, 29, 125, 142)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(163, 5, 44, 111, 124, 235, 200, 112)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__value_aux_4),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(79, 184, 28, 112, 238, 206, 34, 246)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "rewrite"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(180, 58, 216, 170, 2, 199, 127, 134)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__0_value),LEAN_SCALAR_PTR_LITERAL(174, 58, 109, 183, 100, 138, 243, 210)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__4;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "equation `"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__6;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`:"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "\n==>"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10;
static const lean_closure_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_dischargeNone___boxed, .m_arity = 11, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__11 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "unfold"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(180, 58, 216, 170, 2, 199, 127, 134)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 17, 43, 156, 90, 102, 144, 138)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "unfold `"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__3_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Debug"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "reduce"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(167, 248, 27, 31, 3, 126, 142, 13)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(119, 140, 6, 58, 231, 192, 8, 160)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(246, 39, 251, 153, 6, 255, 160, 132)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2_value_aux_2),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(16, 195, 245, 152, 44, 204, 206, 86)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2_value_aux_3),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(200, 16, 126, 88, 211, 46, 70, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "beta:"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "@[cbv_eval] `"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleOpaqueConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleOpaqueConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "foldLit: "};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " ==> "};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "zeta:"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "proj `"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__3;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ": stuck"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__5;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = ": no change"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__7;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__8 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___boxed(lean_object**);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "x"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__0_value),LEAN_SCALAR_PTR_LITERAL(243, 101, 181, 186, 114, 114, 131, 189)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "congrArg"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__3_value),LEAN_SCALAR_PTR_LITERAL(188, 17, 22, 243, 206, 91, 171, 36)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.Tactic.Cbv.Main"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__5 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__5_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 69, .m_capacity = 69, .m_length = 68, .m_data = "_private.Lean.Meta.Tactic.Cbv.Main.0.Lean.Meta.Tactic.Cbv.handleProj"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__6 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__7 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0;
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "simplifyAppFn:"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "const `"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 0}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cbv: "};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "cbv: no change"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cbv:"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0_value_aux_1),((lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(180, 58, 216, 170, 2, 199, 127, 134)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "target: "};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "target: no change"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "target:"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "hypothesis `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "`: no change"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__1_value),LEAN_SCALAR_PTR_LITERAL(183, 66, 254, 161, 210, 133, 94, 78)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_Tactic_Cbv_cbvGoalCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_cbvGoalCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_cbvGoalCore___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___boxed__const__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 88, .m_capacity = 88, .m_length = 87, .m_data = "`decide_cbv` failed: could not reduce the expression to a boolean value; got stuck at: "};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "`decide_cbv` failed: the proposition evaluates to `false`"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4_value;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "`decide_cbv`: expected goal of the form `decide _ = true`, got: "};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__5 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "decide_cbv:"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__7 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "decide_cbv: "};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1;
static const lean_string_object l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "decide_cbv: closed goal"};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__2 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_57_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4_));
v___x_59_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4_));
v___x_60_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4__spec__0(v___x_57_, v___x_58_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4____boxed(lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4_();
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__spec__0(lean_object* v_name_63_, lean_object* v_decl_64_, lean_object* v_ref_65_){
_start:
{
lean_object* v_defValue_67_; lean_object* v_descr_68_; lean_object* v_deprecation_x3f_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v_defValue_67_ = lean_ctor_get(v_decl_64_, 0);
v_descr_68_ = lean_ctor_get(v_decl_64_, 1);
v_deprecation_x3f_69_ = lean_ctor_get(v_decl_64_, 2);
lean_inc(v_defValue_67_);
v___x_70_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_70_, 0, v_defValue_67_);
lean_inc(v_deprecation_x3f_69_);
lean_inc_ref(v_descr_68_);
lean_inc_n(v_name_63_, 2);
v___x_71_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_71_, 0, v_name_63_);
lean_ctor_set(v___x_71_, 1, v_ref_65_);
lean_ctor_set(v___x_71_, 2, v___x_70_);
lean_ctor_set(v___x_71_, 3, v_descr_68_);
lean_ctor_set(v___x_71_, 4, v_deprecation_x3f_69_);
v___x_72_ = lean_register_option(v_name_63_, v___x_71_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_80_; 
v_isSharedCheck_80_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_80_ == 0)
{
lean_object* v_unused_81_; 
v_unused_81_ = lean_ctor_get(v___x_72_, 0);
lean_dec(v_unused_81_);
v___x_74_ = v___x_72_;
v_isShared_75_ = v_isSharedCheck_80_;
goto v_resetjp_73_;
}
else
{
lean_dec(v___x_72_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_80_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_76_; lean_object* v___x_78_; 
lean_inc(v_defValue_67_);
v___x_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_76_, 0, v_name_63_);
lean_ctor_set(v___x_76_, 1, v_defValue_67_);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 0, v___x_76_);
v___x_78_ = v___x_74_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_76_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
else
{
lean_object* v_a_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_89_; 
lean_dec(v_name_63_);
v_a_82_ = lean_ctor_get(v___x_72_, 0);
v_isSharedCheck_89_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_89_ == 0)
{
v___x_84_ = v___x_72_;
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_a_82_);
lean_dec(v___x_72_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_89_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v___x_87_; 
if (v_isShared_85_ == 0)
{
v___x_87_ = v___x_84_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v_a_82_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_90_, lean_object* v_decl_91_, lean_object* v_ref_92_, lean_object* v_a_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__spec__0(v_name_90_, v_decl_91_, v_ref_92_);
lean_dec_ref(v_decl_91_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_112_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4_));
v___x_113_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4_));
v___x_114_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4_));
v___x_115_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4__spec__0(v___x_112_, v___x_113_, v___x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4____boxed(lean_object* v_a_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4_();
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(lean_object* v_msgData_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v___x_124_; lean_object* v_env_125_; lean_object* v___x_126_; lean_object* v_mctx_127_; lean_object* v_lctx_128_; lean_object* v_options_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_124_ = lean_st_ref_get(v___y_122_);
v_env_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc_ref(v_env_125_);
lean_dec(v___x_124_);
v___x_126_ = lean_st_ref_get(v___y_120_);
v_mctx_127_ = lean_ctor_get(v___x_126_, 0);
lean_inc_ref(v_mctx_127_);
lean_dec(v___x_126_);
v_lctx_128_ = lean_ctor_get(v___y_119_, 2);
v_options_129_ = lean_ctor_get(v___y_121_, 2);
lean_inc_ref(v_options_129_);
lean_inc_ref(v_lctx_128_);
v___x_130_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_130_, 0, v_env_125_);
lean_ctor_set(v___x_130_, 1, v_mctx_127_);
lean_ctor_set(v___x_130_, 2, v_lctx_128_);
lean_ctor_set(v___x_130_, 3, v_options_129_);
v___x_131_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v_msgData_118_);
v___x_132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0___boxed(lean_object* v_msgData_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msgData_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
return v_res_139_;
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_140_; double v___x_141_; 
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = lean_float_of_nat(v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(lean_object* v_cls_145_, lean_object* v_msg_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_){
_start:
{
lean_object* v_ref_152_; lean_object* v___x_153_; lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_198_; 
v_ref_152_ = lean_ctor_get(v___y_149_, 5);
v___x_153_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
v_a_154_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_198_ == 0)
{
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_198_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_198_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v_traceState_159_; lean_object* v_env_160_; lean_object* v_nextMacroScope_161_; lean_object* v_ngen_162_; lean_object* v_auxDeclNGen_163_; lean_object* v_cache_164_; lean_object* v_messages_165_; lean_object* v_infoState_166_; lean_object* v_snapshotTasks_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_197_; 
v___x_158_ = lean_st_ref_take(v___y_150_);
v_traceState_159_ = lean_ctor_get(v___x_158_, 4);
v_env_160_ = lean_ctor_get(v___x_158_, 0);
v_nextMacroScope_161_ = lean_ctor_get(v___x_158_, 1);
v_ngen_162_ = lean_ctor_get(v___x_158_, 2);
v_auxDeclNGen_163_ = lean_ctor_get(v___x_158_, 3);
v_cache_164_ = lean_ctor_get(v___x_158_, 5);
v_messages_165_ = lean_ctor_get(v___x_158_, 6);
v_infoState_166_ = lean_ctor_get(v___x_158_, 7);
v_snapshotTasks_167_ = lean_ctor_get(v___x_158_, 8);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_197_ == 0)
{
v___x_169_ = v___x_158_;
v_isShared_170_ = v_isSharedCheck_197_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_snapshotTasks_167_);
lean_inc(v_infoState_166_);
lean_inc(v_messages_165_);
lean_inc(v_cache_164_);
lean_inc(v_traceState_159_);
lean_inc(v_auxDeclNGen_163_);
lean_inc(v_ngen_162_);
lean_inc(v_nextMacroScope_161_);
lean_inc(v_env_160_);
lean_dec(v___x_158_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_197_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
uint64_t v_tid_171_; lean_object* v_traces_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_196_; 
v_tid_171_ = lean_ctor_get_uint64(v_traceState_159_, sizeof(void*)*1);
v_traces_172_ = lean_ctor_get(v_traceState_159_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v_traceState_159_);
if (v_isSharedCheck_196_ == 0)
{
v___x_174_ = v_traceState_159_;
v_isShared_175_ = v_isSharedCheck_196_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_traces_172_);
lean_dec(v_traceState_159_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_196_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_176_; double v___x_177_; uint8_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_176_ = lean_box(0);
v___x_177_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
v___x_178_ = 0;
v___x_179_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_180_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_180_, 0, v_cls_145_);
lean_ctor_set(v___x_180_, 1, v___x_176_);
lean_ctor_set(v___x_180_, 2, v___x_179_);
lean_ctor_set_float(v___x_180_, sizeof(void*)*3, v___x_177_);
lean_ctor_set_float(v___x_180_, sizeof(void*)*3 + 8, v___x_177_);
lean_ctor_set_uint8(v___x_180_, sizeof(void*)*3 + 16, v___x_178_);
v___x_181_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__2));
v___x_182_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_182_, 0, v___x_180_);
lean_ctor_set(v___x_182_, 1, v_a_154_);
lean_ctor_set(v___x_182_, 2, v___x_181_);
lean_inc(v_ref_152_);
v___x_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_183_, 0, v_ref_152_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = l_Lean_PersistentArray_push___redArg(v_traces_172_, v___x_183_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 0, v___x_184_);
v___x_186_ = v___x_174_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v___x_184_);
lean_ctor_set_uint64(v_reuseFailAlloc_195_, sizeof(void*)*1, v_tid_171_);
v___x_186_ = v_reuseFailAlloc_195_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_188_; 
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 4, v___x_186_);
v___x_188_ = v___x_169_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_env_160_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v_nextMacroScope_161_);
lean_ctor_set(v_reuseFailAlloc_194_, 2, v_ngen_162_);
lean_ctor_set(v_reuseFailAlloc_194_, 3, v_auxDeclNGen_163_);
lean_ctor_set(v_reuseFailAlloc_194_, 4, v___x_186_);
lean_ctor_set(v_reuseFailAlloc_194_, 5, v_cache_164_);
lean_ctor_set(v_reuseFailAlloc_194_, 6, v_messages_165_);
lean_ctor_set(v_reuseFailAlloc_194_, 7, v_infoState_166_);
lean_ctor_set(v_reuseFailAlloc_194_, 8, v_snapshotTasks_167_);
v___x_188_ = v_reuseFailAlloc_194_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_192_; 
v___x_189_ = lean_st_ref_set(v___y_150_, v___x_188_);
v___x_190_ = lean_box(0);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v___x_190_);
v___x_192_ = v___x_156_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___boxed(lean_object* v_cls_199_, lean_object* v_msg_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_, lean_object* v___y_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v_cls_199_, v_msg_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_);
lean_dec(v___y_204_);
lean_dec_ref(v___y_203_);
lean_dec(v___y_202_);
lean_dec_ref(v___y_201_);
return v_res_206_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__4(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_216_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1));
v___x_217_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
v___x_218_ = l_Lean_Name_append(v___x_217_, v___x_216_);
return v___x_218_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__6(void){
_start:
{
lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_220_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__5));
v___x_221_ = l_Lean_stringToMessageData(v___x_220_);
return v___x_221_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__7));
v___x_224_ = l_Lean_stringToMessageData(v___x_223_);
return v___x_224_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10(void){
_start:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__9));
v___x_227_ = l_Lean_stringToMessageData(v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations(lean_object* v_e_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
uint8_t v___x_242_; 
v___x_242_ = l_Lean_Expr_isApp(v_e_231_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; lean_object* v___x_244_; 
lean_dec_ref(v_e_231_);
v___x_243_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_243_, 0, v___x_242_);
lean_ctor_set_uint8(v___x_243_, 1, v___x_242_);
v___x_244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
return v___x_244_;
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = l_Lean_Expr_getAppFn(v_e_231_);
v___x_246_ = l_Lean_Expr_constName_x3f(v___x_245_);
lean_dec_ref(v___x_245_);
if (lean_obj_tag(v___x_246_) == 1)
{
lean_object* v_val_247_; lean_object* v___y_249_; lean_object* v___x_286_; 
v_val_247_ = lean_ctor_get(v___x_246_, 0);
lean_inc_n(v_val_247_, 2);
lean_dec_ref_known(v___x_246_, 1);
v___x_286_ = l_Lean_Meta_Tactic_Cbv_getEqnTheorems(v_val_247_, v_a_237_, v_a_238_, v_a_239_, v_a_240_);
if (lean_obj_tag(v___x_286_) == 0)
{
lean_object* v_a_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v_a_287_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_a_287_);
lean_dec_ref_known(v___x_286_, 1);
v___x_288_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__11));
lean_inc_ref(v_e_231_);
v___x_289_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_a_287_, v___x_288_, v_e_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_);
lean_dec(v_a_287_);
if (lean_obj_tag(v___x_289_) == 0)
{
v___y_249_ = v___x_289_;
goto v___jp_248_;
}
else
{
lean_object* v_a_290_; uint8_t v___y_292_; uint8_t v___x_302_; 
v_a_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_a_290_);
v___x_302_ = l_Lean_Exception_isInterrupt(v_a_290_);
if (v___x_302_ == 0)
{
uint8_t v___x_303_; 
v___x_303_ = l_Lean_Exception_isRuntime(v_a_290_);
v___y_292_ = v___x_303_;
goto v___jp_291_;
}
else
{
lean_dec(v_a_290_);
v___y_292_ = v___x_302_;
goto v___jp_291_;
}
v___jp_291_:
{
if (v___y_292_ == 0)
{
lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_300_; 
lean_dec(v_val_247_);
lean_dec_ref(v_e_231_);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_300_ == 0)
{
lean_object* v_unused_301_; 
v_unused_301_ = lean_ctor_get(v___x_289_, 0);
lean_dec(v_unused_301_);
v___x_294_ = v___x_289_;
v_isShared_295_ = v_isSharedCheck_300_;
goto v_resetjp_293_;
}
else
{
lean_dec(v___x_289_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_300_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_296_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_296_, 0, v___y_292_);
lean_ctor_set_uint8(v___x_296_, 1, v___y_292_);
if (v_isShared_295_ == 0)
{
lean_ctor_set_tag(v___x_294_, 0);
lean_ctor_set(v___x_294_, 0, v___x_296_);
v___x_298_ = v___x_294_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
else
{
v___y_249_ = v___x_289_;
goto v___jp_248_;
}
}
}
}
else
{
lean_object* v_a_304_; lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_311_; 
lean_dec(v_val_247_);
lean_dec_ref(v_e_231_);
v_a_304_ = lean_ctor_get(v___x_286_, 0);
v_isSharedCheck_311_ = !lean_is_exclusive(v___x_286_);
if (v_isSharedCheck_311_ == 0)
{
v___x_306_ = v___x_286_;
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
else
{
lean_inc(v_a_304_);
lean_dec(v___x_286_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_311_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_309_; 
if (v_isShared_307_ == 0)
{
v___x_309_ = v___x_306_;
goto v_reusejp_308_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_a_304_);
v___x_309_ = v_reuseFailAlloc_310_;
goto v_reusejp_308_;
}
v_reusejp_308_:
{
return v___x_309_;
}
}
}
v___jp_248_:
{
if (lean_obj_tag(v___y_249_) == 0)
{
lean_object* v_a_250_; 
v_a_250_ = lean_ctor_get(v___y_249_, 0);
if (lean_obj_tag(v_a_250_) == 1)
{
lean_object* v_options_251_; uint8_t v_hasTrace_252_; 
v_options_251_ = lean_ctor_get(v_a_239_, 2);
v_hasTrace_252_ = lean_ctor_get_uint8(v_options_251_, sizeof(void*)*1);
if (v_hasTrace_252_ == 0)
{
lean_dec(v_val_247_);
lean_dec_ref(v_e_231_);
return v___y_249_;
}
else
{
lean_object* v_e_x27_253_; lean_object* v_inheritedTraceOptions_254_; lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v_e_x27_253_ = lean_ctor_get(v_a_250_, 0);
v_inheritedTraceOptions_254_ = lean_ctor_get(v_a_239_, 13);
v___x_255_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1));
v___x_256_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__4, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__4);
v___x_257_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_254_, v_options_251_, v___x_256_);
if (v___x_257_ == 0)
{
lean_dec(v_val_247_);
lean_dec_ref(v_e_231_);
return v___y_249_;
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
lean_inc_ref(v_a_250_);
lean_dec_ref_known(v___y_249_, 1);
v___x_258_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__6, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__6_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__6);
v___x_259_ = l_Lean_MessageData_ofName(v_val_247_);
v___x_260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_258_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8);
v___x_262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_260_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = l_Lean_indentExpr(v_e_231_);
v___x_264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_262_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
v___x_265_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_266_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_264_);
lean_ctor_set(v___x_266_, 1, v___x_265_);
lean_inc_ref(v_e_x27_253_);
v___x_267_ = l_Lean_indentExpr(v_e_x27_253_);
v___x_268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_266_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___x_269_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_255_, v___x_268_, v_a_237_, v_a_238_, v_a_239_, v_a_240_);
if (lean_obj_tag(v___x_269_) == 0)
{
lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_276_ == 0)
{
lean_object* v_unused_277_; 
v_unused_277_ = lean_ctor_get(v___x_269_, 0);
lean_dec(v_unused_277_);
v___x_271_ = v___x_269_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_dec(v___x_269_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
lean_ctor_set(v___x_271_, 0, v_a_250_);
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_250_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
lean_dec_ref_known(v_a_250_, 2);
v_a_278_ = lean_ctor_get(v___x_269_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_269_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_269_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_269_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
}
else
{
lean_dec(v_val_247_);
lean_dec_ref(v_e_231_);
return v___y_249_;
}
}
else
{
lean_dec(v_val_247_);
lean_dec_ref(v_e_231_);
return v___y_249_;
}
}
}
else
{
lean_object* v___x_312_; lean_object* v___x_313_; 
lean_dec(v___x_246_);
lean_dec_ref(v_e_231_);
v___x_312_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
return v___x_313_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___boxed(lean_object* v_e_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations(v_e_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
lean_dec(v_a_317_);
lean_dec_ref(v_a_316_);
lean_dec(v_a_315_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0(lean_object* v_cls_326_, lean_object* v_msg_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v_cls_326_, v_msg_327_, v___y_333_, v___y_334_, v___y_335_, v___y_336_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___boxed(lean_object* v_cls_339_, lean_object* v_msg_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0(v_cls_339_, v_msg_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v___y_347_);
lean_dec_ref(v___y_346_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
return v_res_351_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_358_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1));
v___x_359_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
v___x_360_ = l_Lean_Name_append(v___x_359_, v___x_358_);
return v___x_360_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__4(void){
_start:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__3));
v___x_363_ = l_Lean_stringToMessageData(v___x_362_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold(lean_object* v_e_364_, lean_object* v_a_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
uint8_t v___x_375_; 
v___x_375_ = l_Lean_Expr_isApp(v_e_364_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; lean_object* v___x_377_; 
lean_dec_ref(v_e_364_);
v___x_376_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_376_, 0, v___x_375_);
lean_ctor_set_uint8(v___x_376_, 1, v___x_375_);
v___x_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
return v___x_377_;
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = l_Lean_Expr_getAppFn(v_e_364_);
v___x_379_ = l_Lean_Expr_constName_x3f(v___x_378_);
lean_dec_ref(v___x_378_);
if (lean_obj_tag(v___x_379_) == 1)
{
lean_object* v_val_380_; lean_object* v___y_382_; lean_object* v___x_419_; 
v_val_380_ = lean_ctor_get(v___x_379_, 0);
lean_inc_n(v_val_380_, 2);
lean_dec_ref_known(v___x_379_, 1);
v___x_419_ = l_Lean_Meta_Tactic_Cbv_getUnfoldTheorem(v_val_380_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
if (lean_obj_tag(v___x_419_) == 0)
{
lean_object* v_a_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_445_; 
v_a_420_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_445_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_445_ == 0)
{
v___x_422_ = v___x_419_;
v_isShared_423_ = v_isSharedCheck_445_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_a_420_);
lean_dec(v___x_419_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_445_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
if (lean_obj_tag(v_a_420_) == 1)
{
lean_object* v_val_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
lean_del_object(v___x_422_);
v_val_424_ = lean_ctor_get(v_a_420_, 0);
lean_inc(v_val_424_);
lean_dec_ref_known(v_a_420_, 1);
v___x_425_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__11));
lean_inc_ref(v_e_364_);
v___x_426_ = l_Lean_Meta_Sym_Simp_Theorem_rewrite(v_val_424_, v_e_364_, v___x_425_, v_a_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
if (lean_obj_tag(v___x_426_) == 0)
{
v___y_382_ = v___x_426_;
goto v___jp_381_;
}
else
{
lean_object* v_a_427_; uint8_t v___y_429_; uint8_t v___x_439_; 
v_a_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc(v_a_427_);
v___x_439_ = l_Lean_Exception_isInterrupt(v_a_427_);
if (v___x_439_ == 0)
{
uint8_t v___x_440_; 
v___x_440_ = l_Lean_Exception_isRuntime(v_a_427_);
v___y_429_ = v___x_440_;
goto v___jp_428_;
}
else
{
lean_dec(v_a_427_);
v___y_429_ = v___x_439_;
goto v___jp_428_;
}
v___jp_428_:
{
if (v___y_429_ == 0)
{
lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_437_; 
lean_dec(v_val_380_);
lean_dec_ref(v_e_364_);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_426_);
if (v_isSharedCheck_437_ == 0)
{
lean_object* v_unused_438_; 
v_unused_438_ = lean_ctor_get(v___x_426_, 0);
lean_dec(v_unused_438_);
v___x_431_ = v___x_426_;
v_isShared_432_ = v_isSharedCheck_437_;
goto v_resetjp_430_;
}
else
{
lean_dec(v___x_426_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_437_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v___x_435_; 
v___x_433_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_433_, 0, v___y_429_);
lean_ctor_set_uint8(v___x_433_, 1, v___y_429_);
if (v_isShared_432_ == 0)
{
lean_ctor_set_tag(v___x_431_, 0);
lean_ctor_set(v___x_431_, 0, v___x_433_);
v___x_435_ = v___x_431_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
else
{
v___y_382_ = v___x_426_;
goto v___jp_381_;
}
}
}
}
else
{
lean_object* v___x_441_; lean_object* v___x_443_; 
lean_dec(v_a_420_);
lean_dec(v_val_380_);
lean_dec_ref(v_e_364_);
v___x_441_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_441_);
v___x_443_ = v___x_422_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_441_);
v___x_443_ = v_reuseFailAlloc_444_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
return v___x_443_;
}
}
}
}
else
{
lean_object* v_a_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_453_; 
lean_dec(v_val_380_);
lean_dec_ref(v_e_364_);
v_a_446_ = lean_ctor_get(v___x_419_, 0);
v_isSharedCheck_453_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_453_ == 0)
{
v___x_448_ = v___x_419_;
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_a_446_);
lean_dec(v___x_419_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_453_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_451_; 
if (v_isShared_449_ == 0)
{
v___x_451_ = v___x_448_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_a_446_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
v___jp_381_:
{
if (lean_obj_tag(v___y_382_) == 0)
{
lean_object* v_a_383_; 
v_a_383_ = lean_ctor_get(v___y_382_, 0);
if (lean_obj_tag(v_a_383_) == 1)
{
lean_object* v_options_384_; uint8_t v_hasTrace_385_; 
v_options_384_ = lean_ctor_get(v_a_372_, 2);
v_hasTrace_385_ = lean_ctor_get_uint8(v_options_384_, sizeof(void*)*1);
if (v_hasTrace_385_ == 0)
{
lean_dec(v_val_380_);
lean_dec_ref(v_e_364_);
return v___y_382_;
}
else
{
lean_object* v_e_x27_386_; lean_object* v_inheritedTraceOptions_387_; lean_object* v___x_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v_e_x27_386_ = lean_ctor_get(v_a_383_, 0);
v_inheritedTraceOptions_387_ = lean_ctor_get(v_a_372_, 13);
v___x_388_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1));
v___x_389_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2);
v___x_390_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_387_, v_options_384_, v___x_389_);
if (v___x_390_ == 0)
{
lean_dec(v_val_380_);
lean_dec_ref(v_e_364_);
return v___y_382_;
}
else
{
lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
lean_inc_ref(v_a_383_);
lean_dec_ref_known(v___y_382_, 1);
v___x_391_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__4, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__4);
v___x_392_ = l_Lean_MessageData_ofName(v_val_380_);
v___x_393_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_391_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
v___x_394_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8);
v___x_395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_393_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_396_ = l_Lean_indentExpr(v_e_364_);
v___x_397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_395_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
v___x_398_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_399_, 0, v___x_397_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
lean_inc_ref(v_e_x27_386_);
v___x_400_ = l_Lean_indentExpr(v_e_x27_386_);
v___x_401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_399_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_388_, v___x_401_, v_a_370_, v_a_371_, v_a_372_, v_a_373_);
if (lean_obj_tag(v___x_402_) == 0)
{
lean_object* v___x_404_; uint8_t v_isShared_405_; uint8_t v_isSharedCheck_409_; 
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; 
v_unused_410_ = lean_ctor_get(v___x_402_, 0);
lean_dec(v_unused_410_);
v___x_404_ = v___x_402_;
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
else
{
lean_dec(v___x_402_);
v___x_404_ = lean_box(0);
v_isShared_405_ = v_isSharedCheck_409_;
goto v_resetjp_403_;
}
v_resetjp_403_:
{
lean_object* v___x_407_; 
if (v_isShared_405_ == 0)
{
lean_ctor_set(v___x_404_, 0, v_a_383_);
v___x_407_ = v___x_404_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_a_383_);
v___x_407_ = v_reuseFailAlloc_408_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
return v___x_407_;
}
}
}
else
{
lean_object* v_a_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_418_; 
lean_dec_ref_known(v_a_383_, 2);
v_a_411_ = lean_ctor_get(v___x_402_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_402_);
if (v_isSharedCheck_418_ == 0)
{
v___x_413_ = v___x_402_;
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_a_411_);
lean_dec(v___x_402_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_418_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
if (v_isShared_414_ == 0)
{
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
}
}
else
{
lean_dec(v_val_380_);
lean_dec_ref(v_e_364_);
return v___y_382_;
}
}
else
{
lean_dec(v_val_380_);
lean_dec_ref(v_e_364_);
return v___y_382_;
}
}
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; 
lean_dec(v___x_379_);
lean_dec_ref(v_e_364_);
v___x_454_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
return v___x_455_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___boxed(lean_object* v_e_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold(v_e_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_);
lean_dec(v_a_465_);
lean_dec_ref(v_a_464_);
lean_dec(v_a_463_);
lean_dec_ref(v_a_462_);
lean_dec(v_a_461_);
lean_dec_ref(v_a_460_);
lean_dec(v_a_459_);
lean_dec_ref(v_a_458_);
lean_dec(v_a_457_);
return v_res_467_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_477_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
v___x_478_ = l_Lean_Name_append(v___x_477_, v___x_476_);
return v___x_478_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__5(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__4));
v___x_481_ = l_Lean_stringToMessageData(v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg(lean_object* v_e_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
lean_object* v_new_489_; lean_object* v___x_490_; 
lean_inc_ref(v_e_482_);
v_new_489_ = l_Lean_Expr_headBeta(v_e_482_);
v___x_490_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_new_489_, v_a_483_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v_options_517_; uint8_t v_hasTrace_518_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v___x_490_, 1);
v_options_517_ = lean_ctor_get(v_a_486_, 2);
v_hasTrace_518_ = lean_ctor_get_uint8(v_options_517_, sizeof(void*)*1);
if (v_hasTrace_518_ == 0)
{
lean_dec_ref(v_e_482_);
v___y_493_ = v_a_483_;
v___y_494_ = v_a_484_;
v___y_495_ = v_a_485_;
v___y_496_ = v_a_486_;
v___y_497_ = v_a_487_;
goto v___jp_492_;
}
else
{
lean_object* v_inheritedTraceOptions_519_; lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v_inheritedTraceOptions_519_ = lean_ctor_get(v_a_486_, 13);
v___x_520_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_521_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3);
v___x_522_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_519_, v_options_517_, v___x_521_);
if (v___x_522_ == 0)
{
lean_dec_ref(v_e_482_);
v___y_493_ = v_a_483_;
v___y_494_ = v_a_484_;
v___y_495_ = v_a_485_;
v___y_496_ = v_a_486_;
v___y_497_ = v_a_487_;
goto v___jp_492_;
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_523_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__5, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__5);
v___x_524_ = l_Lean_indentExpr(v_e_482_);
v___x_525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_525_, 0, v___x_523_);
lean_ctor_set(v___x_525_, 1, v___x_524_);
v___x_526_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
lean_inc(v_a_491_);
v___x_528_ = l_Lean_indentExpr(v_a_491_);
v___x_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
v___x_530_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_520_, v___x_529_, v_a_484_, v_a_485_, v_a_486_, v_a_487_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_dec_ref_known(v___x_530_, 1);
v___y_493_ = v_a_483_;
v___y_494_ = v_a_484_;
v___y_495_ = v_a_485_;
v___y_496_ = v_a_486_;
v___y_497_ = v_a_487_;
goto v___jp_492_;
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec(v_a_491_);
v_a_531_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_530_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_530_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
v___jp_492_:
{
lean_object* v___x_498_; 
lean_inc(v_a_491_);
v___x_498_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_491_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_508_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_508_ == 0)
{
v___x_501_ = v___x_498_;
v_isShared_502_ = v_isSharedCheck_508_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_a_499_);
lean_dec(v___x_498_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_508_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
uint8_t v___x_503_; lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_503_ = 0;
v___x_504_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_504_, 0, v_a_491_);
lean_ctor_set(v___x_504_, 1, v_a_499_);
lean_ctor_set_uint8(v___x_504_, sizeof(void*)*2, v___x_503_);
lean_ctor_set_uint8(v___x_504_, sizeof(void*)*2 + 1, v___x_503_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_504_);
v___x_506_ = v___x_501_;
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
else
{
lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_516_; 
lean_dec(v_a_491_);
v_a_509_ = lean_ctor_get(v___x_498_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_516_ == 0)
{
v___x_511_ = v___x_498_;
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_498_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_516_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_512_ == 0)
{
v___x_514_ = v___x_511_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_a_509_);
v___x_514_ = v_reuseFailAlloc_515_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
return v___x_514_;
}
}
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec_ref(v_e_482_);
v_a_539_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_490_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_490_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___boxed(lean_object* v_e_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg(v_e_547_, v_a_548_, v_a_549_, v_a_550_, v_a_551_, v_a_552_);
lean_dec(v_a_552_);
lean_dec_ref(v_a_551_);
lean_dec(v_a_550_);
lean_dec_ref(v_a_549_);
lean_dec(v_a_548_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce(lean_object* v_e_555_, lean_object* v_a_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg(v_e_555_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___boxed(lean_object* v_e_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce(v_e_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
lean_dec(v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec_ref(v_a_573_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
lean_dec(v_a_568_);
return v_res_578_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__1(void){
_start:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__0));
v___x_581_ = l_Lean_stringToMessageData(v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(lean_object* v_e_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = l_Lean_Expr_getAppFn(v_e_582_);
v___x_594_ = l_Lean_Expr_constName_x3f(v___x_593_);
lean_dec_ref(v___x_593_);
if (lean_obj_tag(v___x_594_) == 1)
{
lean_object* v_val_595_; lean_object* v___y_597_; lean_object* v___x_634_; 
v_val_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_val_595_);
lean_dec_ref_known(v___x_594_, 1);
v___x_634_ = l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas___redArg(v_val_595_, v_a_591_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_660_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_660_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_660_ == 0)
{
v___x_637_ = v___x_634_;
v_isShared_638_ = v_isSharedCheck_660_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_634_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_660_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
if (lean_obj_tag(v_a_635_) == 1)
{
lean_object* v_val_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
lean_del_object(v___x_637_);
v_val_639_ = lean_ctor_get(v_a_635_, 0);
lean_inc(v_val_639_);
lean_dec_ref_known(v_a_635_, 1);
v___x_640_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__11));
lean_inc_ref(v_e_582_);
v___x_641_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_val_639_, v___x_640_, v_e_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_);
lean_dec(v_val_639_);
if (lean_obj_tag(v___x_641_) == 0)
{
v___y_597_ = v___x_641_;
goto v___jp_596_;
}
else
{
lean_object* v_a_642_; uint8_t v___y_644_; uint8_t v___x_654_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_a_642_);
v___x_654_ = l_Lean_Exception_isInterrupt(v_a_642_);
if (v___x_654_ == 0)
{
uint8_t v___x_655_; 
v___x_655_ = l_Lean_Exception_isRuntime(v_a_642_);
v___y_644_ = v___x_655_;
goto v___jp_643_;
}
else
{
lean_dec(v_a_642_);
v___y_644_ = v___x_654_;
goto v___jp_643_;
}
v___jp_643_:
{
if (v___y_644_ == 0)
{
lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_652_; 
lean_dec(v_val_595_);
lean_dec_ref(v_e_582_);
v_isSharedCheck_652_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_652_ == 0)
{
lean_object* v_unused_653_; 
v_unused_653_ = lean_ctor_get(v___x_641_, 0);
lean_dec(v_unused_653_);
v___x_646_ = v___x_641_;
v_isShared_647_ = v_isSharedCheck_652_;
goto v_resetjp_645_;
}
else
{
lean_dec(v___x_641_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_652_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_648_; lean_object* v___x_650_; 
v___x_648_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_648_, 0, v___y_644_);
lean_ctor_set_uint8(v___x_648_, 1, v___y_644_);
if (v_isShared_647_ == 0)
{
lean_ctor_set_tag(v___x_646_, 0);
lean_ctor_set(v___x_646_, 0, v___x_648_);
v___x_650_ = v___x_646_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
}
else
{
v___y_597_ = v___x_641_;
goto v___jp_596_;
}
}
}
}
else
{
lean_object* v___x_656_; lean_object* v___x_658_; 
lean_dec(v_a_635_);
lean_dec(v_val_595_);
lean_dec_ref(v_e_582_);
v___x_656_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 0, v___x_656_);
v___x_658_ = v___x_637_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v___x_656_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec(v_val_595_);
lean_dec_ref(v_e_582_);
v_a_661_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_634_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_634_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
v___jp_596_:
{
if (lean_obj_tag(v___y_597_) == 0)
{
lean_object* v_a_598_; 
v_a_598_ = lean_ctor_get(v___y_597_, 0);
if (lean_obj_tag(v_a_598_) == 1)
{
lean_object* v_options_599_; uint8_t v_hasTrace_600_; 
v_options_599_ = lean_ctor_get(v_a_590_, 2);
v_hasTrace_600_ = lean_ctor_get_uint8(v_options_599_, sizeof(void*)*1);
if (v_hasTrace_600_ == 0)
{
lean_dec(v_val_595_);
lean_dec_ref(v_e_582_);
return v___y_597_;
}
else
{
lean_object* v_e_x27_601_; lean_object* v_inheritedTraceOptions_602_; lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v_e_x27_601_ = lean_ctor_get(v_a_598_, 0);
v_inheritedTraceOptions_602_ = lean_ctor_get(v_a_590_, 13);
v___x_603_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1));
v___x_604_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__4, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__4);
v___x_605_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_602_, v_options_599_, v___x_604_);
if (v___x_605_ == 0)
{
lean_dec(v_val_595_);
lean_dec_ref(v_e_582_);
return v___y_597_;
}
else
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
lean_inc_ref(v_a_598_);
lean_dec_ref_known(v___y_597_, 1);
v___x_606_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__1);
v___x_607_ = l_Lean_MessageData_ofName(v_val_595_);
v___x_608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_606_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8);
v___x_610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_608_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = l_Lean_indentExpr(v_e_582_);
v___x_612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_610_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_612_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
lean_inc_ref(v_e_x27_601_);
v___x_615_ = l_Lean_indentExpr(v_e_x27_601_);
v___x_616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_614_);
lean_ctor_set(v___x_616_, 1, v___x_615_);
v___x_617_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_603_, v___x_616_, v_a_588_, v_a_589_, v_a_590_, v_a_591_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_624_; 
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_624_ == 0)
{
lean_object* v_unused_625_; 
v_unused_625_ = lean_ctor_get(v___x_617_, 0);
lean_dec(v_unused_625_);
v___x_619_ = v___x_617_;
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
else
{
lean_dec(v___x_617_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_624_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_622_; 
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v_a_598_);
v___x_622_ = v___x_619_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v_a_598_);
v___x_622_ = v_reuseFailAlloc_623_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
return v___x_622_;
}
}
}
else
{
lean_object* v_a_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_633_; 
lean_dec_ref_known(v_a_598_, 2);
v_a_626_ = lean_ctor_get(v___x_617_, 0);
v_isSharedCheck_633_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_633_ == 0)
{
v___x_628_ = v___x_617_;
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_a_626_);
lean_dec(v___x_617_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_633_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_631_; 
if (v_isShared_629_ == 0)
{
v___x_631_ = v___x_628_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_a_626_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
}
}
}
}
else
{
lean_dec(v_val_595_);
lean_dec_ref(v_e_582_);
return v___y_597_;
}
}
else
{
lean_dec(v_val_595_);
lean_dec_ref(v_e_582_);
return v___y_597_;
}
}
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; 
lean_dec(v___x_594_);
lean_dec_ref(v_e_582_);
v___x_669_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
return v___x_670_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___boxed(lean_object* v_e_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v_e_671_, v_a_672_, v_a_673_, v_a_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_);
lean_dec(v_a_680_);
lean_dec_ref(v_a_679_);
lean_dec(v_a_678_);
lean_dec_ref(v_a_677_);
lean_dec(v_a_676_);
lean_dec_ref(v_a_675_);
lean_dec(v_a_674_);
lean_dec_ref(v_a_673_);
lean_dec(v_a_672_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp(lean_object* v_e_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_){
_start:
{
lean_object* v___x_694_; 
lean_inc_ref(v_e_683_);
v___x_694_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations(v_e_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
if (lean_obj_tag(v_a_695_) == 0)
{
uint8_t v_done_696_; 
v_done_696_ = lean_ctor_get_uint8(v_a_695_, 0);
if (v_done_696_ == 0)
{
uint8_t v_contextDependent_697_; lean_object* v___x_698_; 
lean_dec_ref_known(v___x_694_, 1);
v_contextDependent_697_ = lean_ctor_get_uint8(v_a_695_, 1);
lean_dec_ref_known(v_a_695_, 0);
v___x_698_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold(v_e_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; uint8_t v___y_701_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
if (v_contextDependent_697_ == 0)
{
lean_dec(v_a_699_);
return v___x_698_;
}
else
{
if (lean_obj_tag(v_a_699_) == 0)
{
uint8_t v_contextDependent_711_; 
v_contextDependent_711_ = lean_ctor_get_uint8(v_a_699_, 1);
v___y_701_ = v_contextDependent_711_;
goto v___jp_700_;
}
else
{
uint8_t v_contextDependent_712_; 
v_contextDependent_712_ = lean_ctor_get_uint8(v_a_699_, sizeof(void*)*2 + 1);
v___y_701_ = v_contextDependent_712_;
goto v___jp_700_;
}
}
v___jp_700_:
{
if (v___y_701_ == 0)
{
lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_709_; 
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; 
v_unused_710_ = lean_ctor_get(v___x_698_, 0);
lean_dec(v_unused_710_);
v___x_703_ = v___x_698_;
v_isShared_704_ = v_isSharedCheck_709_;
goto v_resetjp_702_;
}
else
{
lean_dec(v___x_698_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_709_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v___x_707_; 
v___x_705_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_699_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_705_);
v___x_707_ = v___x_703_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
else
{
lean_dec(v_a_699_);
return v___x_698_;
}
}
}
else
{
return v___x_698_;
}
}
else
{
lean_dec_ref_known(v_a_695_, 0);
lean_dec_ref(v_e_683_);
return v___x_694_;
}
}
else
{
lean_dec_ref_known(v_a_695_, 2);
lean_dec_ref(v_e_683_);
return v___x_694_;
}
}
else
{
lean_dec_ref(v_e_683_);
return v___x_694_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp___boxed(lean_object* v_e_713_, lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp(v_e_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_);
lean_dec(v_a_722_);
lean_dec_ref(v_a_721_);
lean_dec(v_a_720_);
lean_dec_ref(v_a_719_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
lean_dec_ref(v_a_715_);
lean_dec(v_a_714_);
return v_res_724_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0(lean_object* v_a_725_, uint8_t v_done_726_, lean_object* v_x_727_){
_start:
{
uint8_t v___x_728_; 
v___x_728_ = l_Lean_ConstantInfo_hasValue(v_a_725_, v_done_726_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0___boxed(lean_object* v_a_729_, lean_object* v_done_730_, lean_object* v_x_731_){
_start:
{
uint8_t v_done_18197__boxed_732_; uint8_t v_res_733_; lean_object* v_r_734_; 
v_done_18197__boxed_732_ = lean_unbox(v_done_730_);
v_res_733_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0(v_a_729_, v_done_18197__boxed_732_, v_x_731_);
lean_dec_ref(v_x_731_);
lean_dec_ref(v_a_729_);
v_r_734_ = lean_box(v_res_733_);
return v_r_734_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_735_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
return v___x_737_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_738_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
lean_ctor_set(v___x_740_, 2, v___x_739_);
lean_ctor_set(v___x_740_, 3, v___x_739_);
lean_ctor_set(v___x_740_, 4, v___x_738_);
lean_ctor_set(v___x_740_, 5, v___x_738_);
lean_ctor_set(v___x_740_, 6, v___x_738_);
lean_ctor_set(v___x_740_, 7, v___x_738_);
lean_ctor_set(v___x_740_, 8, v___x_738_);
lean_ctor_set(v___x_740_, 9, v___x_738_);
return v___x_740_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_741_ = lean_unsigned_to_nat(32u);
v___x_742_ = lean_mk_empty_array_with_capacity(v___x_741_);
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
return v___x_743_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_744_ = ((size_t)5ULL);
v___x_745_ = lean_unsigned_to_nat(0u);
v___x_746_ = lean_unsigned_to_nat(32u);
v___x_747_ = lean_mk_empty_array_with_capacity(v___x_746_);
v___x_748_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_749_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_749_, 0, v___x_748_);
lean_ctor_set(v___x_749_, 1, v___x_747_);
lean_ctor_set(v___x_749_, 2, v___x_745_);
lean_ctor_set(v___x_749_, 3, v___x_745_);
lean_ctor_set_usize(v___x_749_, 4, v___x_744_);
return v___x_749_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_750_ = lean_box(1);
v___x_751_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_752_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_753_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v___x_751_);
lean_ctor_set(v___x_753_, 2, v___x_750_);
return v___x_753_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_756_ = l_Lean_stringToMessageData(v___x_755_);
return v___x_756_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_759_ = l_Lean_stringToMessageData(v___x_758_);
return v___x_759_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_762_ = l_Lean_stringToMessageData(v___x_761_);
return v___x_762_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_765_ = l_Lean_stringToMessageData(v___x_764_);
return v___x_765_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_768_ = l_Lean_stringToMessageData(v___x_767_);
return v___x_768_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_771_ = l_Lean_stringToMessageData(v___x_770_);
return v___x_771_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_774_ = l_Lean_stringToMessageData(v___x_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_775_, lean_object* v_declHint_776_, lean_object* v___y_777_){
_start:
{
lean_object* v___x_779_; lean_object* v_env_780_; uint8_t v___x_781_; 
v___x_779_ = lean_st_ref_get(v___y_777_);
v_env_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc_ref(v_env_780_);
lean_dec(v___x_779_);
v___x_781_ = l_Lean_Name_isAnonymous(v_declHint_776_);
if (v___x_781_ == 0)
{
uint8_t v_isExporting_782_; 
v_isExporting_782_ = lean_ctor_get_uint8(v_env_780_, sizeof(void*)*8);
if (v_isExporting_782_ == 0)
{
lean_object* v___x_783_; 
lean_dec_ref(v_env_780_);
lean_dec(v_declHint_776_);
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v_msg_775_);
return v___x_783_;
}
else
{
lean_object* v___x_784_; uint8_t v___x_785_; 
lean_inc_ref(v_env_780_);
v___x_784_ = l_Lean_Environment_setExporting(v_env_780_, v___x_781_);
lean_inc(v_declHint_776_);
lean_inc_ref(v___x_784_);
v___x_785_ = l_Lean_Environment_contains(v___x_784_, v_declHint_776_, v_isExporting_782_);
if (v___x_785_ == 0)
{
lean_object* v___x_786_; 
lean_dec_ref(v___x_784_);
lean_dec_ref(v_env_780_);
lean_dec(v_declHint_776_);
v___x_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_786_, 0, v_msg_775_);
return v___x_786_;
}
else
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v_c_792_; lean_object* v___x_793_; 
v___x_787_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_788_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_789_ = l_Lean_Options_empty;
v___x_790_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_790_, 0, v___x_784_);
lean_ctor_set(v___x_790_, 1, v___x_787_);
lean_ctor_set(v___x_790_, 2, v___x_788_);
lean_ctor_set(v___x_790_, 3, v___x_789_);
lean_inc(v_declHint_776_);
v___x_791_ = l_Lean_MessageData_ofConstName(v_declHint_776_, v___x_781_);
v_c_792_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_792_, 0, v___x_790_);
lean_ctor_set(v_c_792_, 1, v___x_791_);
v___x_793_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_780_, v_declHint_776_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec_ref(v_env_780_);
lean_dec(v_declHint_776_);
v___x_794_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
lean_ctor_set(v___x_795_, 1, v_c_792_);
v___x_796_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_795_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = l_Lean_MessageData_note(v___x_797_);
v___x_799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_799_, 0, v_msg_775_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
return v___x_800_;
}
else
{
lean_object* v_val_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_836_; 
v_val_801_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_836_ == 0)
{
v___x_803_ = v___x_793_;
v_isShared_804_ = v_isSharedCheck_836_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_val_801_);
lean_dec(v___x_793_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_836_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v_mod_808_; uint8_t v___x_809_; 
v___x_805_ = lean_box(0);
v___x_806_ = l_Lean_Environment_header(v_env_780_);
lean_dec_ref(v_env_780_);
v___x_807_ = l_Lean_EnvironmentHeader_moduleNames(v___x_806_);
v_mod_808_ = lean_array_get(v___x_805_, v___x_807_, v_val_801_);
lean_dec(v_val_801_);
lean_dec_ref(v___x_807_);
v___x_809_ = l_Lean_isPrivateName(v_declHint_776_);
lean_dec(v_declHint_776_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_821_; 
v___x_810_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
lean_ctor_set(v___x_811_, 1, v_c_792_);
v___x_812_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_811_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = l_Lean_MessageData_ofName(v_mod_808_);
v___x_815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_813_);
lean_ctor_set(v___x_815_, 1, v___x_814_);
v___x_816_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_815_);
lean_ctor_set(v___x_817_, 1, v___x_816_);
v___x_818_ = l_Lean_MessageData_note(v___x_817_);
v___x_819_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_819_, 0, v_msg_775_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
if (v_isShared_804_ == 0)
{
lean_ctor_set_tag(v___x_803_, 0);
lean_ctor_set(v___x_803_, 0, v___x_819_);
v___x_821_ = v___x_803_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
else
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_834_; 
v___x_823_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_824_, 0, v___x_823_);
lean_ctor_set(v___x_824_, 1, v_c_792_);
v___x_825_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_824_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
v___x_827_ = l_Lean_MessageData_ofName(v_mod_808_);
v___x_828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_826_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_828_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
v___x_831_ = l_Lean_MessageData_note(v___x_830_);
v___x_832_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_832_, 0, v_msg_775_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
if (v_isShared_804_ == 0)
{
lean_ctor_set_tag(v___x_803_, 0);
lean_ctor_set(v___x_803_, 0, v___x_832_);
v___x_834_ = v___x_803_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_837_; 
lean_dec_ref(v_env_780_);
lean_dec(v_declHint_776_);
v___x_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_837_, 0, v_msg_775_);
return v___x_837_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_838_, lean_object* v_declHint_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_838_, v_declHint_839_, v___y_840_);
lean_dec(v___y_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_843_, lean_object* v_declHint_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v___x_855_; lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_865_; 
v___x_855_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_843_, v_declHint_844_, v___y_853_);
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_865_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_865_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_865_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_860_ = l_Lean_unknownIdentifierMessageTag;
v___x_861_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
lean_ctor_set(v___x_861_, 1, v_a_856_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_861_);
v___x_863_ = v___x_858_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_866_, lean_object* v_declHint_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_866_, v_declHint_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_msg_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v_ref_885_; lean_object* v___x_886_; lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_895_; 
v_ref_885_ = lean_ctor_get(v___y_882_, 5);
v___x_886_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
v_a_887_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_895_ == 0)
{
v___x_889_ = v___x_886_;
v_isShared_890_ = v_isSharedCheck_895_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_886_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_895_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_891_; lean_object* v___x_893_; 
lean_inc(v_ref_885_);
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v_ref_885_);
lean_ctor_set(v___x_891_, 1, v_a_887_);
if (v_isShared_890_ == 0)
{
lean_ctor_set_tag(v___x_889_, 1);
lean_ctor_set(v___x_889_, 0, v___x_891_);
v___x_893_ = v___x_889_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_msg_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_903_, lean_object* v_msg_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_fileName_915_; lean_object* v_fileMap_916_; lean_object* v_options_917_; lean_object* v_currRecDepth_918_; lean_object* v_maxRecDepth_919_; lean_object* v_ref_920_; lean_object* v_currNamespace_921_; lean_object* v_openDecls_922_; lean_object* v_initHeartbeats_923_; lean_object* v_maxHeartbeats_924_; lean_object* v_quotContext_925_; lean_object* v_currMacroScope_926_; uint8_t v_diag_927_; lean_object* v_cancelTk_x3f_928_; uint8_t v_suppressElabErrors_929_; lean_object* v_inheritedTraceOptions_930_; lean_object* v_ref_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v_fileName_915_ = lean_ctor_get(v___y_912_, 0);
v_fileMap_916_ = lean_ctor_get(v___y_912_, 1);
v_options_917_ = lean_ctor_get(v___y_912_, 2);
v_currRecDepth_918_ = lean_ctor_get(v___y_912_, 3);
v_maxRecDepth_919_ = lean_ctor_get(v___y_912_, 4);
v_ref_920_ = lean_ctor_get(v___y_912_, 5);
v_currNamespace_921_ = lean_ctor_get(v___y_912_, 6);
v_openDecls_922_ = lean_ctor_get(v___y_912_, 7);
v_initHeartbeats_923_ = lean_ctor_get(v___y_912_, 8);
v_maxHeartbeats_924_ = lean_ctor_get(v___y_912_, 9);
v_quotContext_925_ = lean_ctor_get(v___y_912_, 10);
v_currMacroScope_926_ = lean_ctor_get(v___y_912_, 11);
v_diag_927_ = lean_ctor_get_uint8(v___y_912_, sizeof(void*)*14);
v_cancelTk_x3f_928_ = lean_ctor_get(v___y_912_, 12);
v_suppressElabErrors_929_ = lean_ctor_get_uint8(v___y_912_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_930_ = lean_ctor_get(v___y_912_, 13);
v_ref_931_ = l_Lean_replaceRef(v_ref_903_, v_ref_920_);
lean_inc_ref(v_inheritedTraceOptions_930_);
lean_inc(v_cancelTk_x3f_928_);
lean_inc(v_currMacroScope_926_);
lean_inc(v_quotContext_925_);
lean_inc(v_maxHeartbeats_924_);
lean_inc(v_initHeartbeats_923_);
lean_inc(v_openDecls_922_);
lean_inc(v_currNamespace_921_);
lean_inc(v_maxRecDepth_919_);
lean_inc(v_currRecDepth_918_);
lean_inc_ref(v_options_917_);
lean_inc_ref(v_fileMap_916_);
lean_inc_ref(v_fileName_915_);
v___x_932_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_932_, 0, v_fileName_915_);
lean_ctor_set(v___x_932_, 1, v_fileMap_916_);
lean_ctor_set(v___x_932_, 2, v_options_917_);
lean_ctor_set(v___x_932_, 3, v_currRecDepth_918_);
lean_ctor_set(v___x_932_, 4, v_maxRecDepth_919_);
lean_ctor_set(v___x_932_, 5, v_ref_931_);
lean_ctor_set(v___x_932_, 6, v_currNamespace_921_);
lean_ctor_set(v___x_932_, 7, v_openDecls_922_);
lean_ctor_set(v___x_932_, 8, v_initHeartbeats_923_);
lean_ctor_set(v___x_932_, 9, v_maxHeartbeats_924_);
lean_ctor_set(v___x_932_, 10, v_quotContext_925_);
lean_ctor_set(v___x_932_, 11, v_currMacroScope_926_);
lean_ctor_set(v___x_932_, 12, v_cancelTk_x3f_928_);
lean_ctor_set(v___x_932_, 13, v_inheritedTraceOptions_930_);
lean_ctor_set_uint8(v___x_932_, sizeof(void*)*14, v_diag_927_);
lean_ctor_set_uint8(v___x_932_, sizeof(void*)*14 + 1, v_suppressElabErrors_929_);
v___x_933_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_904_, v___y_910_, v___y_911_, v___x_932_, v___y_913_);
lean_dec_ref_known(v___x_932_, 14);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_934_, lean_object* v_msg_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_){
_start:
{
lean_object* v_res_946_; 
v_res_946_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_934_, v_msg_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec_ref(v___y_939_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec(v_ref_934_);
return v_res_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_947_, lean_object* v_msg_948_, lean_object* v_declHint_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_){
_start:
{
lean_object* v___x_960_; lean_object* v_a_961_; lean_object* v___x_962_; 
v___x_960_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_948_, v_declHint_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref(v___x_960_);
v___x_962_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_947_, v_a_961_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_963_, lean_object* v_msg_964_, lean_object* v_declHint_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_963_, v_msg_964_, v_declHint_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec(v_ref_963_);
return v_res_976_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; 
v___x_978_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_979_ = l_Lean_stringToMessageData(v___x_978_);
return v___x_979_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_982_ = l_Lean_stringToMessageData(v___x_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_983_, lean_object* v_constName_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___x_995_; uint8_t v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_995_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_996_ = 0;
lean_inc(v_constName_984_);
v___x_997_ = l_Lean_MessageData_ofConstName(v_constName_984_, v___x_996_);
v___x_998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_995_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1000_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_998_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
v___x_1001_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_983_, v___x_1000_, v_constName_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1002_, lean_object* v_constName_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg(v_ref_1002_, v_constName_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_);
lean_dec(v___y_1012_);
lean_dec_ref(v___y_1011_);
lean_dec(v___y_1010_);
lean_dec_ref(v___y_1009_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec(v_ref_1002_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg(lean_object* v_constName_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_ref_1026_; lean_object* v___x_1027_; 
v_ref_1026_ = lean_ctor_get(v___y_1023_, 5);
v___x_1027_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg(v_ref_1026_, v_constName_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg(v_constName_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(lean_object* v_constName_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
lean_object* v___x_1051_; lean_object* v_env_1052_; uint8_t v___x_1053_; lean_object* v___x_1054_; 
v___x_1051_ = lean_st_ref_get(v___y_1049_);
v_env_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc_ref(v_env_1052_);
lean_dec(v___x_1051_);
v___x_1053_ = 0;
lean_inc(v_constName_1040_);
v___x_1054_ = l_Lean_Environment_find_x3f(v_env_1052_, v_constName_1040_, v___x_1053_);
if (lean_obj_tag(v___x_1054_) == 0)
{
lean_object* v___x_1055_; 
v___x_1055_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg(v_constName_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
return v___x_1055_;
}
else
{
lean_object* v_val_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec(v_constName_1040_);
v_val_1056_ = lean_ctor_get(v___x_1054_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1054_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1054_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_val_1056_);
lean_dec(v___x_1054_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
lean_ctor_set_tag(v___x_1058_, 0);
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_val_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0___boxed(lean_object* v_constName_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(v_constName_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp(lean_object* v_e_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v___y_1088_; lean_object* v___y_1089_; uint8_t v___y_1090_; uint8_t v___x_1093_; 
v___x_1093_ = l_Lean_Expr_isApp(v_e_1076_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
lean_dec_ref(v_e_1076_);
v___x_1094_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1094_, 0, v___x_1093_);
lean_ctor_set_uint8(v___x_1094_, 1, v___x_1093_);
v___x_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
return v___x_1095_;
}
else
{
lean_object* v_fn_1096_; 
v_fn_1096_ = l_Lean_Expr_getAppFn(v_e_1076_);
switch(lean_obj_tag(v_fn_1096_))
{
case 4:
{
lean_object* v_declName_1097_; lean_object* v___x_1098_; 
v_declName_1097_ = lean_ctor_get(v_fn_1096_, 0);
lean_inc(v_declName_1097_);
lean_dec_ref_known(v_fn_1096_, 2);
v___x_1098_ = l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(v_declName_1097_, v_a_1085_);
if (lean_obj_tag(v___x_1098_) == 0)
{
lean_object* v_a_1099_; uint8_t v___x_1100_; 
v_a_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_a_1099_);
lean_dec_ref_known(v___x_1098_, 1);
v___x_1100_ = lean_unbox(v_a_1099_);
lean_dec(v_a_1099_);
if (v___x_1100_ == 0)
{
lean_object* v___x_1101_; 
v___x_1101_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(v_declName_1097_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___x_1103_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref_known(v___x_1101_, 1);
lean_inc_ref(v_e_1076_);
v___x_1103_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v_e_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_object* v_a_1104_; 
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
lean_inc(v_a_1104_);
if (lean_obj_tag(v_a_1104_) == 0)
{
uint8_t v_done_1105_; uint8_t v_contextDependent_1106_; lean_object* v___y_1108_; lean_object* v_a_1109_; lean_object* v___y_1113_; 
v_done_1105_ = lean_ctor_get_uint8(v_a_1104_, 0);
v_contextDependent_1106_ = lean_ctor_get_uint8(v_a_1104_, 1);
lean_dec_ref_known(v_a_1104_, 0);
if (v_done_1105_ == 0)
{
lean_object* v___x_1115_; lean_object* v___f_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
lean_dec_ref_known(v___x_1103_, 1);
v___x_1115_ = lean_box(v_done_1105_);
v___f_1116_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1116_, 0, v_a_1102_);
lean_closure_set(v___f_1116_, 1, v___x_1115_);
v___x_1117_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp___boxed), 11, 0);
lean_inc_ref(v_e_1076_);
v___x_1118_ = l_Lean_Meta_Tactic_Cbv_guardSimproc(v___f_1116_, v___x_1117_, v_e_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
if (lean_obj_tag(v_a_1119_) == 0)
{
uint8_t v_done_1120_; 
v_done_1120_ = lean_ctor_get_uint8(v_a_1119_, 0);
if (v_done_1120_ == 0)
{
uint8_t v_contextDependent_1121_; lean_object* v___x_1122_; 
lean_dec_ref_known(v___x_1118_, 1);
v_contextDependent_1121_ = lean_ctor_get_uint8(v_a_1119_, 1);
lean_dec_ref_known(v_a_1119_, 0);
v___x_1122_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_e_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; uint8_t v___y_1125_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1123_);
if (v_contextDependent_1121_ == 0)
{
lean_dec(v_a_1123_);
v___y_1113_ = v___x_1122_;
goto v___jp_1112_;
}
else
{
if (lean_obj_tag(v_a_1123_) == 0)
{
uint8_t v_contextDependent_1135_; 
v_contextDependent_1135_ = lean_ctor_get_uint8(v_a_1123_, 1);
v___y_1125_ = v_contextDependent_1135_;
goto v___jp_1124_;
}
else
{
uint8_t v_contextDependent_1136_; 
v_contextDependent_1136_ = lean_ctor_get_uint8(v_a_1123_, sizeof(void*)*2 + 1);
v___y_1125_ = v_contextDependent_1136_;
goto v___jp_1124_;
}
}
v___jp_1124_:
{
if (v___y_1125_ == 0)
{
lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1133_; 
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1133_ == 0)
{
lean_object* v_unused_1134_; 
v_unused_1134_ = lean_ctor_get(v___x_1122_, 0);
lean_dec(v_unused_1134_);
v___x_1127_ = v___x_1122_;
v_isShared_1128_ = v_isSharedCheck_1133_;
goto v_resetjp_1126_;
}
else
{
lean_dec(v___x_1122_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1133_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; lean_object* v___x_1131_; 
v___x_1129_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1123_);
lean_inc_ref(v___x_1129_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1129_);
v___x_1131_ = v___x_1127_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v___x_1129_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
v___y_1108_ = v___x_1131_;
v_a_1109_ = v___x_1129_;
goto v___jp_1107_;
}
}
}
else
{
lean_dec(v_a_1123_);
v___y_1113_ = v___x_1122_;
goto v___jp_1112_;
}
}
}
else
{
v___y_1113_ = v___x_1122_;
goto v___jp_1112_;
}
}
else
{
lean_dec_ref_known(v_a_1119_, 0);
lean_dec_ref(v_e_1076_);
v___y_1113_ = v___x_1118_;
goto v___jp_1112_;
}
}
else
{
lean_dec_ref_known(v_a_1119_, 2);
lean_dec_ref(v_e_1076_);
v___y_1113_ = v___x_1118_;
goto v___jp_1112_;
}
}
else
{
lean_dec_ref(v_e_1076_);
v___y_1113_ = v___x_1118_;
goto v___jp_1112_;
}
}
else
{
lean_dec(v_a_1102_);
lean_dec_ref(v_e_1076_);
return v___x_1103_;
}
v___jp_1107_:
{
if (v_contextDependent_1106_ == 0)
{
lean_dec_ref(v_a_1109_);
return v___y_1108_;
}
else
{
if (lean_obj_tag(v_a_1109_) == 0)
{
uint8_t v_contextDependent_1110_; 
v_contextDependent_1110_ = lean_ctor_get_uint8(v_a_1109_, 1);
v___y_1088_ = v_a_1109_;
v___y_1089_ = v___y_1108_;
v___y_1090_ = v_contextDependent_1110_;
goto v___jp_1087_;
}
else
{
uint8_t v_contextDependent_1111_; 
v_contextDependent_1111_ = lean_ctor_get_uint8(v_a_1109_, sizeof(void*)*2 + 1);
v___y_1088_ = v_a_1109_;
v___y_1089_ = v___y_1108_;
v___y_1090_ = v_contextDependent_1111_;
goto v___jp_1087_;
}
}
}
v___jp_1112_:
{
if (lean_obj_tag(v___y_1113_) == 0)
{
lean_object* v_a_1114_; 
v_a_1114_ = lean_ctor_get(v___y_1113_, 0);
lean_inc(v_a_1114_);
v___y_1108_ = v___y_1113_;
v_a_1109_ = v_a_1114_;
goto v___jp_1107_;
}
else
{
return v___y_1113_;
}
}
}
else
{
lean_dec_ref_known(v_a_1104_, 2);
lean_dec(v_a_1102_);
lean_dec_ref(v_e_1076_);
return v___x_1103_;
}
}
else
{
lean_dec(v_a_1102_);
lean_dec_ref(v_e_1076_);
return v___x_1103_;
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec_ref(v_e_1076_);
v_a_1137_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1101_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1101_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
else
{
lean_object* v___x_1145_; 
lean_dec(v_declName_1097_);
v___x_1145_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v_e_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1154_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1154_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1154_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1150_ = l_Lean_Meta_Tactic_Cbv_markAsDoneIfFailed(v_a_1146_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1150_);
v___x_1152_ = v___x_1148_;
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
}
else
{
return v___x_1145_;
}
}
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec(v_declName_1097_);
lean_dec_ref(v_e_1076_);
v_a_1155_ = lean_ctor_get(v___x_1098_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1098_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1098_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1098_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
case 6:
{
lean_object* v___x_1163_; 
lean_dec_ref_known(v_fn_1096_, 3);
v___x_1163_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg(v_e_1076_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_);
return v___x_1163_;
}
default: 
{
lean_object* v___x_1164_; lean_object* v___x_1165_; 
lean_dec_ref(v_fn_1096_);
lean_dec_ref(v_e_1076_);
v___x_1164_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_1165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
return v___x_1165_;
}
}
}
v___jp_1087_:
{
if (v___y_1090_ == 0)
{
lean_object* v___x_1091_; lean_object* v___x_1092_; 
lean_dec_ref(v___y_1089_);
v___x_1091_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1088_);
v___x_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
return v___x_1092_;
}
else
{
lean_dec_ref(v___y_1088_);
return v___y_1089_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___boxed(lean_object* v_e_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp(v_e_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
lean_dec(v_a_1173_);
lean_dec_ref(v_a_1172_);
lean_dec(v_a_1171_);
lean_dec_ref(v_a_1170_);
lean_dec(v_a_1169_);
lean_dec_ref(v_a_1168_);
lean_dec(v_a_1167_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0(lean_object* v_00_u03b1_1178_, lean_object* v_constName_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg(v_constName_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1191_, lean_object* v_constName_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0(v_00_u03b1_1191_, v_constName_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
return v_res_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1204_, lean_object* v_ref_1205_, lean_object* v_constName_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg(v_ref_1205_, v_constName_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1218_, lean_object* v_ref_1219_, lean_object* v_constName_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1(v_00_u03b1_1218_, v_ref_1219_, v_constName_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec(v_ref_1219_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1232_, lean_object* v_ref_1233_, lean_object* v_msg_1234_, lean_object* v_declHint_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1233_, v_msg_1234_, v_declHint_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1247_, lean_object* v_ref_1248_, lean_object* v_msg_1249_, lean_object* v_declHint_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1247_, v_ref_1248_, v_msg_1249_, v_declHint_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec(v_ref_1248_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1262_, lean_object* v_declHint_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_){
_start:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1262_, v_declHint_1263_, v___y_1272_);
return v___x_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1275_, lean_object* v_declHint_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_){
_start:
{
lean_object* v_res_1287_; 
v_res_1287_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1275_, v_declHint_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
return v_res_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1288_, lean_object* v_ref_1289_, lean_object* v_msg_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1289_, v_msg_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_);
return v___x_1301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1302_, lean_object* v_ref_1303_, lean_object* v_msg_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1302_, v_ref_1303_, v_msg_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
lean_dec(v___y_1307_);
lean_dec_ref(v___y_1306_);
lean_dec(v___y_1305_);
lean_dec(v_ref_1303_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_1316_, lean_object* v_msg_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___x_1328_; 
v___x_1328_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1317_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1329_, lean_object* v_msg_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_1329_, v_msg_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleOpaqueConst(lean_object* v_e_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_){
_start:
{
if (lean_obj_tag(v_e_1342_) == 4)
{
lean_object* v_declName_1353_; lean_object* v___x_1354_; 
v_declName_1353_ = lean_ctor_get(v_e_1342_, 0);
v___x_1354_ = l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(v_declName_1353_, v_a_1351_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1376_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1357_ = v___x_1354_;
v_isShared_1358_ = v_isSharedCheck_1376_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1354_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1376_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
uint8_t v___x_1359_; 
v___x_1359_ = lean_unbox(v_a_1355_);
if (v___x_1359_ == 0)
{
lean_object* v___x_1360_; uint8_t v___x_1361_; uint8_t v___x_1362_; lean_object* v___x_1364_; 
lean_dec_ref_known(v_e_1342_, 2);
v___x_1360_ = lean_alloc_ctor(0, 0, 2);
v___x_1361_ = lean_unbox(v_a_1355_);
lean_ctor_set_uint8(v___x_1360_, 0, v___x_1361_);
v___x_1362_ = lean_unbox(v_a_1355_);
lean_dec(v_a_1355_);
lean_ctor_set_uint8(v___x_1360_, 1, v___x_1362_);
if (v_isShared_1358_ == 0)
{
lean_ctor_set(v___x_1357_, 0, v___x_1360_);
v___x_1364_ = v___x_1357_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1360_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
else
{
lean_object* v___x_1366_; 
lean_del_object(v___x_1357_);
lean_dec(v_a_1355_);
v___x_1366_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v_e_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1375_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1369_ = v___x_1366_;
v_isShared_1370_ = v_isSharedCheck_1375_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1366_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1375_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1371_ = l_Lean_Meta_Tactic_Cbv_markAsDoneIfFailed(v_a_1367_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v___x_1371_);
v___x_1373_ = v___x_1369_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1371_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
else
{
return v___x_1366_;
}
}
}
}
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
lean_dec_ref_known(v_e_1342_, 2);
v_a_1377_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1354_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1354_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
else
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
lean_dec_ref(v_e_1342_);
v___x_1385_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
return v___x_1386_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleOpaqueConst___boxed(lean_object* v_e_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleOpaqueConst(v_e_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_);
lean_dec(v_a_1396_);
lean_dec_ref(v_a_1395_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
lean_dec(v_a_1392_);
lean_dec_ref(v_a_1391_);
lean_dec(v_a_1390_);
lean_dec_ref(v_a_1389_);
lean_dec(v_a_1388_);
return v_res_1398_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1(void){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__0));
v___x_1401_ = l_Lean_stringToMessageData(v___x_1400_);
return v___x_1401_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3(void){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__2));
v___x_1404_ = l_Lean_stringToMessageData(v___x_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(lean_object* v_e_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v___x_1412_; 
lean_inc_ref(v_e_1405_);
v___x_1412_ = l_Lean_Expr_rawNatLit_x3f(v_e_1405_);
if (lean_obj_tag(v___x_1412_) == 1)
{
lean_object* v_val_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v_val_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_val_1413_);
lean_dec_ref_known(v___x_1412_, 1);
v___x_1414_ = l_Lean_mkNatLit(v_val_1413_);
v___x_1415_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v___x_1414_, v_a_1406_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v_options_1442_; uint8_t v_hasTrace_1443_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref_known(v___x_1415_, 1);
v_options_1442_ = lean_ctor_get(v_a_1409_, 2);
v_hasTrace_1443_ = lean_ctor_get_uint8(v_options_1442_, sizeof(void*)*1);
if (v_hasTrace_1443_ == 0)
{
v___y_1418_ = v_a_1406_;
v___y_1419_ = v_a_1407_;
v___y_1420_ = v_a_1408_;
v___y_1421_ = v_a_1409_;
v___y_1422_ = v_a_1410_;
goto v___jp_1417_;
}
else
{
lean_object* v_inheritedTraceOptions_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
v_inheritedTraceOptions_1444_ = lean_ctor_get(v_a_1409_, 13);
v___x_1445_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_1446_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3);
v___x_1447_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1444_, v_options_1442_, v___x_1446_);
if (v___x_1447_ == 0)
{
v___y_1418_ = v_a_1406_;
v___y_1419_ = v_a_1407_;
v___y_1420_ = v_a_1408_;
v___y_1421_ = v_a_1409_;
v___y_1422_ = v_a_1410_;
goto v___jp_1417_;
}
else
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1448_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1);
lean_inc_ref(v_e_1405_);
v___x_1449_ = l_Lean_MessageData_ofExpr(v_e_1405_);
v___x_1450_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1448_);
lean_ctor_set(v___x_1450_, 1, v___x_1449_);
v___x_1451_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3);
v___x_1452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1450_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
lean_inc(v_a_1416_);
v___x_1453_ = l_Lean_MessageData_ofExpr(v_a_1416_);
v___x_1454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1452_);
lean_ctor_set(v___x_1454_, 1, v___x_1453_);
v___x_1455_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_1445_, v___x_1454_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_);
if (lean_obj_tag(v___x_1455_) == 0)
{
lean_dec_ref_known(v___x_1455_, 1);
v___y_1418_ = v_a_1406_;
v___y_1419_ = v_a_1407_;
v___y_1420_ = v_a_1408_;
v___y_1421_ = v_a_1409_;
v___y_1422_ = v_a_1410_;
goto v___jp_1417_;
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec(v_a_1416_);
lean_dec_ref(v_e_1405_);
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1455_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1455_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1455_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
}
v___jp_1417_:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_e_1405_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1433_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1433_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1433_ == 0)
{
v___x_1426_ = v___x_1423_;
v_isShared_1427_ = v_isSharedCheck_1433_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1423_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1433_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
uint8_t v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1431_; 
v___x_1428_ = 0;
v___x_1429_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1429_, 0, v_a_1416_);
lean_ctor_set(v___x_1429_, 1, v_a_1424_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*2, v___x_1428_);
lean_ctor_set_uint8(v___x_1429_, sizeof(void*)*2 + 1, v___x_1428_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1429_);
v___x_1431_ = v___x_1426_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1429_);
v___x_1431_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
return v___x_1431_;
}
}
}
else
{
lean_object* v_a_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1441_; 
lean_dec(v_a_1416_);
v_a_1434_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1436_ = v___x_1423_;
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_a_1434_);
lean_dec(v___x_1423_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1441_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1439_; 
if (v_isShared_1437_ == 0)
{
v___x_1439_ = v___x_1436_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v_a_1434_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec_ref(v_e_1405_);
v_a_1464_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1415_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1415_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
else
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec(v___x_1412_);
lean_dec_ref(v_e_1405_);
v___x_1472_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_1473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1472_);
return v___x_1473_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___boxed(lean_object* v_e_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_, lean_object* v_a_1479_, lean_object* v_a_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(v_e_1474_, v_a_1475_, v_a_1476_, v_a_1477_, v_a_1478_, v_a_1479_);
lean_dec(v_a_1479_);
lean_dec_ref(v_a_1478_);
lean_dec(v_a_1477_);
lean_dec_ref(v_a_1476_);
lean_dec(v_a_1475_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit(lean_object* v_e_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(v_e_1482_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___boxed(lean_object* v_e_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit(v_e_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_);
lean_dec(v_a_1503_);
lean_dec_ref(v_a_1502_);
lean_dec(v_a_1501_);
lean_dec_ref(v_a_1500_);
lean_dec(v_a_1499_);
lean_dec_ref(v_a_1498_);
lean_dec(v_a_1497_);
lean_dec_ref(v_a_1496_);
lean_dec(v_a_1495_);
return v_res_1505_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1(void){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__0));
v___x_1508_ = l_Lean_stringToMessageData(v___x_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(lean_object* v_e_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
if (lean_obj_tag(v_e_1509_) == 8)
{
lean_object* v_value_1516_; lean_object* v_body_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; lean_object* v_new_1522_; lean_object* v___x_1523_; 
v_value_1516_ = lean_ctor_get(v_e_1509_, 2);
v_body_1517_ = lean_ctor_get(v_e_1509_, 3);
v___x_1518_ = lean_unsigned_to_nat(1u);
v___x_1519_ = lean_mk_empty_array_with_capacity(v___x_1518_);
lean_inc_ref(v_value_1516_);
v___x_1520_ = lean_array_push(v___x_1519_, v_value_1516_);
v___x_1521_ = 1;
v_new_1522_ = l_Lean_Meta_expandLet(v_body_1517_, v___x_1520_, v___x_1521_);
v___x_1523_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_new_1522_, v_a_1510_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v___y_1526_; lean_object* v___y_1527_; lean_object* v___y_1528_; lean_object* v___y_1529_; lean_object* v___y_1530_; lean_object* v_options_1550_; uint8_t v_hasTrace_1551_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_a_1524_);
lean_dec_ref_known(v___x_1523_, 1);
v_options_1550_ = lean_ctor_get(v_a_1513_, 2);
v_hasTrace_1551_ = lean_ctor_get_uint8(v_options_1550_, sizeof(void*)*1);
if (v_hasTrace_1551_ == 0)
{
lean_dec_ref_known(v_e_1509_, 4);
v___y_1526_ = v_a_1510_;
v___y_1527_ = v_a_1511_;
v___y_1528_ = v_a_1512_;
v___y_1529_ = v_a_1513_;
v___y_1530_ = v_a_1514_;
goto v___jp_1525_;
}
else
{
lean_object* v_inheritedTraceOptions_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; uint8_t v___x_1555_; 
v_inheritedTraceOptions_1552_ = lean_ctor_get(v_a_1513_, 13);
v___x_1553_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_1554_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3);
v___x_1555_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1552_, v_options_1550_, v___x_1554_);
if (v___x_1555_ == 0)
{
lean_dec_ref_known(v_e_1509_, 4);
v___y_1526_ = v_a_1510_;
v___y_1527_ = v_a_1511_;
v___y_1528_ = v_a_1512_;
v___y_1529_ = v_a_1513_;
v___y_1530_ = v_a_1514_;
goto v___jp_1525_;
}
else
{
lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1556_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1);
v___x_1557_ = l_Lean_indentExpr(v_e_1509_);
v___x_1558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1556_);
lean_ctor_set(v___x_1558_, 1, v___x_1557_);
v___x_1559_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_1560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1558_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
lean_inc(v_a_1524_);
v___x_1561_ = l_Lean_indentExpr(v_a_1524_);
v___x_1562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1560_);
lean_ctor_set(v___x_1562_, 1, v___x_1561_);
v___x_1563_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_1553_, v___x_1562_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_dec_ref_known(v___x_1563_, 1);
v___y_1526_ = v_a_1510_;
v___y_1527_ = v_a_1511_;
v___y_1528_ = v_a_1512_;
v___y_1529_ = v_a_1513_;
v___y_1530_ = v_a_1514_;
goto v___jp_1525_;
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
lean_dec(v_a_1524_);
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1563_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1563_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
v___jp_1525_:
{
lean_object* v___x_1531_; 
lean_inc(v_a_1524_);
v___x_1531_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_1524_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
if (lean_obj_tag(v___x_1531_) == 0)
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1541_; 
v_a_1532_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1534_ = v___x_1531_;
v_isShared_1535_ = v_isSharedCheck_1541_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1531_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1541_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
uint8_t v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1539_; 
v___x_1536_ = 0;
v___x_1537_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1537_, 0, v_a_1524_);
lean_ctor_set(v___x_1537_, 1, v_a_1532_);
lean_ctor_set_uint8(v___x_1537_, sizeof(void*)*2, v___x_1536_);
lean_ctor_set_uint8(v___x_1537_, sizeof(void*)*2 + 1, v___x_1536_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 0, v___x_1537_);
v___x_1539_ = v___x_1534_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1537_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
else
{
lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1549_; 
lean_dec(v_a_1524_);
v_a_1542_ = lean_ctor_get(v___x_1531_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1531_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1544_ = v___x_1531_;
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1531_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1549_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1547_; 
if (v_isShared_1545_ == 0)
{
v___x_1547_ = v___x_1544_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
}
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_dec_ref_known(v_e_1509_, 4);
v_a_1572_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1523_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1523_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
else
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
lean_dec_ref(v_e_1509_);
v___x_1580_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
return v___x_1581_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___boxed(lean_object* v_e_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_, lean_object* v_a_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(v_e_1582_, v_a_1583_, v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_);
lean_dec(v_a_1587_);
lean_dec_ref(v_a_1586_);
lean_dec(v_a_1585_);
lean_dec_ref(v_a_1584_);
lean_dec(v_a_1583_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce(lean_object* v_e_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(v_e_1590_, v_a_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_);
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___boxed(lean_object* v_e_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce(v_e_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_);
lean_dec(v_a_1611_);
lean_dec_ref(v_a_1610_);
lean_dec(v_a_1609_);
lean_dec_ref(v_a_1608_);
lean_dec(v_a_1607_);
lean_dec_ref(v_a_1606_);
lean_dec(v_a_1605_);
lean_dec_ref(v_a_1604_);
lean_dec(v_a_1603_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(lean_object* v_structName_1614_, lean_object* v_idx_1615_, lean_object* v_struct_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v___y_1625_; lean_object* v___x_1628_; uint8_t v_debug_1629_; 
v___x_1628_ = lean_st_ref_get(v___y_1618_);
v_debug_1629_ = lean_ctor_get_uint8(v___x_1628_, sizeof(void*)*10);
lean_dec(v___x_1628_);
if (v_debug_1629_ == 0)
{
v___y_1625_ = v___y_1618_;
goto v___jp_1624_;
}
else
{
lean_object* v___x_1630_; 
lean_inc_ref(v_struct_1616_);
v___x_1630_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_struct_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_dec_ref_known(v___x_1630_, 1);
v___y_1625_ = v___y_1618_;
goto v___jp_1624_;
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec_ref(v_struct_1616_);
lean_dec(v_idx_1615_);
lean_dec(v_structName_1614_);
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1630_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1630_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
v___jp_1624_:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = l_Lean_Expr_proj___override(v_structName_1614_, v_idx_1615_, v_struct_1616_);
v___x_1627_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1626_, v___y_1625_);
return v___x_1627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg___boxed(lean_object* v_structName_1639_, lean_object* v_idx_1640_, lean_object* v_struct_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_structName_1639_, v_idx_1640_, v_struct_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0(lean_object* v_structName_1650_, lean_object* v_idx_1651_, lean_object* v_struct_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_structName_1650_, v_idx_1651_, v_struct_1652_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___boxed(lean_object* v_structName_1664_, lean_object* v_idx_1665_, lean_object* v_struct_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0(v_structName_1664_, v_idx_1665_, v_struct_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec_ref(v___y_1670_);
lean_dec(v___y_1669_);
lean_dec_ref(v___y_1668_);
lean_dec(v___y_1667_);
return v_res_1677_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(lean_object* v_msg_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_146520__overap_1691_; lean_object* v___x_1692_; 
v___x_1690_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___closed__0);
v___x_146520__overap_1691_ = lean_panic_fn_borrowed(v___x_1690_, v_msg_1679_);
lean_inc(v___y_1688_);
lean_inc_ref(v___y_1687_);
lean_inc(v___y_1686_);
lean_inc_ref(v___y_1685_);
lean_inc(v___y_1684_);
lean_inc_ref(v___y_1683_);
lean_inc(v___y_1682_);
lean_inc_ref(v___y_1681_);
lean_inc(v___y_1680_);
v___x_1692_ = lean_apply_10(v___x_146520__overap_1691_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, lean_box(0));
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___boxed(lean_object* v_msg_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(v_msg_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec_ref(v___y_1695_);
lean_dec(v___y_1694_);
return v_res_1704_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1705_ = lean_unsigned_to_nat(32u);
v___x_1706_ = lean_mk_empty_array_with_capacity(v___x_1705_);
v___x_1707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1706_);
return v___x_1707_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1708_ = ((size_t)5ULL);
v___x_1709_ = lean_unsigned_to_nat(0u);
v___x_1710_ = lean_unsigned_to_nat(32u);
v___x_1711_ = lean_mk_empty_array_with_capacity(v___x_1710_);
v___x_1712_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__0);
v___x_1713_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
lean_ctor_set(v___x_1713_, 1, v___x_1711_);
lean_ctor_set(v___x_1713_, 2, v___x_1709_);
lean_ctor_set(v___x_1713_, 3, v___x_1709_);
lean_ctor_set_usize(v___x_1713_, 4, v___x_1708_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg(lean_object* v___y_1714_){
_start:
{
lean_object* v___x_1716_; lean_object* v_traceState_1717_; lean_object* v_traces_1718_; lean_object* v___x_1719_; lean_object* v_traceState_1720_; lean_object* v_env_1721_; lean_object* v_nextMacroScope_1722_; lean_object* v_ngen_1723_; lean_object* v_auxDeclNGen_1724_; lean_object* v_cache_1725_; lean_object* v_messages_1726_; lean_object* v_infoState_1727_; lean_object* v_snapshotTasks_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1747_; 
v___x_1716_ = lean_st_ref_get(v___y_1714_);
v_traceState_1717_ = lean_ctor_get(v___x_1716_, 4);
lean_inc_ref(v_traceState_1717_);
lean_dec(v___x_1716_);
v_traces_1718_ = lean_ctor_get(v_traceState_1717_, 0);
lean_inc_ref(v_traces_1718_);
lean_dec_ref(v_traceState_1717_);
v___x_1719_ = lean_st_ref_take(v___y_1714_);
v_traceState_1720_ = lean_ctor_get(v___x_1719_, 4);
v_env_1721_ = lean_ctor_get(v___x_1719_, 0);
v_nextMacroScope_1722_ = lean_ctor_get(v___x_1719_, 1);
v_ngen_1723_ = lean_ctor_get(v___x_1719_, 2);
v_auxDeclNGen_1724_ = lean_ctor_get(v___x_1719_, 3);
v_cache_1725_ = lean_ctor_get(v___x_1719_, 5);
v_messages_1726_ = lean_ctor_get(v___x_1719_, 6);
v_infoState_1727_ = lean_ctor_get(v___x_1719_, 7);
v_snapshotTasks_1728_ = lean_ctor_get(v___x_1719_, 8);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1730_ = v___x_1719_;
v_isShared_1731_ = v_isSharedCheck_1747_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_snapshotTasks_1728_);
lean_inc(v_infoState_1727_);
lean_inc(v_messages_1726_);
lean_inc(v_cache_1725_);
lean_inc(v_traceState_1720_);
lean_inc(v_auxDeclNGen_1724_);
lean_inc(v_ngen_1723_);
lean_inc(v_nextMacroScope_1722_);
lean_inc(v_env_1721_);
lean_dec(v___x_1719_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1747_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
uint64_t v_tid_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1745_; 
v_tid_1732_ = lean_ctor_get_uint64(v_traceState_1720_, sizeof(void*)*1);
v_isSharedCheck_1745_ = !lean_is_exclusive(v_traceState_1720_);
if (v_isSharedCheck_1745_ == 0)
{
lean_object* v_unused_1746_; 
v_unused_1746_ = lean_ctor_get(v_traceState_1720_, 0);
lean_dec(v_unused_1746_);
v___x_1734_ = v_traceState_1720_;
v_isShared_1735_ = v_isSharedCheck_1745_;
goto v_resetjp_1733_;
}
else
{
lean_dec(v_traceState_1720_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1745_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1736_; lean_object* v___x_1738_; 
v___x_1736_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v___x_1736_);
v___x_1738_ = v___x_1734_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1736_);
lean_ctor_set_uint64(v_reuseFailAlloc_1744_, sizeof(void*)*1, v_tid_1732_);
v___x_1738_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
lean_object* v___x_1740_; 
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 4, v___x_1738_);
v___x_1740_ = v___x_1730_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_env_1721_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v_nextMacroScope_1722_);
lean_ctor_set(v_reuseFailAlloc_1743_, 2, v_ngen_1723_);
lean_ctor_set(v_reuseFailAlloc_1743_, 3, v_auxDeclNGen_1724_);
lean_ctor_set(v_reuseFailAlloc_1743_, 4, v___x_1738_);
lean_ctor_set(v_reuseFailAlloc_1743_, 5, v_cache_1725_);
lean_ctor_set(v_reuseFailAlloc_1743_, 6, v_messages_1726_);
lean_ctor_set(v_reuseFailAlloc_1743_, 7, v_infoState_1727_);
lean_ctor_set(v_reuseFailAlloc_1743_, 8, v_snapshotTasks_1728_);
v___x_1740_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1741_ = lean_st_ref_set(v___y_1714_, v___x_1740_);
v___x_1742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1742_, 0, v_traces_1718_);
return v___x_1742_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___boxed(lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg(v___y_1748_);
lean_dec(v___y_1748_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg(v___y_1759_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___boxed(lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
return v_res_1772_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(lean_object* v_opts_1773_, lean_object* v_opt_1774_){
_start:
{
lean_object* v_name_1775_; lean_object* v_defValue_1776_; lean_object* v_map_1777_; lean_object* v___x_1778_; 
v_name_1775_ = lean_ctor_get(v_opt_1774_, 0);
v_defValue_1776_ = lean_ctor_get(v_opt_1774_, 1);
v_map_1777_ = lean_ctor_get(v_opts_1773_, 0);
v___x_1778_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1777_, v_name_1775_);
if (lean_obj_tag(v___x_1778_) == 0)
{
uint8_t v___x_1779_; 
v___x_1779_ = lean_unbox(v_defValue_1776_);
return v___x_1779_;
}
else
{
lean_object* v_val_1780_; 
v_val_1780_ = lean_ctor_get(v___x_1778_, 0);
lean_inc(v_val_1780_);
lean_dec_ref_known(v___x_1778_, 1);
if (lean_obj_tag(v_val_1780_) == 1)
{
uint8_t v_v_1781_; 
v_v_1781_ = lean_ctor_get_uint8(v_val_1780_, 0);
lean_dec_ref_known(v_val_1780_, 0);
return v_v_1781_;
}
else
{
uint8_t v___x_1782_; 
lean_dec(v_val_1780_);
v___x_1782_ = lean_unbox(v_defValue_1776_);
return v___x_1782_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___boxed(lean_object* v_opts_1783_, lean_object* v_opt_1784_){
_start:
{
uint8_t v_res_1785_; lean_object* v_r_1786_; 
v_res_1785_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_1783_, v_opt_1784_);
lean_dec_ref(v_opt_1784_);
lean_dec_ref(v_opts_1783_);
v_r_1786_ = lean_box(v_res_1785_);
return v_r_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0(uint8_t v___x_1787_, lean_object* v_e_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v___x_1794_; uint8_t v_foApprox_1795_; uint8_t v_ctxApprox_1796_; uint8_t v_quasiPatternApprox_1797_; uint8_t v_constApprox_1798_; uint8_t v_isDefEqStuckEx_1799_; uint8_t v_unificationHints_1800_; uint8_t v_proofIrrelevance_1801_; uint8_t v_assignSyntheticOpaque_1802_; uint8_t v_offsetCnstrs_1803_; uint8_t v_etaStruct_1804_; uint8_t v_univApprox_1805_; uint8_t v_iota_1806_; uint8_t v_beta_1807_; uint8_t v_proj_1808_; uint8_t v_zeta_1809_; uint8_t v_zetaDelta_1810_; uint8_t v_zetaUnused_1811_; uint8_t v_zetaHave_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1851_; 
v___x_1794_ = l_Lean_Meta_Context_config(v___y_1789_);
v_foApprox_1795_ = lean_ctor_get_uint8(v___x_1794_, 0);
v_ctxApprox_1796_ = lean_ctor_get_uint8(v___x_1794_, 1);
v_quasiPatternApprox_1797_ = lean_ctor_get_uint8(v___x_1794_, 2);
v_constApprox_1798_ = lean_ctor_get_uint8(v___x_1794_, 3);
v_isDefEqStuckEx_1799_ = lean_ctor_get_uint8(v___x_1794_, 4);
v_unificationHints_1800_ = lean_ctor_get_uint8(v___x_1794_, 5);
v_proofIrrelevance_1801_ = lean_ctor_get_uint8(v___x_1794_, 6);
v_assignSyntheticOpaque_1802_ = lean_ctor_get_uint8(v___x_1794_, 7);
v_offsetCnstrs_1803_ = lean_ctor_get_uint8(v___x_1794_, 8);
v_etaStruct_1804_ = lean_ctor_get_uint8(v___x_1794_, 10);
v_univApprox_1805_ = lean_ctor_get_uint8(v___x_1794_, 11);
v_iota_1806_ = lean_ctor_get_uint8(v___x_1794_, 12);
v_beta_1807_ = lean_ctor_get_uint8(v___x_1794_, 13);
v_proj_1808_ = lean_ctor_get_uint8(v___x_1794_, 14);
v_zeta_1809_ = lean_ctor_get_uint8(v___x_1794_, 15);
v_zetaDelta_1810_ = lean_ctor_get_uint8(v___x_1794_, 16);
v_zetaUnused_1811_ = lean_ctor_get_uint8(v___x_1794_, 17);
v_zetaHave_1812_ = lean_ctor_get_uint8(v___x_1794_, 18);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1794_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1814_ = v___x_1794_;
v_isShared_1815_ = v_isSharedCheck_1851_;
goto v_resetjp_1813_;
}
else
{
lean_dec(v___x_1794_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1851_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
uint8_t v_trackZetaDelta_1816_; lean_object* v_zetaDeltaSet_1817_; lean_object* v_lctx_1818_; lean_object* v_localInstances_1819_; lean_object* v_defEqCtx_x3f_1820_; lean_object* v_synthPendingDepth_1821_; lean_object* v_canUnfold_x3f_1822_; uint8_t v_univApprox_1823_; uint8_t v_inTypeClassResolution_1824_; uint8_t v_cacheInferType_1825_; lean_object* v_config_1827_; 
v_trackZetaDelta_1816_ = lean_ctor_get_uint8(v___y_1789_, sizeof(void*)*7);
v_zetaDeltaSet_1817_ = lean_ctor_get(v___y_1789_, 1);
lean_inc(v_zetaDeltaSet_1817_);
v_lctx_1818_ = lean_ctor_get(v___y_1789_, 2);
lean_inc_ref(v_lctx_1818_);
v_localInstances_1819_ = lean_ctor_get(v___y_1789_, 3);
lean_inc_ref(v_localInstances_1819_);
v_defEqCtx_x3f_1820_ = lean_ctor_get(v___y_1789_, 4);
lean_inc(v_defEqCtx_x3f_1820_);
v_synthPendingDepth_1821_ = lean_ctor_get(v___y_1789_, 5);
lean_inc(v_synthPendingDepth_1821_);
v_canUnfold_x3f_1822_ = lean_ctor_get(v___y_1789_, 6);
lean_inc(v_canUnfold_x3f_1822_);
v_univApprox_1823_ = lean_ctor_get_uint8(v___y_1789_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1824_ = lean_ctor_get_uint8(v___y_1789_, sizeof(void*)*7 + 2);
v_cacheInferType_1825_ = lean_ctor_get_uint8(v___y_1789_, sizeof(void*)*7 + 3);
if (v_isShared_1815_ == 0)
{
v_config_1827_ = v___x_1814_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, 0, v_foApprox_1795_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, 1, v_ctxApprox_1796_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, 2, v_quasiPatternApprox_1797_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, 3, v_constApprox_1798_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, 4, v_isDefEqStuckEx_1799_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, 5, v_unificationHints_1800_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, 6, v_proofIrrelevance_1801_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, 7, v_assignSyntheticOpaque_1802_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, 8, v_offsetCnstrs_1803_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, 10, v_etaStruct_1804_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, 11, v_univApprox_1805_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, 12, v_iota_1806_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, 13, v_beta_1807_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, 14, v_proj_1808_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, 15, v_zeta_1809_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, 16, v_zetaDelta_1810_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, 17, v_zetaUnused_1811_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, 18, v_zetaHave_1812_);
v_config_1827_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
uint64_t v___x_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1842_; 
lean_ctor_set_uint8(v_config_1827_, 9, v___x_1787_);
v___x_1828_ = l_Lean_Meta_Context_configKey(v___y_1789_);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___y_1789_);
if (v_isSharedCheck_1842_ == 0)
{
lean_object* v_unused_1843_; lean_object* v_unused_1844_; lean_object* v_unused_1845_; lean_object* v_unused_1846_; lean_object* v_unused_1847_; lean_object* v_unused_1848_; lean_object* v_unused_1849_; 
v_unused_1843_ = lean_ctor_get(v___y_1789_, 6);
lean_dec(v_unused_1843_);
v_unused_1844_ = lean_ctor_get(v___y_1789_, 5);
lean_dec(v_unused_1844_);
v_unused_1845_ = lean_ctor_get(v___y_1789_, 4);
lean_dec(v_unused_1845_);
v_unused_1846_ = lean_ctor_get(v___y_1789_, 3);
lean_dec(v_unused_1846_);
v_unused_1847_ = lean_ctor_get(v___y_1789_, 2);
lean_dec(v_unused_1847_);
v_unused_1848_ = lean_ctor_get(v___y_1789_, 1);
lean_dec(v_unused_1848_);
v_unused_1849_ = lean_ctor_get(v___y_1789_, 0);
lean_dec(v_unused_1849_);
v___x_1830_ = v___y_1789_;
v_isShared_1831_ = v_isSharedCheck_1842_;
goto v_resetjp_1829_;
}
else
{
lean_dec(v___y_1789_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1842_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
uint64_t v___x_1832_; uint64_t v___x_1833_; uint64_t v___x_1834_; uint64_t v___x_1835_; uint64_t v_key_1836_; lean_object* v___x_1837_; lean_object* v___x_1839_; 
v___x_1832_ = 3ULL;
v___x_1833_ = lean_uint64_shift_right(v___x_1828_, v___x_1832_);
v___x_1834_ = lean_uint64_shift_left(v___x_1833_, v___x_1832_);
v___x_1835_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1787_);
v_key_1836_ = lean_uint64_lor(v___x_1834_, v___x_1835_);
v___x_1837_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1837_, 0, v_config_1827_);
lean_ctor_set_uint64(v___x_1837_, sizeof(void*)*1, v_key_1836_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 0, v___x_1837_);
v___x_1839_ = v___x_1830_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1837_);
lean_ctor_set(v_reuseFailAlloc_1841_, 1, v_zetaDeltaSet_1817_);
lean_ctor_set(v_reuseFailAlloc_1841_, 2, v_lctx_1818_);
lean_ctor_set(v_reuseFailAlloc_1841_, 3, v_localInstances_1819_);
lean_ctor_set(v_reuseFailAlloc_1841_, 4, v_defEqCtx_x3f_1820_);
lean_ctor_set(v_reuseFailAlloc_1841_, 5, v_synthPendingDepth_1821_);
lean_ctor_set(v_reuseFailAlloc_1841_, 6, v_canUnfold_x3f_1822_);
lean_ctor_set_uint8(v_reuseFailAlloc_1841_, sizeof(void*)*7, v_trackZetaDelta_1816_);
lean_ctor_set_uint8(v_reuseFailAlloc_1841_, sizeof(void*)*7 + 1, v_univApprox_1823_);
lean_ctor_set_uint8(v_reuseFailAlloc_1841_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1824_);
lean_ctor_set_uint8(v_reuseFailAlloc_1841_, sizeof(void*)*7 + 3, v_cacheInferType_1825_);
v___x_1839_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
lean_object* v___x_1840_; 
v___x_1840_ = l_Lean_Meta_reduceProj_x3f(v_e_1788_, v___x_1839_, v___y_1790_, v___y_1791_, v___y_1792_);
lean_dec_ref(v___x_1839_);
return v___x_1840_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed(lean_object* v___x_1852_, lean_object* v_e_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
uint8_t v___x_163278__boxed_1859_; lean_object* v_res_1860_; 
v___x_163278__boxed_1859_ = lean_unbox(v___x_1852_);
v_res_1860_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0(v___x_163278__boxed_1859_, v_e_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
lean_dec(v___y_1855_);
return v_res_1860_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__0));
v___x_1863_ = l_Lean_stringToMessageData(v___x_1862_);
return v___x_1863_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1865_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__2));
v___x_1866_ = l_Lean_stringToMessageData(v___x_1865_);
return v___x_1866_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__5(void){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1868_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__4));
v___x_1869_ = l_Lean_stringToMessageData(v___x_1868_);
return v___x_1869_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__7(void){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1871_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__6));
v___x_1872_ = l_Lean_stringToMessageData(v___x_1871_);
return v___x_1872_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__9(void){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__8));
v___x_1875_ = l_Lean_stringToMessageData(v___x_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2(lean_object* v_typeName_1876_, lean_object* v_idx_1877_, lean_object* v_e_1878_, lean_object* v_x_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
if (lean_obj_tag(v_x_1879_) == 0)
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1910_; 
lean_dec_ref(v_e_1878_);
v_a_1890_ = lean_ctor_get(v_x_1879_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v_x_1879_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1892_ = v_x_1879_;
v_isShared_1893_ = v_isSharedCheck_1910_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v_x_1879_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1910_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1901_; 
v___x_1894_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1);
v___x_1895_ = l_Lean_MessageData_ofName(v_typeName_1876_);
v___x_1896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1894_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
v___x_1897_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1898_, 0, v___x_1896_);
lean_ctor_set(v___x_1898_, 1, v___x_1897_);
v___x_1899_ = l_Nat_reprFast(v_idx_1877_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set_tag(v___x_1892_, 3);
lean_ctor_set(v___x_1892_, 0, v___x_1899_);
v___x_1901_ = v___x_1892_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1899_);
v___x_1901_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1902_ = l_Lean_MessageData_ofFormat(v___x_1901_);
v___x_1903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1898_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__3);
v___x_1905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
v___x_1906_ = l_Lean_Exception_toMessageData(v_a_1890_);
v___x_1907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1905_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
return v___x_1908_;
}
}
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1967_; 
v_a_1911_ = lean_ctor_get(v_x_1879_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v_x_1879_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1913_ = v_x_1879_;
v_isShared_1914_ = v_isSharedCheck_1967_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v_x_1879_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1967_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
if (lean_obj_tag(v_a_1911_) == 0)
{
uint8_t v_done_1915_; 
v_done_1915_ = lean_ctor_get_uint8(v_a_1911_, 0);
lean_dec_ref_known(v_a_1911_, 0);
if (v_done_1915_ == 1)
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1923_; 
v___x_1916_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1);
v___x_1917_ = l_Lean_MessageData_ofName(v_typeName_1876_);
v___x_1918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1916_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1918_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
v___x_1921_ = l_Nat_reprFast(v_idx_1877_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set_tag(v___x_1913_, 3);
lean_ctor_set(v___x_1913_, 0, v___x_1921_);
v___x_1923_ = v___x_1913_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v___x_1921_);
v___x_1923_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1924_ = l_Lean_MessageData_ofFormat(v___x_1923_);
v___x_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1920_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__5, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__5);
v___x_1927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1925_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = l_Lean_indentExpr(v_e_1878_);
v___x_1929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1927_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1929_);
return v___x_1930_;
}
}
else
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1939_; 
lean_dec_ref(v_e_1878_);
v___x_1932_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1);
v___x_1933_ = l_Lean_MessageData_ofName(v_typeName_1876_);
v___x_1934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1932_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1934_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
v___x_1937_ = l_Nat_reprFast(v_idx_1877_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set_tag(v___x_1913_, 3);
lean_ctor_set(v___x_1913_, 0, v___x_1937_);
v___x_1939_ = v___x_1913_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v___x_1937_);
v___x_1939_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1940_ = l_Lean_MessageData_ofFormat(v___x_1939_);
v___x_1941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1936_);
lean_ctor_set(v___x_1941_, 1, v___x_1940_);
v___x_1942_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__7);
v___x_1943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1941_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
v___x_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
return v___x_1944_;
}
}
}
else
{
lean_object* v_e_x27_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1954_; 
v_e_x27_1946_ = lean_ctor_get(v_a_1911_, 0);
lean_inc_ref(v_e_x27_1946_);
lean_dec_ref_known(v_a_1911_, 2);
v___x_1947_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1);
v___x_1948_ = l_Lean_MessageData_ofName(v_typeName_1876_);
v___x_1949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1947_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1949_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = l_Nat_reprFast(v_idx_1877_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set_tag(v___x_1913_, 3);
lean_ctor_set(v___x_1913_, 0, v___x_1952_);
v___x_1954_ = v___x_1913_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1952_);
v___x_1954_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1955_ = l_Lean_MessageData_ofFormat(v___x_1954_);
v___x_1956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1951_);
lean_ctor_set(v___x_1956_, 1, v___x_1955_);
v___x_1957_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__9);
v___x_1958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1956_);
lean_ctor_set(v___x_1958_, 1, v___x_1957_);
v___x_1959_ = l_Lean_indentExpr(v_e_1878_);
v___x_1960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1958_);
lean_ctor_set(v___x_1960_, 1, v___x_1959_);
v___x_1961_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_1962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1960_);
lean_ctor_set(v___x_1962_, 1, v___x_1961_);
v___x_1963_ = l_Lean_indentExpr(v_e_x27_1946_);
v___x_1964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1962_);
lean_ctor_set(v___x_1964_, 1, v___x_1963_);
v___x_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1964_);
return v___x_1965_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___boxed(lean_object* v_typeName_1968_, lean_object* v_idx_1969_, lean_object* v_e_1970_, lean_object* v_x_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2(v_typeName_1968_, v_idx_1969_, v_e_1970_, v_x_1971_, v___y_1972_, v___y_1973_, v___y_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_, v___y_1979_, v___y_1980_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec(v___y_1974_);
lean_dec_ref(v___y_1973_);
lean_dec(v___y_1972_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(lean_object* v_x_1983_){
_start:
{
if (lean_obj_tag(v_x_1983_) == 0)
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
v_a_1985_ = lean_ctor_get(v_x_1983_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_x_1983_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v_x_1983_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v_x_1983_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
lean_ctor_set_tag(v___x_1987_, 1);
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
else
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
v_a_1993_ = lean_ctor_get(v_x_1983_, 0);
v_isSharedCheck_2000_ = !lean_is_exclusive(v_x_1983_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v_x_1983_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v_x_1983_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
lean_ctor_set_tag(v___x_1995_, 0);
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_a_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg___boxed(lean_object* v_x_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(v_x_2001_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5(size_t v_sz_2004_, size_t v_i_2005_, lean_object* v_bs_2006_){
_start:
{
uint8_t v___x_2007_; 
v___x_2007_ = lean_usize_dec_lt(v_i_2005_, v_sz_2004_);
if (v___x_2007_ == 0)
{
return v_bs_2006_;
}
else
{
lean_object* v_v_2008_; lean_object* v_msg_2009_; lean_object* v___x_2010_; lean_object* v_bs_x27_2011_; size_t v___x_2012_; size_t v___x_2013_; lean_object* v___x_2014_; 
v_v_2008_ = lean_array_uget_borrowed(v_bs_2006_, v_i_2005_);
v_msg_2009_ = lean_ctor_get(v_v_2008_, 1);
lean_inc_ref(v_msg_2009_);
v___x_2010_ = lean_unsigned_to_nat(0u);
v_bs_x27_2011_ = lean_array_uset(v_bs_2006_, v_i_2005_, v___x_2010_);
v___x_2012_ = ((size_t)1ULL);
v___x_2013_ = lean_usize_add(v_i_2005_, v___x_2012_);
v___x_2014_ = lean_array_uset(v_bs_x27_2011_, v_i_2005_, v_msg_2009_);
v_i_2005_ = v___x_2013_;
v_bs_2006_ = v___x_2014_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5___boxed(lean_object* v_sz_2016_, lean_object* v_i_2017_, lean_object* v_bs_2018_){
_start:
{
size_t v_sz_boxed_2019_; size_t v_i_boxed_2020_; lean_object* v_res_2021_; 
v_sz_boxed_2019_ = lean_unbox_usize(v_sz_2016_);
lean_dec(v_sz_2016_);
v_i_boxed_2020_ = lean_unbox_usize(v_i_2017_);
lean_dec(v_i_2017_);
v_res_2021_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5(v_sz_boxed_2019_, v_i_boxed_2020_, v_bs_2018_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___redArg(lean_object* v_oldTraces_2022_, lean_object* v_data_2023_, lean_object* v_ref_2024_, lean_object* v_msg_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v_fileName_2031_; lean_object* v_fileMap_2032_; lean_object* v_options_2033_; lean_object* v_currRecDepth_2034_; lean_object* v_maxRecDepth_2035_; lean_object* v_ref_2036_; lean_object* v_currNamespace_2037_; lean_object* v_openDecls_2038_; lean_object* v_initHeartbeats_2039_; lean_object* v_maxHeartbeats_2040_; lean_object* v_quotContext_2041_; lean_object* v_currMacroScope_2042_; uint8_t v_diag_2043_; lean_object* v_cancelTk_x3f_2044_; uint8_t v_suppressElabErrors_2045_; lean_object* v_inheritedTraceOptions_2046_; lean_object* v___x_2047_; lean_object* v_traceState_2048_; lean_object* v_traces_2049_; lean_object* v_ref_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; size_t v_sz_2053_; size_t v___x_2054_; lean_object* v___x_2055_; lean_object* v_msg_2056_; lean_object* v___x_2057_; lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2095_; 
v_fileName_2031_ = lean_ctor_get(v___y_2028_, 0);
v_fileMap_2032_ = lean_ctor_get(v___y_2028_, 1);
v_options_2033_ = lean_ctor_get(v___y_2028_, 2);
v_currRecDepth_2034_ = lean_ctor_get(v___y_2028_, 3);
v_maxRecDepth_2035_ = lean_ctor_get(v___y_2028_, 4);
v_ref_2036_ = lean_ctor_get(v___y_2028_, 5);
v_currNamespace_2037_ = lean_ctor_get(v___y_2028_, 6);
v_openDecls_2038_ = lean_ctor_get(v___y_2028_, 7);
v_initHeartbeats_2039_ = lean_ctor_get(v___y_2028_, 8);
v_maxHeartbeats_2040_ = lean_ctor_get(v___y_2028_, 9);
v_quotContext_2041_ = lean_ctor_get(v___y_2028_, 10);
v_currMacroScope_2042_ = lean_ctor_get(v___y_2028_, 11);
v_diag_2043_ = lean_ctor_get_uint8(v___y_2028_, sizeof(void*)*14);
v_cancelTk_x3f_2044_ = lean_ctor_get(v___y_2028_, 12);
v_suppressElabErrors_2045_ = lean_ctor_get_uint8(v___y_2028_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2046_ = lean_ctor_get(v___y_2028_, 13);
v___x_2047_ = lean_st_ref_get(v___y_2029_);
v_traceState_2048_ = lean_ctor_get(v___x_2047_, 4);
lean_inc_ref(v_traceState_2048_);
lean_dec(v___x_2047_);
v_traces_2049_ = lean_ctor_get(v_traceState_2048_, 0);
lean_inc_ref(v_traces_2049_);
lean_dec_ref(v_traceState_2048_);
v_ref_2050_ = l_Lean_replaceRef(v_ref_2024_, v_ref_2036_);
lean_inc_ref(v_inheritedTraceOptions_2046_);
lean_inc(v_cancelTk_x3f_2044_);
lean_inc(v_currMacroScope_2042_);
lean_inc(v_quotContext_2041_);
lean_inc(v_maxHeartbeats_2040_);
lean_inc(v_initHeartbeats_2039_);
lean_inc(v_openDecls_2038_);
lean_inc(v_currNamespace_2037_);
lean_inc(v_maxRecDepth_2035_);
lean_inc(v_currRecDepth_2034_);
lean_inc_ref(v_options_2033_);
lean_inc_ref(v_fileMap_2032_);
lean_inc_ref(v_fileName_2031_);
v___x_2051_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2051_, 0, v_fileName_2031_);
lean_ctor_set(v___x_2051_, 1, v_fileMap_2032_);
lean_ctor_set(v___x_2051_, 2, v_options_2033_);
lean_ctor_set(v___x_2051_, 3, v_currRecDepth_2034_);
lean_ctor_set(v___x_2051_, 4, v_maxRecDepth_2035_);
lean_ctor_set(v___x_2051_, 5, v_ref_2050_);
lean_ctor_set(v___x_2051_, 6, v_currNamespace_2037_);
lean_ctor_set(v___x_2051_, 7, v_openDecls_2038_);
lean_ctor_set(v___x_2051_, 8, v_initHeartbeats_2039_);
lean_ctor_set(v___x_2051_, 9, v_maxHeartbeats_2040_);
lean_ctor_set(v___x_2051_, 10, v_quotContext_2041_);
lean_ctor_set(v___x_2051_, 11, v_currMacroScope_2042_);
lean_ctor_set(v___x_2051_, 12, v_cancelTk_x3f_2044_);
lean_ctor_set(v___x_2051_, 13, v_inheritedTraceOptions_2046_);
lean_ctor_set_uint8(v___x_2051_, sizeof(void*)*14, v_diag_2043_);
lean_ctor_set_uint8(v___x_2051_, sizeof(void*)*14 + 1, v_suppressElabErrors_2045_);
v___x_2052_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2049_);
lean_dec_ref(v_traces_2049_);
v_sz_2053_ = lean_array_size(v___x_2052_);
v___x_2054_ = ((size_t)0ULL);
v___x_2055_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5(v_sz_2053_, v___x_2054_, v___x_2052_);
v_msg_2056_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2056_, 0, v_data_2023_);
lean_ctor_set(v_msg_2056_, 1, v_msg_2025_);
lean_ctor_set(v_msg_2056_, 2, v___x_2055_);
v___x_2057_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_2056_, v___y_2026_, v___y_2027_, v___x_2051_, v___y_2029_);
lean_dec_ref_known(v___x_2051_, 14);
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2060_ = v___x_2057_;
v_isShared_2061_ = v_isSharedCheck_2095_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2057_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2095_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2062_; lean_object* v_traceState_2063_; lean_object* v_env_2064_; lean_object* v_nextMacroScope_2065_; lean_object* v_ngen_2066_; lean_object* v_auxDeclNGen_2067_; lean_object* v_cache_2068_; lean_object* v_messages_2069_; lean_object* v_infoState_2070_; lean_object* v_snapshotTasks_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2094_; 
v___x_2062_ = lean_st_ref_take(v___y_2029_);
v_traceState_2063_ = lean_ctor_get(v___x_2062_, 4);
v_env_2064_ = lean_ctor_get(v___x_2062_, 0);
v_nextMacroScope_2065_ = lean_ctor_get(v___x_2062_, 1);
v_ngen_2066_ = lean_ctor_get(v___x_2062_, 2);
v_auxDeclNGen_2067_ = lean_ctor_get(v___x_2062_, 3);
v_cache_2068_ = lean_ctor_get(v___x_2062_, 5);
v_messages_2069_ = lean_ctor_get(v___x_2062_, 6);
v_infoState_2070_ = lean_ctor_get(v___x_2062_, 7);
v_snapshotTasks_2071_ = lean_ctor_get(v___x_2062_, 8);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2073_ = v___x_2062_;
v_isShared_2074_ = v_isSharedCheck_2094_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_snapshotTasks_2071_);
lean_inc(v_infoState_2070_);
lean_inc(v_messages_2069_);
lean_inc(v_cache_2068_);
lean_inc(v_traceState_2063_);
lean_inc(v_auxDeclNGen_2067_);
lean_inc(v_ngen_2066_);
lean_inc(v_nextMacroScope_2065_);
lean_inc(v_env_2064_);
lean_dec(v___x_2062_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2094_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
uint64_t v_tid_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2092_; 
v_tid_2075_ = lean_ctor_get_uint64(v_traceState_2063_, sizeof(void*)*1);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_traceState_2063_);
if (v_isSharedCheck_2092_ == 0)
{
lean_object* v_unused_2093_; 
v_unused_2093_ = lean_ctor_get(v_traceState_2063_, 0);
lean_dec(v_unused_2093_);
v___x_2077_ = v_traceState_2063_;
v_isShared_2078_ = v_isSharedCheck_2092_;
goto v_resetjp_2076_;
}
else
{
lean_dec(v_traceState_2063_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2092_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2079_, 0, v_ref_2024_);
lean_ctor_set(v___x_2079_, 1, v_a_2058_);
v___x_2080_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2022_, v___x_2079_);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v___x_2080_);
v___x_2082_ = v___x_2077_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_2080_);
lean_ctor_set_uint64(v_reuseFailAlloc_2091_, sizeof(void*)*1, v_tid_2075_);
v___x_2082_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
lean_object* v___x_2084_; 
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 4, v___x_2082_);
v___x_2084_ = v___x_2073_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_env_2064_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_nextMacroScope_2065_);
lean_ctor_set(v_reuseFailAlloc_2090_, 2, v_ngen_2066_);
lean_ctor_set(v_reuseFailAlloc_2090_, 3, v_auxDeclNGen_2067_);
lean_ctor_set(v_reuseFailAlloc_2090_, 4, v___x_2082_);
lean_ctor_set(v_reuseFailAlloc_2090_, 5, v_cache_2068_);
lean_ctor_set(v_reuseFailAlloc_2090_, 6, v_messages_2069_);
lean_ctor_set(v_reuseFailAlloc_2090_, 7, v_infoState_2070_);
lean_ctor_set(v_reuseFailAlloc_2090_, 8, v_snapshotTasks_2071_);
v___x_2084_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2088_; 
v___x_2085_ = lean_st_ref_set(v___y_2029_, v___x_2084_);
v___x_2086_ = lean_box(0);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 0, v___x_2086_);
v___x_2088_ = v___x_2060_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2086_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___redArg___boxed(lean_object* v_oldTraces_2096_, lean_object* v_data_2097_, lean_object* v_ref_2098_, lean_object* v_msg_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___redArg(v_oldTraces_2096_, v_data_2097_, v_ref_2098_, v_msg_2099_, v___y_2100_, v___y_2101_, v___y_2102_, v___y_2103_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
return v_res_2105_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(lean_object* v_e_2106_){
_start:
{
if (lean_obj_tag(v_e_2106_) == 0)
{
uint8_t v___x_2107_; 
v___x_2107_ = 2;
return v___x_2107_;
}
else
{
uint8_t v___x_2108_; 
v___x_2108_ = 0;
return v___x_2108_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6___boxed(lean_object* v_e_2109_){
_start:
{
uint8_t v_res_2110_; lean_object* v_r_2111_; 
v_res_2110_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(v_e_2109_);
lean_dec_ref(v_e_2109_);
v_r_2111_ = lean_box(v_res_2110_);
return v_r_2111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(lean_object* v_opts_2112_, lean_object* v_opt_2113_){
_start:
{
lean_object* v_name_2114_; lean_object* v_defValue_2115_; lean_object* v_map_2116_; lean_object* v___x_2117_; 
v_name_2114_ = lean_ctor_get(v_opt_2113_, 0);
v_defValue_2115_ = lean_ctor_get(v_opt_2113_, 1);
v_map_2116_ = lean_ctor_get(v_opts_2112_, 0);
v___x_2117_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2116_, v_name_2114_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_inc(v_defValue_2115_);
return v_defValue_2115_;
}
else
{
lean_object* v_val_2118_; 
v_val_2118_ = lean_ctor_get(v___x_2117_, 0);
lean_inc(v_val_2118_);
lean_dec_ref_known(v___x_2117_, 1);
if (lean_obj_tag(v_val_2118_) == 3)
{
lean_object* v_v_2119_; 
v_v_2119_ = lean_ctor_get(v_val_2118_, 0);
lean_inc(v_v_2119_);
lean_dec_ref_known(v_val_2118_, 1);
return v_v_2119_;
}
else
{
lean_dec(v_val_2118_);
lean_inc(v_defValue_2115_);
return v_defValue_2115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7___boxed(lean_object* v_opts_2120_, lean_object* v_opt_2121_){
_start:
{
lean_object* v_res_2122_; 
v_res_2122_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_2120_, v_opt_2121_);
lean_dec_ref(v_opt_2121_);
lean_dec_ref(v_opts_2120_);
return v_res_2122_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__0));
v___x_2125_ = l_Lean_stringToMessageData(v___x_2124_);
return v___x_2125_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2126_; double v___x_2127_; 
v___x_2126_ = lean_unsigned_to_nat(1000u);
v___x_2127_ = lean_float_of_nat(v___x_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4(lean_object* v_cls_2128_, uint8_t v_collapsed_2129_, lean_object* v_tag_2130_, lean_object* v_opts_2131_, uint8_t v_clsEnabled_2132_, lean_object* v_oldTraces_2133_, lean_object* v_msg_2134_, lean_object* v_resStartStop_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v_fst_2146_; lean_object* v_snd_2147_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v_data_2151_; lean_object* v_fst_2162_; lean_object* v_snd_2163_; lean_object* v___x_2164_; uint8_t v___x_2165_; lean_object* v___y_2167_; lean_object* v_a_2168_; uint8_t v___y_2183_; double v___y_2214_; 
v_fst_2146_ = lean_ctor_get(v_resStartStop_2135_, 0);
lean_inc(v_fst_2146_);
v_snd_2147_ = lean_ctor_get(v_resStartStop_2135_, 1);
lean_inc(v_snd_2147_);
lean_dec_ref(v_resStartStop_2135_);
v_fst_2162_ = lean_ctor_get(v_snd_2147_, 0);
lean_inc(v_fst_2162_);
v_snd_2163_ = lean_ctor_get(v_snd_2147_, 1);
lean_inc(v_snd_2163_);
lean_dec(v_snd_2147_);
v___x_2164_ = l_Lean_trace_profiler;
v___x_2165_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_2131_, v___x_2164_);
if (v___x_2165_ == 0)
{
v___y_2183_ = v___x_2165_;
goto v___jp_2182_;
}
else
{
lean_object* v___x_2219_; uint8_t v___x_2220_; 
v___x_2219_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2220_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_2131_, v___x_2219_);
if (v___x_2220_ == 0)
{
lean_object* v___x_2221_; lean_object* v___x_2222_; double v___x_2223_; double v___x_2224_; double v___x_2225_; 
v___x_2221_ = l_Lean_trace_profiler_threshold;
v___x_2222_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_2131_, v___x_2221_);
v___x_2223_ = lean_float_of_nat(v___x_2222_);
v___x_2224_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2);
v___x_2225_ = lean_float_div(v___x_2223_, v___x_2224_);
v___y_2214_ = v___x_2225_;
goto v___jp_2213_;
}
else
{
lean_object* v___x_2226_; lean_object* v___x_2227_; double v___x_2228_; 
v___x_2226_ = l_Lean_trace_profiler_threshold;
v___x_2227_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_2131_, v___x_2226_);
v___x_2228_ = lean_float_of_nat(v___x_2227_);
v___y_2214_ = v___x_2228_;
goto v___jp_2213_;
}
}
v___jp_2148_:
{
lean_object* v___x_2152_; 
lean_inc(v___y_2149_);
v___x_2152_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___redArg(v_oldTraces_2133_, v_data_2151_, v___y_2149_, v___y_2150_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_object* v___x_2153_; 
lean_dec_ref_known(v___x_2152_, 1);
v___x_2153_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(v_fst_2146_);
return v___x_2153_;
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2161_; 
lean_dec(v_fst_2146_);
v_a_2154_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2156_ = v___x_2152_;
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2152_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2161_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2159_; 
if (v_isShared_2157_ == 0)
{
v___x_2159_ = v___x_2156_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
}
v___jp_2166_:
{
uint8_t v_result_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; double v___x_2172_; lean_object* v_data_2173_; 
v_result_2169_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(v_fst_2146_);
v___x_2170_ = lean_box(v_result_2169_);
v___x_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2171_, 0, v___x_2170_);
v___x_2172_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_2130_);
lean_inc_ref(v___x_2171_);
lean_inc(v_cls_2128_);
v_data_2173_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2173_, 0, v_cls_2128_);
lean_ctor_set(v_data_2173_, 1, v___x_2171_);
lean_ctor_set(v_data_2173_, 2, v_tag_2130_);
lean_ctor_set_float(v_data_2173_, sizeof(void*)*3, v___x_2172_);
lean_ctor_set_float(v_data_2173_, sizeof(void*)*3 + 8, v___x_2172_);
lean_ctor_set_uint8(v_data_2173_, sizeof(void*)*3 + 16, v_collapsed_2129_);
if (v___x_2165_ == 0)
{
lean_dec_ref_known(v___x_2171_, 1);
lean_dec(v_snd_2163_);
lean_dec(v_fst_2162_);
lean_dec_ref(v_tag_2130_);
lean_dec(v_cls_2128_);
v___y_2149_ = v___y_2167_;
v___y_2150_ = v_a_2168_;
v_data_2151_ = v_data_2173_;
goto v___jp_2148_;
}
else
{
lean_object* v_data_2174_; double v___x_2175_; double v___x_2176_; 
lean_dec_ref_known(v_data_2173_, 3);
v_data_2174_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2174_, 0, v_cls_2128_);
lean_ctor_set(v_data_2174_, 1, v___x_2171_);
lean_ctor_set(v_data_2174_, 2, v_tag_2130_);
v___x_2175_ = lean_unbox_float(v_fst_2162_);
lean_dec(v_fst_2162_);
lean_ctor_set_float(v_data_2174_, sizeof(void*)*3, v___x_2175_);
v___x_2176_ = lean_unbox_float(v_snd_2163_);
lean_dec(v_snd_2163_);
lean_ctor_set_float(v_data_2174_, sizeof(void*)*3 + 8, v___x_2176_);
lean_ctor_set_uint8(v_data_2174_, sizeof(void*)*3 + 16, v_collapsed_2129_);
v___y_2149_ = v___y_2167_;
v___y_2150_ = v_a_2168_;
v_data_2151_ = v_data_2174_;
goto v___jp_2148_;
}
}
v___jp_2177_:
{
lean_object* v_ref_2178_; lean_object* v___x_2179_; 
v_ref_2178_ = lean_ctor_get(v___y_2143_, 5);
lean_inc(v___y_2144_);
lean_inc_ref(v___y_2143_);
lean_inc(v___y_2142_);
lean_inc_ref(v___y_2141_);
lean_inc(v___y_2140_);
lean_inc_ref(v___y_2139_);
lean_inc(v___y_2138_);
lean_inc_ref(v___y_2137_);
lean_inc(v___y_2136_);
lean_inc(v_fst_2146_);
v___x_2179_ = lean_apply_11(v_msg_2134_, v_fst_2146_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_, v___y_2143_, v___y_2144_, lean_box(0));
if (lean_obj_tag(v___x_2179_) == 0)
{
lean_object* v_a_2180_; 
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
lean_inc(v_a_2180_);
lean_dec_ref_known(v___x_2179_, 1);
v___y_2167_ = v_ref_2178_;
v_a_2168_ = v_a_2180_;
goto v___jp_2166_;
}
else
{
lean_object* v___x_2181_; 
lean_dec_ref_known(v___x_2179_, 1);
v___x_2181_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
v___y_2167_ = v_ref_2178_;
v_a_2168_ = v___x_2181_;
goto v___jp_2166_;
}
}
v___jp_2182_:
{
if (v_clsEnabled_2132_ == 0)
{
if (v___y_2183_ == 0)
{
lean_object* v___x_2184_; lean_object* v_traceState_2185_; lean_object* v_env_2186_; lean_object* v_nextMacroScope_2187_; lean_object* v_ngen_2188_; lean_object* v_auxDeclNGen_2189_; lean_object* v_cache_2190_; lean_object* v_messages_2191_; lean_object* v_infoState_2192_; lean_object* v_snapshotTasks_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2212_; 
lean_dec(v_snd_2163_);
lean_dec(v_fst_2162_);
lean_dec_ref(v_msg_2134_);
lean_dec_ref(v_tag_2130_);
lean_dec(v_cls_2128_);
v___x_2184_ = lean_st_ref_take(v___y_2144_);
v_traceState_2185_ = lean_ctor_get(v___x_2184_, 4);
v_env_2186_ = lean_ctor_get(v___x_2184_, 0);
v_nextMacroScope_2187_ = lean_ctor_get(v___x_2184_, 1);
v_ngen_2188_ = lean_ctor_get(v___x_2184_, 2);
v_auxDeclNGen_2189_ = lean_ctor_get(v___x_2184_, 3);
v_cache_2190_ = lean_ctor_get(v___x_2184_, 5);
v_messages_2191_ = lean_ctor_get(v___x_2184_, 6);
v_infoState_2192_ = lean_ctor_get(v___x_2184_, 7);
v_snapshotTasks_2193_ = lean_ctor_get(v___x_2184_, 8);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2195_ = v___x_2184_;
v_isShared_2196_ = v_isSharedCheck_2212_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_snapshotTasks_2193_);
lean_inc(v_infoState_2192_);
lean_inc(v_messages_2191_);
lean_inc(v_cache_2190_);
lean_inc(v_traceState_2185_);
lean_inc(v_auxDeclNGen_2189_);
lean_inc(v_ngen_2188_);
lean_inc(v_nextMacroScope_2187_);
lean_inc(v_env_2186_);
lean_dec(v___x_2184_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2212_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
uint64_t v_tid_2197_; lean_object* v_traces_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2211_; 
v_tid_2197_ = lean_ctor_get_uint64(v_traceState_2185_, sizeof(void*)*1);
v_traces_2198_ = lean_ctor_get(v_traceState_2185_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v_traceState_2185_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2200_ = v_traceState_2185_;
v_isShared_2201_ = v_isSharedCheck_2211_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_traces_2198_);
lean_dec(v_traceState_2185_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2211_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2202_; lean_object* v___x_2204_; 
v___x_2202_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2133_, v_traces_2198_);
lean_dec_ref(v_traces_2198_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v___x_2202_);
v___x_2204_ = v___x_2200_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2202_);
lean_ctor_set_uint64(v_reuseFailAlloc_2210_, sizeof(void*)*1, v_tid_2197_);
v___x_2204_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
lean_object* v___x_2206_; 
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 4, v___x_2204_);
v___x_2206_ = v___x_2195_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_env_2186_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_nextMacroScope_2187_);
lean_ctor_set(v_reuseFailAlloc_2209_, 2, v_ngen_2188_);
lean_ctor_set(v_reuseFailAlloc_2209_, 3, v_auxDeclNGen_2189_);
lean_ctor_set(v_reuseFailAlloc_2209_, 4, v___x_2204_);
lean_ctor_set(v_reuseFailAlloc_2209_, 5, v_cache_2190_);
lean_ctor_set(v_reuseFailAlloc_2209_, 6, v_messages_2191_);
lean_ctor_set(v_reuseFailAlloc_2209_, 7, v_infoState_2192_);
lean_ctor_set(v_reuseFailAlloc_2209_, 8, v_snapshotTasks_2193_);
v___x_2206_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2207_ = lean_st_ref_set(v___y_2144_, v___x_2206_);
v___x_2208_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(v_fst_2146_);
return v___x_2208_;
}
}
}
}
}
else
{
goto v___jp_2177_;
}
}
else
{
goto v___jp_2177_;
}
}
v___jp_2213_:
{
double v___x_2215_; double v___x_2216_; double v___x_2217_; uint8_t v___x_2218_; 
v___x_2215_ = lean_unbox_float(v_snd_2163_);
v___x_2216_ = lean_unbox_float(v_fst_2162_);
v___x_2217_ = lean_float_sub(v___x_2215_, v___x_2216_);
v___x_2218_ = lean_float_decLt(v___y_2214_, v___x_2217_);
v___y_2183_ = v___x_2218_;
goto v___jp_2182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___boxed(lean_object** _args){
lean_object* v_cls_2229_ = _args[0];
lean_object* v_collapsed_2230_ = _args[1];
lean_object* v_tag_2231_ = _args[2];
lean_object* v_opts_2232_ = _args[3];
lean_object* v_clsEnabled_2233_ = _args[4];
lean_object* v_oldTraces_2234_ = _args[5];
lean_object* v_msg_2235_ = _args[6];
lean_object* v_resStartStop_2236_ = _args[7];
lean_object* v___y_2237_ = _args[8];
lean_object* v___y_2238_ = _args[9];
lean_object* v___y_2239_ = _args[10];
lean_object* v___y_2240_ = _args[11];
lean_object* v___y_2241_ = _args[12];
lean_object* v___y_2242_ = _args[13];
lean_object* v___y_2243_ = _args[14];
lean_object* v___y_2244_ = _args[15];
lean_object* v___y_2245_ = _args[16];
lean_object* v___y_2246_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2247_; uint8_t v_clsEnabled_boxed_2248_; lean_object* v_res_2249_; 
v_collapsed_boxed_2247_ = lean_unbox(v_collapsed_2230_);
v_clsEnabled_boxed_2248_ = lean_unbox(v_clsEnabled_2233_);
v_res_2249_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4(v_cls_2229_, v_collapsed_boxed_2247_, v_tag_2231_, v_opts_2232_, v_clsEnabled_boxed_2248_, v_oldTraces_2234_, v_msg_2235_, v_resStartStop_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v_opts_2232_);
return v_res_2249_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2(void){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = lean_unsigned_to_nat(0u);
v___x_2254_ = l_Lean_Expr_bvar___override(v___x_2253_);
return v___x_2254_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8(void){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2261_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__7));
v___x_2262_ = lean_unsigned_to_nat(48u);
v___x_2263_ = lean_unsigned_to_nat(219u);
v___x_2264_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__6));
v___x_2265_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__5));
v___x_2266_ = l_mkPanicMessageWithDecl(v___x_2265_, v___x_2264_, v___x_2263_, v___x_2262_, v___x_2261_);
return v___x_2266_;
}
}
static double _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9(void){
_start:
{
lean_object* v___x_2267_; double v___x_2268_; 
v___x_2267_ = lean_unsigned_to_nat(1000000000u);
v___x_2268_ = lean_float_of_nat(v___x_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(lean_object* v_e_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_, lean_object* v_a_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_){
_start:
{
lean_object* v___y_2281_; uint8_t v___y_2282_; uint8_t v___y_2283_; lean_object* v_a_2284_; lean_object* v___y_2288_; uint8_t v___y_2289_; lean_object* v_a_2290_; 
if (lean_obj_tag(v_e_2269_) == 11)
{
lean_object* v_typeName_2294_; lean_object* v_idx_2295_; lean_object* v_struct_2296_; lean_object* v_res_2298_; lean_object* v___y_2299_; lean_object* v___y_2300_; lean_object* v___y_2301_; lean_object* v___y_2302_; lean_object* v___y_2303_; lean_object* v___y_2304_; lean_object* v___y_2305_; lean_object* v___y_2306_; lean_object* v___y_2307_; lean_object* v_options_2538_; uint8_t v_hasTrace_2539_; 
v_typeName_2294_ = lean_ctor_get(v_e_2269_, 0);
v_idx_2295_ = lean_ctor_get(v_e_2269_, 1);
v_struct_2296_ = lean_ctor_get(v_e_2269_, 2);
v_options_2538_ = lean_ctor_get(v_a_2277_, 2);
v_hasTrace_2539_ = lean_ctor_get_uint8(v_options_2538_, sizeof(void*)*1);
if (v_hasTrace_2539_ == 0)
{
lean_object* v___x_2540_; 
lean_inc(v_a_2278_);
lean_inc_ref(v_a_2277_);
lean_inc(v_a_2276_);
lean_inc_ref(v_a_2275_);
lean_inc(v_a_2274_);
lean_inc_ref(v_a_2273_);
lean_inc(v_a_2272_);
lean_inc_ref(v_a_2271_);
lean_inc(v_a_2270_);
lean_inc_ref(v_struct_2296_);
v___x_2540_ = lean_sym_simp(v_struct_2296_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v_a_2541_; 
v_a_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_a_2541_);
lean_dec_ref_known(v___x_2540_, 1);
v_res_2298_ = v_a_2541_;
v___y_2299_ = v_a_2270_;
v___y_2300_ = v_a_2271_;
v___y_2301_ = v_a_2272_;
v___y_2302_ = v_a_2273_;
v___y_2303_ = v_a_2274_;
v___y_2304_ = v_a_2275_;
v___y_2305_ = v_a_2276_;
v___y_2306_ = v_a_2277_;
v___y_2307_ = v_a_2278_;
goto v___jp_2297_;
}
else
{
lean_dec_ref_known(v_e_2269_, 3);
return v___x_2540_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2542_; lean_object* v___f_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v_a_2551_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v_a_2566_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v_a_2571_; lean_object* v___y_2574_; lean_object* v___y_2575_; uint8_t v___y_2576_; uint8_t v___y_2577_; lean_object* v___y_2578_; lean_object* v_a_2579_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2588_; uint8_t v___y_2589_; uint8_t v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v_a_2593_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v_a_2598_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v_a_2610_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v_a_2615_; lean_object* v___y_2618_; uint8_t v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; uint8_t v___y_2622_; lean_object* v_a_2623_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2632_; uint8_t v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v_a_2636_; 
v_inheritedTraceOptions_2542_ = lean_ctor_get(v_a_2277_, 13);
lean_inc_ref(v_e_2269_);
lean_inc(v_idx_2295_);
lean_inc(v_typeName_2294_);
v___f_2543_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___boxed), 14, 3);
lean_closure_set(v___f_2543_, 0, v_typeName_2294_);
lean_closure_set(v___f_2543_, 1, v_idx_2295_);
lean_closure_set(v___f_2543_, 2, v_e_2269_);
v___x_2544_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_2545_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_2546_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3);
v___x_2547_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2542_, v_options_2538_, v___x_2546_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2839_; uint8_t v___x_2840_; 
v___x_2839_ = l_Lean_trace_profiler;
v___x_2840_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_2538_, v___x_2839_);
if (v___x_2840_ == 0)
{
lean_object* v___x_2841_; 
lean_dec_ref(v___f_2543_);
lean_inc(v_a_2278_);
lean_inc_ref(v_a_2277_);
lean_inc(v_a_2276_);
lean_inc_ref(v_a_2275_);
lean_inc(v_a_2274_);
lean_inc_ref(v_a_2273_);
lean_inc(v_a_2272_);
lean_inc_ref(v_a_2271_);
lean_inc(v_a_2270_);
lean_inc_ref(v_struct_2296_);
v___x_2841_ = lean_sym_simp(v_struct_2296_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2842_);
lean_dec_ref_known(v___x_2841_, 1);
v_res_2298_ = v_a_2842_;
v___y_2299_ = v_a_2270_;
v___y_2300_ = v_a_2271_;
v___y_2301_ = v_a_2272_;
v___y_2302_ = v_a_2273_;
v___y_2303_ = v_a_2274_;
v___y_2304_ = v_a_2275_;
v___y_2305_ = v_a_2276_;
v___y_2306_ = v_a_2277_;
v___y_2307_ = v_a_2278_;
goto v___jp_2297_;
}
else
{
lean_dec_ref_known(v_e_2269_, 3);
return v___x_2841_;
}
}
else
{
goto v___jp_2639_;
}
}
else
{
goto v___jp_2639_;
}
v___jp_2548_:
{
lean_object* v___x_2552_; double v___x_2553_; double v___x_2554_; double v___x_2555_; double v___x_2556_; double v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2552_ = lean_io_mono_nanos_now();
v___x_2553_ = lean_float_of_nat(v___y_2549_);
v___x_2554_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_2555_ = lean_float_div(v___x_2553_, v___x_2554_);
v___x_2556_ = lean_float_of_nat(v___x_2552_);
v___x_2557_ = lean_float_div(v___x_2556_, v___x_2554_);
v___x_2558_ = lean_box_float(v___x_2555_);
v___x_2559_ = lean_box_float(v___x_2557_);
v___x_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2558_);
lean_ctor_set(v___x_2560_, 1, v___x_2559_);
v___x_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2561_, 0, v_a_2551_);
lean_ctor_set(v___x_2561_, 1, v___x_2560_);
v___x_2562_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4(v___x_2544_, v_hasTrace_2539_, v___x_2545_, v_options_2538_, v___x_2547_, v___y_2550_, v___f_2543_, v___x_2561_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
return v___x_2562_;
}
v___jp_2563_:
{
lean_object* v___x_2567_; 
v___x_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2567_, 0, v_a_2566_);
v___y_2549_ = v___y_2564_;
v___y_2550_ = v___y_2565_;
v_a_2551_ = v___x_2567_;
goto v___jp_2548_;
}
v___jp_2568_:
{
lean_object* v___x_2572_; 
v___x_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2572_, 0, v_a_2571_);
v___y_2549_ = v___y_2569_;
v___y_2550_ = v___y_2570_;
v_a_2551_ = v___x_2572_;
goto v___jp_2548_;
}
v___jp_2573_:
{
lean_object* v___x_2580_; 
v___x_2580_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2580_, 0, v_a_2579_);
lean_ctor_set(v___x_2580_, 1, v___y_2575_);
lean_ctor_set_uint8(v___x_2580_, sizeof(void*)*2, v___y_2576_);
lean_ctor_set_uint8(v___x_2580_, sizeof(void*)*2 + 1, v___y_2577_);
v___y_2569_ = v___y_2574_;
v___y_2570_ = v___y_2578_;
v_a_2571_ = v___x_2580_;
goto v___jp_2568_;
}
v___jp_2581_:
{
if (lean_obj_tag(v___y_2584_) == 0)
{
lean_object* v_a_2585_; 
v_a_2585_ = lean_ctor_get(v___y_2584_, 0);
lean_inc(v_a_2585_);
lean_dec_ref_known(v___y_2584_, 1);
v___y_2569_ = v___y_2582_;
v___y_2570_ = v___y_2583_;
v_a_2571_ = v_a_2585_;
goto v___jp_2568_;
}
else
{
lean_object* v_a_2586_; 
v_a_2586_ = lean_ctor_get(v___y_2584_, 0);
lean_inc(v_a_2586_);
lean_dec_ref_known(v___y_2584_, 1);
v___y_2564_ = v___y_2582_;
v___y_2565_ = v___y_2583_;
v_a_2566_ = v_a_2586_;
goto v___jp_2563_;
}
}
v___jp_2587_:
{
lean_object* v___x_2594_; 
v___x_2594_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2594_, 0, v_a_2593_);
lean_ctor_set(v___x_2594_, 1, v___y_2591_);
lean_ctor_set_uint8(v___x_2594_, sizeof(void*)*2, v___y_2589_);
lean_ctor_set_uint8(v___x_2594_, sizeof(void*)*2 + 1, v___y_2590_);
v___y_2569_ = v___y_2588_;
v___y_2570_ = v___y_2592_;
v_a_2571_ = v___x_2594_;
goto v___jp_2568_;
}
v___jp_2595_:
{
lean_object* v___x_2599_; double v___x_2600_; double v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; 
v___x_2599_ = lean_io_get_num_heartbeats();
v___x_2600_ = lean_float_of_nat(v___y_2596_);
v___x_2601_ = lean_float_of_nat(v___x_2599_);
v___x_2602_ = lean_box_float(v___x_2600_);
v___x_2603_ = lean_box_float(v___x_2601_);
v___x_2604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2602_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
v___x_2605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2605_, 0, v_a_2598_);
lean_ctor_set(v___x_2605_, 1, v___x_2604_);
v___x_2606_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4(v___x_2544_, v_hasTrace_2539_, v___x_2545_, v_options_2538_, v___x_2547_, v___y_2597_, v___f_2543_, v___x_2605_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
return v___x_2606_;
}
v___jp_2607_:
{
lean_object* v___x_2611_; 
v___x_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2611_, 0, v_a_2610_);
v___y_2596_ = v___y_2608_;
v___y_2597_ = v___y_2609_;
v_a_2598_ = v___x_2611_;
goto v___jp_2595_;
}
v___jp_2612_:
{
lean_object* v___x_2616_; 
v___x_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2616_, 0, v_a_2615_);
v___y_2596_ = v___y_2613_;
v___y_2597_ = v___y_2614_;
v_a_2598_ = v___x_2616_;
goto v___jp_2595_;
}
v___jp_2617_:
{
lean_object* v___x_2624_; 
v___x_2624_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2624_, 0, v_a_2623_);
lean_ctor_set(v___x_2624_, 1, v___y_2620_);
lean_ctor_set_uint8(v___x_2624_, sizeof(void*)*2, v___y_2619_);
lean_ctor_set_uint8(v___x_2624_, sizeof(void*)*2 + 1, v___y_2622_);
v___y_2613_ = v___y_2618_;
v___y_2614_ = v___y_2621_;
v_a_2615_ = v___x_2624_;
goto v___jp_2612_;
}
v___jp_2625_:
{
if (lean_obj_tag(v___y_2628_) == 0)
{
lean_object* v_a_2629_; 
v_a_2629_ = lean_ctor_get(v___y_2628_, 0);
lean_inc(v_a_2629_);
lean_dec_ref_known(v___y_2628_, 1);
v___y_2613_ = v___y_2626_;
v___y_2614_ = v___y_2627_;
v_a_2615_ = v_a_2629_;
goto v___jp_2612_;
}
else
{
lean_object* v_a_2630_; 
v_a_2630_ = lean_ctor_get(v___y_2628_, 0);
lean_inc(v_a_2630_);
lean_dec_ref_known(v___y_2628_, 1);
v___y_2608_ = v___y_2626_;
v___y_2609_ = v___y_2627_;
v_a_2610_ = v_a_2630_;
goto v___jp_2607_;
}
}
v___jp_2631_:
{
uint8_t v___x_2637_; lean_object* v___x_2638_; 
v___x_2637_ = 0;
v___x_2638_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2638_, 0, v_a_2636_);
lean_ctor_set(v___x_2638_, 1, v___y_2634_);
lean_ctor_set_uint8(v___x_2638_, sizeof(void*)*2, v___y_2633_);
lean_ctor_set_uint8(v___x_2638_, sizeof(void*)*2 + 1, v___x_2637_);
v___y_2613_ = v___y_2632_;
v___y_2614_ = v___y_2635_;
v_a_2615_ = v___x_2638_;
goto v___jp_2612_;
}
v___jp_2639_:
{
lean_object* v___x_2640_; lean_object* v_a_2641_; lean_object* v___x_2642_; uint8_t v___x_2643_; 
v___x_2640_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg(v_a_2278_);
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_a_2641_);
lean_dec_ref(v___x_2640_);
v___x_2642_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2643_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_2538_, v___x_2642_);
if (v___x_2643_ == 0)
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2644_ = lean_io_mono_nanos_now();
lean_inc(v_a_2278_);
lean_inc_ref(v_a_2277_);
lean_inc(v_a_2276_);
lean_inc_ref(v_a_2275_);
lean_inc(v_a_2274_);
lean_inc_ref(v_a_2273_);
lean_inc(v_a_2272_);
lean_inc_ref(v_a_2271_);
lean_inc(v_a_2270_);
lean_inc_ref(v_struct_2296_);
v___x_2645_ = lean_sym_simp(v_struct_2296_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v_a_2646_; 
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2646_);
lean_dec_ref_known(v___x_2645_, 1);
if (lean_obj_tag(v_a_2646_) == 0)
{
uint8_t v_contextDependent_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2668_; 
v_contextDependent_2647_ = lean_ctor_get_uint8(v_a_2646_, 1);
v_isSharedCheck_2668_ = !lean_is_exclusive(v_a_2646_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2649_ = v_a_2646_;
v_isShared_2650_ = v_isSharedCheck_2668_;
goto v_resetjp_2648_;
}
else
{
lean_dec(v_a_2646_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2668_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
uint8_t v___x_2651_; lean_object* v___x_2652_; lean_object* v___f_2653_; lean_object* v___x_2654_; 
v___x_2651_ = 1;
v___x_2652_ = lean_box(v___x_2651_);
v___f_2653_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2653_, 0, v___x_2652_);
lean_closure_set(v___f_2653_, 1, v_e_2269_);
v___x_2654_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2653_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
lean_dec_ref_known(v___x_2654_, 1);
if (lean_obj_tag(v_a_2655_) == 1)
{
lean_object* v_val_2656_; lean_object* v___x_2657_; 
lean_del_object(v___x_2649_);
v_val_2656_ = lean_ctor_get(v_a_2655_, 0);
lean_inc(v_val_2656_);
lean_dec_ref_known(v_a_2655_, 1);
v___x_2657_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2656_, v_a_2274_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v___x_2659_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc_n(v_a_2658_, 2);
lean_dec_ref_known(v___x_2657_, 1);
v___x_2659_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_2658_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2661_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref_known(v___x_2659_, 1);
v___x_2661_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2661_, 0, v_a_2658_);
lean_ctor_set(v___x_2661_, 1, v_a_2660_);
lean_ctor_set_uint8(v___x_2661_, sizeof(void*)*2, v_contextDependent_2647_);
lean_ctor_set_uint8(v___x_2661_, sizeof(void*)*2 + 1, v___x_2643_);
v___y_2569_ = v___x_2644_;
v___y_2570_ = v_a_2641_;
v_a_2571_ = v___x_2661_;
goto v___jp_2568_;
}
else
{
lean_object* v_a_2662_; 
lean_dec(v_a_2658_);
v_a_2662_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2662_);
lean_dec_ref_known(v___x_2659_, 1);
v___y_2564_ = v___x_2644_;
v___y_2565_ = v_a_2641_;
v_a_2566_ = v_a_2662_;
goto v___jp_2563_;
}
}
else
{
lean_object* v_a_2663_; 
v_a_2663_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2663_);
lean_dec_ref_known(v___x_2657_, 1);
v___y_2564_ = v___x_2644_;
v___y_2565_ = v_a_2641_;
v_a_2566_ = v_a_2663_;
goto v___jp_2563_;
}
}
else
{
lean_object* v___x_2665_; 
lean_dec(v_a_2655_);
if (v_isShared_2650_ == 0)
{
v___x_2665_ = v___x_2649_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_2666_, 1, v_contextDependent_2647_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
lean_ctor_set_uint8(v___x_2665_, 0, v_hasTrace_2539_);
v___y_2569_ = v___x_2644_;
v___y_2570_ = v_a_2641_;
v_a_2571_ = v___x_2665_;
goto v___jp_2568_;
}
}
}
else
{
lean_object* v_a_2667_; 
lean_del_object(v___x_2649_);
v_a_2667_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2667_);
lean_dec_ref_known(v___x_2654_, 1);
v___y_2564_ = v___x_2644_;
v___y_2565_ = v_a_2641_;
v_a_2566_ = v_a_2667_;
goto v___jp_2563_;
}
}
}
else
{
lean_object* v_e_x27_2669_; lean_object* v_proof_2670_; uint8_t v_contextDependent_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2740_; 
v_e_x27_2669_ = lean_ctor_get(v_a_2646_, 0);
v_proof_2670_ = lean_ctor_get(v_a_2646_, 1);
v_contextDependent_2671_ = lean_ctor_get_uint8(v_a_2646_, sizeof(void*)*2 + 1);
v_isSharedCheck_2740_ = !lean_is_exclusive(v_a_2646_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2673_ = v_a_2646_;
v_isShared_2674_ = v_isSharedCheck_2740_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_proof_2670_);
lean_inc(v_e_x27_2669_);
lean_dec(v_a_2646_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2740_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2675_; 
lean_inc_ref(v_e_x27_2669_);
v___x_2675_ = l_Lean_Meta_Sym_inferType___redArg(v_e_x27_2669_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v___x_2675_, 1);
v___x_2677_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1));
v___x_2678_ = 0;
v___x_2679_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2);
lean_inc(v_idx_2295_);
lean_inc(v_typeName_2294_);
v___x_2680_ = l_Lean_Expr_proj___override(v_typeName_2294_, v_idx_2295_, v___x_2679_);
v___x_2681_ = l_Lean_mkLambda(v___x_2677_, v___x_2678_, v_a_2676_, v___x_2680_);
lean_inc_ref(v___x_2681_);
v___x_2682_ = l_Lean_Meta_Sym_inferType___redArg(v___x_2681_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; uint8_t v___x_2684_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v___x_2682_, 1);
v___x_2684_ = l_Lean_Expr_isArrow(v_a_2683_);
if (v___x_2684_ == 0)
{
uint8_t v___x_2685_; lean_object* v___x_2686_; lean_object* v___f_2687_; lean_object* v___x_2688_; 
lean_dec(v_a_2683_);
v___x_2685_ = 1;
v___x_2686_ = lean_box(v___x_2685_);
lean_inc_ref(v_e_2269_);
v___f_2687_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2687_, 0, v___x_2686_);
lean_closure_set(v___f_2687_, 1, v_e_2269_);
v___x_2688_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2687_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2688_) == 0)
{
lean_object* v_a_2689_; 
v_a_2689_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_a_2689_);
lean_dec_ref_known(v___x_2688_, 1);
if (lean_obj_tag(v_a_2689_) == 0)
{
lean_object* v___x_2690_; 
lean_del_object(v___x_2673_);
lean_inc_ref(v_e_x27_2669_);
lean_inc_ref(v_struct_2296_);
v___x_2690_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_struct_2296_, v_e_x27_2669_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v_a_2691_; uint8_t v___x_2692_; 
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2691_);
lean_dec_ref_known(v___x_2690_, 1);
v___x_2692_ = lean_unbox(v_a_2691_);
lean_dec(v_a_2691_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; 
lean_dec_ref(v___x_2681_);
lean_dec_ref(v_proof_2670_);
lean_dec_ref(v_e_x27_2669_);
lean_dec_ref_known(v_e_2269_, 3);
v___x_2693_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2693_, 0, v_hasTrace_2539_);
lean_ctor_set_uint8(v___x_2693_, 1, v_contextDependent_2671_);
v___y_2569_ = v___x_2644_;
v___y_2570_ = v_a_2641_;
v_a_2571_ = v___x_2693_;
goto v___jp_2568_;
}
else
{
lean_object* v___x_2694_; 
v___x_2694_ = l_Lean_Meta_mkHCongr(v___x_2681_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_object* v_a_2695_; lean_object* v_proof_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v_a_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2695_);
lean_dec_ref_known(v___x_2694_, 1);
v_proof_2696_ = lean_ctor_get(v_a_2695_, 1);
lean_inc_ref(v_proof_2696_);
lean_dec(v_a_2695_);
lean_inc_ref(v_e_x27_2669_);
lean_inc_ref(v_struct_2296_);
v___x_2697_ = l_Lean_mkApp3(v_proof_2696_, v_struct_2296_, v_e_x27_2669_, v_proof_2670_);
v___x_2698_ = l_Lean_Meta_mkEqOfHEq(v___x_2697_, v___x_2643_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; uint8_t v___x_2700_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
lean_dec_ref_known(v___x_2698_, 1);
v___x_2700_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2296_, v_e_x27_2669_);
if (v___x_2700_ == 0)
{
lean_object* v___x_2701_; 
lean_inc(v_idx_2295_);
lean_inc(v_typeName_2294_);
lean_dec_ref_known(v_e_2269_, 3);
v___x_2701_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2294_, v_idx_2295_, v_e_x27_2669_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___x_2701_, 1);
v___y_2574_ = v___x_2644_;
v___y_2575_ = v_a_2699_;
v___y_2576_ = v_contextDependent_2671_;
v___y_2577_ = v___x_2643_;
v___y_2578_ = v_a_2641_;
v_a_2579_ = v_a_2702_;
goto v___jp_2573_;
}
else
{
lean_object* v_a_2703_; 
lean_dec(v_a_2699_);
v_a_2703_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2703_);
lean_dec_ref_known(v___x_2701_, 1);
v___y_2564_ = v___x_2644_;
v___y_2565_ = v_a_2641_;
v_a_2566_ = v_a_2703_;
goto v___jp_2563_;
}
}
else
{
lean_dec_ref(v_e_x27_2669_);
v___y_2574_ = v___x_2644_;
v___y_2575_ = v_a_2699_;
v___y_2576_ = v_contextDependent_2671_;
v___y_2577_ = v___x_2643_;
v___y_2578_ = v_a_2641_;
v_a_2579_ = v_e_2269_;
goto v___jp_2573_;
}
}
else
{
lean_object* v_a_2704_; 
lean_dec_ref(v_e_x27_2669_);
lean_dec_ref_known(v_e_2269_, 3);
v_a_2704_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2698_, 1);
v___y_2564_ = v___x_2644_;
v___y_2565_ = v_a_2641_;
v_a_2566_ = v_a_2704_;
goto v___jp_2563_;
}
}
else
{
lean_object* v_a_2705_; 
lean_dec_ref(v_proof_2670_);
lean_dec_ref(v_e_x27_2669_);
lean_dec_ref_known(v_e_2269_, 3);
v_a_2705_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v___x_2694_, 1);
v___y_2564_ = v___x_2644_;
v___y_2565_ = v_a_2641_;
v_a_2566_ = v_a_2705_;
goto v___jp_2563_;
}
}
}
else
{
lean_object* v_a_2706_; 
lean_dec_ref(v___x_2681_);
lean_dec_ref(v_proof_2670_);
lean_dec_ref(v_e_x27_2669_);
lean_dec_ref_known(v_e_2269_, 3);
v_a_2706_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2690_, 1);
v___y_2564_ = v___x_2644_;
v___y_2565_ = v_a_2641_;
v_a_2566_ = v_a_2706_;
goto v___jp_2563_;
}
}
else
{
lean_object* v_val_2707_; lean_object* v___x_2708_; 
lean_dec_ref(v___x_2681_);
lean_dec_ref(v_proof_2670_);
lean_dec_ref(v_e_x27_2669_);
lean_dec_ref_known(v_e_2269_, 3);
v_val_2707_ = lean_ctor_get(v_a_2689_, 0);
lean_inc(v_val_2707_);
lean_dec_ref_known(v_a_2689_, 1);
v___x_2708_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2707_, v_a_2274_);
if (lean_obj_tag(v___x_2708_) == 0)
{
lean_object* v_a_2709_; lean_object* v___x_2710_; 
v_a_2709_ = lean_ctor_get(v___x_2708_, 0);
lean_inc_n(v_a_2709_, 2);
lean_dec_ref_known(v___x_2708_, 1);
v___x_2710_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_2709_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; lean_object* v___x_2713_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2711_);
lean_dec_ref_known(v___x_2710_, 1);
if (v_isShared_2674_ == 0)
{
lean_ctor_set(v___x_2673_, 1, v_a_2711_);
lean_ctor_set(v___x_2673_, 0, v_a_2709_);
v___x_2713_ = v___x_2673_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_a_2709_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v_a_2711_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
lean_ctor_set_uint8(v___x_2713_, sizeof(void*)*2, v_contextDependent_2671_);
lean_ctor_set_uint8(v___x_2713_, sizeof(void*)*2 + 1, v___x_2643_);
v___y_2569_ = v___x_2644_;
v___y_2570_ = v_a_2641_;
v_a_2571_ = v___x_2713_;
goto v___jp_2568_;
}
}
else
{
lean_object* v_a_2715_; 
lean_dec(v_a_2709_);
lean_del_object(v___x_2673_);
v_a_2715_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2715_);
lean_dec_ref_known(v___x_2710_, 1);
v___y_2564_ = v___x_2644_;
v___y_2565_ = v_a_2641_;
v_a_2566_ = v_a_2715_;
goto v___jp_2563_;
}
}
else
{
lean_object* v_a_2716_; 
lean_del_object(v___x_2673_);
v_a_2716_ = lean_ctor_get(v___x_2708_, 0);
lean_inc(v_a_2716_);
lean_dec_ref_known(v___x_2708_, 1);
v___y_2564_ = v___x_2644_;
v___y_2565_ = v_a_2641_;
v_a_2566_ = v_a_2716_;
goto v___jp_2563_;
}
}
}
else
{
lean_object* v_a_2717_; 
lean_dec_ref(v___x_2681_);
lean_del_object(v___x_2673_);
lean_dec_ref(v_proof_2670_);
lean_dec_ref(v_e_x27_2669_);
lean_dec_ref_known(v_e_2269_, 3);
v_a_2717_ = lean_ctor_get(v___x_2688_, 0);
lean_inc(v_a_2717_);
lean_dec_ref_known(v___x_2688_, 1);
v___y_2564_ = v___x_2644_;
v___y_2565_ = v_a_2641_;
v_a_2566_ = v_a_2717_;
goto v___jp_2563_;
}
}
else
{
lean_del_object(v___x_2673_);
if (lean_obj_tag(v_a_2683_) == 7)
{
lean_object* v_binderType_2718_; lean_object* v_body_2719_; lean_object* v___x_2720_; 
v_binderType_2718_ = lean_ctor_get(v_a_2683_, 1);
lean_inc_ref_n(v_binderType_2718_, 2);
v_body_2719_ = lean_ctor_get(v_a_2683_, 2);
lean_inc_ref(v_body_2719_);
lean_dec_ref_known(v_a_2683_, 3);
v___x_2720_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2718_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_a_2721_; lean_object* v___x_2722_; 
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2721_);
lean_dec_ref_known(v___x_2720_, 1);
lean_inc_ref(v_body_2719_);
v___x_2722_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_2719_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2722_) == 0)
{
lean_object* v_a_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; uint8_t v___x_2730_; 
v_a_2723_ = lean_ctor_get(v___x_2722_, 0);
lean_inc(v_a_2723_);
lean_dec_ref_known(v___x_2722_, 1);
v___x_2724_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4));
v___x_2725_ = lean_box(0);
v___x_2726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2726_, 0, v_a_2723_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
v___x_2727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2727_, 0, v_a_2721_);
lean_ctor_set(v___x_2727_, 1, v___x_2726_);
v___x_2728_ = l_Lean_mkConst(v___x_2724_, v___x_2727_);
lean_inc_ref(v_e_x27_2669_);
lean_inc_ref(v_struct_2296_);
v___x_2729_ = l_Lean_mkApp6(v___x_2728_, v_binderType_2718_, v_body_2719_, v_struct_2296_, v_e_x27_2669_, v___x_2681_, v_proof_2670_);
v___x_2730_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2296_, v_e_x27_2669_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2731_; 
lean_inc(v_idx_2295_);
lean_inc(v_typeName_2294_);
lean_dec_ref_known(v_e_2269_, 3);
v___x_2731_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2294_, v_idx_2295_, v_e_x27_2669_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2732_);
lean_dec_ref_known(v___x_2731_, 1);
v___y_2588_ = v___x_2644_;
v___y_2589_ = v_contextDependent_2671_;
v___y_2590_ = v___x_2643_;
v___y_2591_ = v___x_2729_;
v___y_2592_ = v_a_2641_;
v_a_2593_ = v_a_2732_;
goto v___jp_2587_;
}
else
{
lean_object* v_a_2733_; 
lean_dec_ref(v___x_2729_);
v_a_2733_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v___x_2731_, 1);
v___y_2564_ = v___x_2644_;
v___y_2565_ = v_a_2641_;
v_a_2566_ = v_a_2733_;
goto v___jp_2563_;
}
}
else
{
lean_dec_ref(v_e_x27_2669_);
v___y_2588_ = v___x_2644_;
v___y_2589_ = v_contextDependent_2671_;
v___y_2590_ = v___x_2643_;
v___y_2591_ = v___x_2729_;
v___y_2592_ = v_a_2641_;
v_a_2593_ = v_e_2269_;
goto v___jp_2587_;
}
}
else
{
lean_object* v_a_2734_; 
lean_dec(v_a_2721_);
lean_dec_ref(v_body_2719_);
lean_dec_ref(v_binderType_2718_);
lean_dec_ref(v___x_2681_);
lean_dec_ref(v_proof_2670_);
lean_dec_ref(v_e_x27_2669_);
lean_dec_ref_known(v_e_2269_, 3);
v_a_2734_ = lean_ctor_get(v___x_2722_, 0);
lean_inc(v_a_2734_);
lean_dec_ref_known(v___x_2722_, 1);
v___y_2564_ = v___x_2644_;
v___y_2565_ = v_a_2641_;
v_a_2566_ = v_a_2734_;
goto v___jp_2563_;
}
}
else
{
lean_object* v_a_2735_; 
lean_dec_ref(v_body_2719_);
lean_dec_ref(v_binderType_2718_);
lean_dec_ref(v___x_2681_);
lean_dec_ref(v_proof_2670_);
lean_dec_ref(v_e_x27_2669_);
lean_dec_ref_known(v_e_2269_, 3);
v_a_2735_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2735_);
lean_dec_ref_known(v___x_2720_, 1);
v___y_2564_ = v___x_2644_;
v___y_2565_ = v_a_2641_;
v_a_2566_ = v_a_2735_;
goto v___jp_2563_;
}
}
else
{
lean_object* v___x_2736_; lean_object* v___x_2737_; 
lean_dec(v_a_2683_);
lean_dec_ref(v___x_2681_);
lean_dec_ref(v_proof_2670_);
lean_dec_ref(v_e_x27_2669_);
lean_dec_ref_known(v_e_2269_, 3);
v___x_2736_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8);
v___x_2737_ = l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(v___x_2736_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
v___y_2582_ = v___x_2644_;
v___y_2583_ = v_a_2641_;
v___y_2584_ = v___x_2737_;
goto v___jp_2581_;
}
}
}
else
{
lean_object* v_a_2738_; 
lean_dec_ref(v___x_2681_);
lean_del_object(v___x_2673_);
lean_dec_ref(v_proof_2670_);
lean_dec_ref(v_e_x27_2669_);
lean_dec_ref_known(v_e_2269_, 3);
v_a_2738_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2738_);
lean_dec_ref_known(v___x_2682_, 1);
v___y_2564_ = v___x_2644_;
v___y_2565_ = v_a_2641_;
v_a_2566_ = v_a_2738_;
goto v___jp_2563_;
}
}
else
{
lean_object* v_a_2739_; 
lean_del_object(v___x_2673_);
lean_dec_ref(v_proof_2670_);
lean_dec_ref(v_e_x27_2669_);
lean_dec_ref_known(v_e_2269_, 3);
v_a_2739_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2739_);
lean_dec_ref_known(v___x_2675_, 1);
v___y_2564_ = v___x_2644_;
v___y_2565_ = v_a_2641_;
v_a_2566_ = v_a_2739_;
goto v___jp_2563_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2269_, 3);
v___y_2582_ = v___x_2644_;
v___y_2583_ = v_a_2641_;
v___y_2584_ = v___x_2645_;
goto v___jp_2581_;
}
}
else
{
lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2741_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2278_);
lean_inc_ref(v_a_2277_);
lean_inc(v_a_2276_);
lean_inc_ref(v_a_2275_);
lean_inc(v_a_2274_);
lean_inc_ref(v_a_2273_);
lean_inc(v_a_2272_);
lean_inc_ref(v_a_2271_);
lean_inc(v_a_2270_);
lean_inc_ref(v_struct_2296_);
v___x_2742_ = lean_sym_simp(v_struct_2296_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2742_) == 0)
{
lean_object* v_a_2743_; 
v_a_2743_ = lean_ctor_get(v___x_2742_, 0);
lean_inc(v_a_2743_);
lean_dec_ref_known(v___x_2742_, 1);
if (lean_obj_tag(v_a_2743_) == 0)
{
uint8_t v_contextDependent_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2766_; 
v_contextDependent_2744_ = lean_ctor_get_uint8(v_a_2743_, 1);
v_isSharedCheck_2766_ = !lean_is_exclusive(v_a_2743_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2746_ = v_a_2743_;
v_isShared_2747_ = v_isSharedCheck_2766_;
goto v_resetjp_2745_;
}
else
{
lean_dec(v_a_2743_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2766_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
uint8_t v___x_2748_; lean_object* v___x_2749_; lean_object* v___f_2750_; lean_object* v___x_2751_; 
v___x_2748_ = 1;
v___x_2749_ = lean_box(v___x_2748_);
v___f_2750_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2750_, 0, v___x_2749_);
lean_closure_set(v___f_2750_, 1, v_e_2269_);
v___x_2751_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2750_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; 
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
lean_inc(v_a_2752_);
lean_dec_ref_known(v___x_2751_, 1);
if (lean_obj_tag(v_a_2752_) == 1)
{
lean_object* v_val_2753_; lean_object* v___x_2754_; 
lean_del_object(v___x_2746_);
v_val_2753_ = lean_ctor_get(v_a_2752_, 0);
lean_inc(v_val_2753_);
lean_dec_ref_known(v_a_2752_, 1);
v___x_2754_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2753_, v_a_2274_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v_a_2755_; lean_object* v___x_2756_; 
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc_n(v_a_2755_, 2);
lean_dec_ref_known(v___x_2754_, 1);
v___x_2756_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_2755_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; uint8_t v___x_2758_; lean_object* v___x_2759_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2757_);
lean_dec_ref_known(v___x_2756_, 1);
v___x_2758_ = 0;
v___x_2759_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2759_, 0, v_a_2755_);
lean_ctor_set(v___x_2759_, 1, v_a_2757_);
lean_ctor_set_uint8(v___x_2759_, sizeof(void*)*2, v_contextDependent_2744_);
lean_ctor_set_uint8(v___x_2759_, sizeof(void*)*2 + 1, v___x_2758_);
v___y_2613_ = v___x_2741_;
v___y_2614_ = v_a_2641_;
v_a_2615_ = v___x_2759_;
goto v___jp_2612_;
}
else
{
lean_object* v_a_2760_; 
lean_dec(v_a_2755_);
v_a_2760_ = lean_ctor_get(v___x_2756_, 0);
lean_inc(v_a_2760_);
lean_dec_ref_known(v___x_2756_, 1);
v___y_2608_ = v___x_2741_;
v___y_2609_ = v_a_2641_;
v_a_2610_ = v_a_2760_;
goto v___jp_2607_;
}
}
else
{
lean_object* v_a_2761_; 
v_a_2761_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_a_2761_);
lean_dec_ref_known(v___x_2754_, 1);
v___y_2608_ = v___x_2741_;
v___y_2609_ = v_a_2641_;
v_a_2610_ = v_a_2761_;
goto v___jp_2607_;
}
}
else
{
lean_object* v___x_2763_; 
lean_dec(v_a_2752_);
if (v_isShared_2747_ == 0)
{
v___x_2763_ = v___x_2746_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_2764_, 1, v_contextDependent_2744_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
lean_ctor_set_uint8(v___x_2763_, 0, v___x_2643_);
v___y_2613_ = v___x_2741_;
v___y_2614_ = v_a_2641_;
v_a_2615_ = v___x_2763_;
goto v___jp_2612_;
}
}
}
else
{
lean_object* v_a_2765_; 
lean_del_object(v___x_2746_);
v_a_2765_ = lean_ctor_get(v___x_2751_, 0);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2751_, 1);
v___y_2608_ = v___x_2741_;
v___y_2609_ = v_a_2641_;
v_a_2610_ = v_a_2765_;
goto v___jp_2607_;
}
}
}
else
{
lean_object* v_e_x27_2767_; lean_object* v_proof_2768_; uint8_t v_contextDependent_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2838_; 
v_e_x27_2767_ = lean_ctor_get(v_a_2743_, 0);
v_proof_2768_ = lean_ctor_get(v_a_2743_, 1);
v_contextDependent_2769_ = lean_ctor_get_uint8(v_a_2743_, sizeof(void*)*2 + 1);
v_isSharedCheck_2838_ = !lean_is_exclusive(v_a_2743_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2771_ = v_a_2743_;
v_isShared_2772_ = v_isSharedCheck_2838_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_proof_2768_);
lean_inc(v_e_x27_2767_);
lean_dec(v_a_2743_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2838_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2773_; 
lean_inc_ref(v_e_x27_2767_);
v___x_2773_ = l_Lean_Meta_Sym_inferType___redArg(v_e_x27_2767_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2775_; uint8_t v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
lean_dec_ref_known(v___x_2773_, 1);
v___x_2775_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1));
v___x_2776_ = 0;
v___x_2777_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2);
lean_inc(v_idx_2295_);
lean_inc(v_typeName_2294_);
v___x_2778_ = l_Lean_Expr_proj___override(v_typeName_2294_, v_idx_2295_, v___x_2777_);
v___x_2779_ = l_Lean_mkLambda(v___x_2775_, v___x_2776_, v_a_2774_, v___x_2778_);
lean_inc_ref(v___x_2779_);
v___x_2780_ = l_Lean_Meta_Sym_inferType___redArg(v___x_2779_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; uint8_t v___x_2782_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref_known(v___x_2780_, 1);
v___x_2782_ = l_Lean_Expr_isArrow(v_a_2781_);
if (v___x_2782_ == 0)
{
uint8_t v___x_2783_; lean_object* v___x_2784_; lean_object* v___f_2785_; lean_object* v___x_2786_; 
lean_dec(v_a_2781_);
v___x_2783_ = 1;
v___x_2784_ = lean_box(v___x_2783_);
lean_inc_ref(v_e_2269_);
v___f_2785_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2785_, 0, v___x_2784_);
lean_closure_set(v___f_2785_, 1, v_e_2269_);
v___x_2786_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2785_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
lean_dec_ref_known(v___x_2786_, 1);
if (lean_obj_tag(v_a_2787_) == 0)
{
lean_object* v___x_2788_; 
lean_del_object(v___x_2771_);
lean_inc_ref(v_e_x27_2767_);
lean_inc_ref(v_struct_2296_);
v___x_2788_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_struct_2296_, v_e_x27_2767_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; uint8_t v___x_2790_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2788_, 1);
v___x_2790_ = lean_unbox(v_a_2789_);
lean_dec(v_a_2789_);
if (v___x_2790_ == 0)
{
lean_object* v___x_2791_; 
lean_dec_ref(v___x_2779_);
lean_dec_ref(v_proof_2768_);
lean_dec_ref(v_e_x27_2767_);
lean_dec_ref_known(v_e_2269_, 3);
v___x_2791_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2791_, 0, v___x_2643_);
lean_ctor_set_uint8(v___x_2791_, 1, v_contextDependent_2769_);
v___y_2613_ = v___x_2741_;
v___y_2614_ = v_a_2641_;
v_a_2615_ = v___x_2791_;
goto v___jp_2612_;
}
else
{
lean_object* v___x_2792_; 
v___x_2792_ = l_Lean_Meta_mkHCongr(v___x_2779_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; lean_object* v_proof_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2793_);
lean_dec_ref_known(v___x_2792_, 1);
v_proof_2794_ = lean_ctor_get(v_a_2793_, 1);
lean_inc_ref(v_proof_2794_);
lean_dec(v_a_2793_);
lean_inc_ref(v_e_x27_2767_);
lean_inc_ref(v_struct_2296_);
v___x_2795_ = l_Lean_mkApp3(v_proof_2794_, v_struct_2296_, v_e_x27_2767_, v_proof_2768_);
v___x_2796_ = l_Lean_Meta_mkEqOfHEq(v___x_2795_, v___x_2782_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; uint8_t v___x_2798_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2797_);
lean_dec_ref_known(v___x_2796_, 1);
v___x_2798_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2296_, v_e_x27_2767_);
if (v___x_2798_ == 0)
{
lean_object* v___x_2799_; 
lean_inc(v_idx_2295_);
lean_inc(v_typeName_2294_);
lean_dec_ref_known(v_e_2269_, 3);
v___x_2799_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2294_, v_idx_2295_, v_e_x27_2767_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2799_, 1);
v___y_2618_ = v___x_2741_;
v___y_2619_ = v_contextDependent_2769_;
v___y_2620_ = v_a_2797_;
v___y_2621_ = v_a_2641_;
v___y_2622_ = v___x_2782_;
v_a_2623_ = v_a_2800_;
goto v___jp_2617_;
}
else
{
lean_object* v_a_2801_; 
lean_dec(v_a_2797_);
v_a_2801_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2801_);
lean_dec_ref_known(v___x_2799_, 1);
v___y_2608_ = v___x_2741_;
v___y_2609_ = v_a_2641_;
v_a_2610_ = v_a_2801_;
goto v___jp_2607_;
}
}
else
{
lean_dec_ref(v_e_x27_2767_);
v___y_2618_ = v___x_2741_;
v___y_2619_ = v_contextDependent_2769_;
v___y_2620_ = v_a_2797_;
v___y_2621_ = v_a_2641_;
v___y_2622_ = v___x_2782_;
v_a_2623_ = v_e_2269_;
goto v___jp_2617_;
}
}
else
{
lean_object* v_a_2802_; 
lean_dec_ref(v_e_x27_2767_);
lean_dec_ref_known(v_e_2269_, 3);
v_a_2802_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2802_);
lean_dec_ref_known(v___x_2796_, 1);
v___y_2608_ = v___x_2741_;
v___y_2609_ = v_a_2641_;
v_a_2610_ = v_a_2802_;
goto v___jp_2607_;
}
}
else
{
lean_object* v_a_2803_; 
lean_dec_ref(v_proof_2768_);
lean_dec_ref(v_e_x27_2767_);
lean_dec_ref_known(v_e_2269_, 3);
v_a_2803_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2803_);
lean_dec_ref_known(v___x_2792_, 1);
v___y_2608_ = v___x_2741_;
v___y_2609_ = v_a_2641_;
v_a_2610_ = v_a_2803_;
goto v___jp_2607_;
}
}
}
else
{
lean_object* v_a_2804_; 
lean_dec_ref(v___x_2779_);
lean_dec_ref(v_proof_2768_);
lean_dec_ref(v_e_x27_2767_);
lean_dec_ref_known(v_e_2269_, 3);
v_a_2804_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2804_);
lean_dec_ref_known(v___x_2788_, 1);
v___y_2608_ = v___x_2741_;
v___y_2609_ = v_a_2641_;
v_a_2610_ = v_a_2804_;
goto v___jp_2607_;
}
}
else
{
lean_object* v_val_2805_; lean_object* v___x_2806_; 
lean_dec_ref(v___x_2779_);
lean_dec_ref(v_proof_2768_);
lean_dec_ref(v_e_x27_2767_);
lean_dec_ref_known(v_e_2269_, 3);
v_val_2805_ = lean_ctor_get(v_a_2787_, 0);
lean_inc(v_val_2805_);
lean_dec_ref_known(v_a_2787_, 1);
v___x_2806_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2805_, v_a_2274_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v___x_2808_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc_n(v_a_2807_, 2);
lean_dec_ref_known(v___x_2806_, 1);
v___x_2808_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_2807_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2811_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_a_2809_);
lean_dec_ref_known(v___x_2808_, 1);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 1, v_a_2809_);
lean_ctor_set(v___x_2771_, 0, v_a_2807_);
v___x_2811_ = v___x_2771_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2812_; 
v_reuseFailAlloc_2812_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2812_, 0, v_a_2807_);
lean_ctor_set(v_reuseFailAlloc_2812_, 1, v_a_2809_);
v___x_2811_ = v_reuseFailAlloc_2812_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
lean_ctor_set_uint8(v___x_2811_, sizeof(void*)*2, v_contextDependent_2769_);
lean_ctor_set_uint8(v___x_2811_, sizeof(void*)*2 + 1, v___x_2782_);
v___y_2613_ = v___x_2741_;
v___y_2614_ = v_a_2641_;
v_a_2615_ = v___x_2811_;
goto v___jp_2612_;
}
}
else
{
lean_object* v_a_2813_; 
lean_dec(v_a_2807_);
lean_del_object(v___x_2771_);
v_a_2813_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_a_2813_);
lean_dec_ref_known(v___x_2808_, 1);
v___y_2608_ = v___x_2741_;
v___y_2609_ = v_a_2641_;
v_a_2610_ = v_a_2813_;
goto v___jp_2607_;
}
}
else
{
lean_object* v_a_2814_; 
lean_del_object(v___x_2771_);
v_a_2814_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2814_);
lean_dec_ref_known(v___x_2806_, 1);
v___y_2608_ = v___x_2741_;
v___y_2609_ = v_a_2641_;
v_a_2610_ = v_a_2814_;
goto v___jp_2607_;
}
}
}
else
{
lean_object* v_a_2815_; 
lean_dec_ref(v___x_2779_);
lean_del_object(v___x_2771_);
lean_dec_ref(v_proof_2768_);
lean_dec_ref(v_e_x27_2767_);
lean_dec_ref_known(v_e_2269_, 3);
v_a_2815_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2815_);
lean_dec_ref_known(v___x_2786_, 1);
v___y_2608_ = v___x_2741_;
v___y_2609_ = v_a_2641_;
v_a_2610_ = v_a_2815_;
goto v___jp_2607_;
}
}
else
{
lean_del_object(v___x_2771_);
if (lean_obj_tag(v_a_2781_) == 7)
{
lean_object* v_binderType_2816_; lean_object* v_body_2817_; lean_object* v___x_2818_; 
v_binderType_2816_ = lean_ctor_get(v_a_2781_, 1);
lean_inc_ref_n(v_binderType_2816_, 2);
v_body_2817_ = lean_ctor_get(v_a_2781_, 2);
lean_inc_ref(v_body_2817_);
lean_dec_ref_known(v_a_2781_, 3);
v___x_2818_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2816_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v___x_2820_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref_known(v___x_2818_, 1);
lean_inc_ref(v_body_2817_);
v___x_2820_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_2817_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2820_, 1);
v___x_2822_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4));
v___x_2823_ = lean_box(0);
v___x_2824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2824_, 0, v_a_2821_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2825_, 0, v_a_2819_);
lean_ctor_set(v___x_2825_, 1, v___x_2824_);
v___x_2826_ = l_Lean_mkConst(v___x_2822_, v___x_2825_);
lean_inc_ref(v_e_x27_2767_);
lean_inc_ref(v_struct_2296_);
v___x_2827_ = l_Lean_mkApp6(v___x_2826_, v_binderType_2816_, v_body_2817_, v_struct_2296_, v_e_x27_2767_, v___x_2779_, v_proof_2768_);
v___x_2828_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2296_, v_e_x27_2767_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2829_; 
lean_inc(v_idx_2295_);
lean_inc(v_typeName_2294_);
lean_dec_ref_known(v_e_2269_, 3);
v___x_2829_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2294_, v_idx_2295_, v_e_x27_2767_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2830_);
lean_dec_ref_known(v___x_2829_, 1);
v___y_2632_ = v___x_2741_;
v___y_2633_ = v_contextDependent_2769_;
v___y_2634_ = v___x_2827_;
v___y_2635_ = v_a_2641_;
v_a_2636_ = v_a_2830_;
goto v___jp_2631_;
}
else
{
lean_object* v_a_2831_; 
lean_dec_ref(v___x_2827_);
v_a_2831_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2829_, 1);
v___y_2608_ = v___x_2741_;
v___y_2609_ = v_a_2641_;
v_a_2610_ = v_a_2831_;
goto v___jp_2607_;
}
}
else
{
lean_dec_ref(v_e_x27_2767_);
v___y_2632_ = v___x_2741_;
v___y_2633_ = v_contextDependent_2769_;
v___y_2634_ = v___x_2827_;
v___y_2635_ = v_a_2641_;
v_a_2636_ = v_e_2269_;
goto v___jp_2631_;
}
}
else
{
lean_object* v_a_2832_; 
lean_dec(v_a_2819_);
lean_dec_ref(v_body_2817_);
lean_dec_ref(v_binderType_2816_);
lean_dec_ref(v___x_2779_);
lean_dec_ref(v_proof_2768_);
lean_dec_ref(v_e_x27_2767_);
lean_dec_ref_known(v_e_2269_, 3);
v_a_2832_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2832_);
lean_dec_ref_known(v___x_2820_, 1);
v___y_2608_ = v___x_2741_;
v___y_2609_ = v_a_2641_;
v_a_2610_ = v_a_2832_;
goto v___jp_2607_;
}
}
else
{
lean_object* v_a_2833_; 
lean_dec_ref(v_body_2817_);
lean_dec_ref(v_binderType_2816_);
lean_dec_ref(v___x_2779_);
lean_dec_ref(v_proof_2768_);
lean_dec_ref(v_e_x27_2767_);
lean_dec_ref_known(v_e_2269_, 3);
v_a_2833_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2833_);
lean_dec_ref_known(v___x_2818_, 1);
v___y_2608_ = v___x_2741_;
v___y_2609_ = v_a_2641_;
v_a_2610_ = v_a_2833_;
goto v___jp_2607_;
}
}
else
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
lean_dec(v_a_2781_);
lean_dec_ref(v___x_2779_);
lean_dec_ref(v_proof_2768_);
lean_dec_ref(v_e_x27_2767_);
lean_dec_ref_known(v_e_2269_, 3);
v___x_2834_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8);
v___x_2835_ = l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(v___x_2834_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
v___y_2626_ = v___x_2741_;
v___y_2627_ = v_a_2641_;
v___y_2628_ = v___x_2835_;
goto v___jp_2625_;
}
}
}
else
{
lean_object* v_a_2836_; 
lean_dec_ref(v___x_2779_);
lean_del_object(v___x_2771_);
lean_dec_ref(v_proof_2768_);
lean_dec_ref(v_e_x27_2767_);
lean_dec_ref_known(v_e_2269_, 3);
v_a_2836_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2836_);
lean_dec_ref_known(v___x_2780_, 1);
v___y_2608_ = v___x_2741_;
v___y_2609_ = v_a_2641_;
v_a_2610_ = v_a_2836_;
goto v___jp_2607_;
}
}
else
{
lean_object* v_a_2837_; 
lean_del_object(v___x_2771_);
lean_dec_ref(v_proof_2768_);
lean_dec_ref(v_e_x27_2767_);
lean_dec_ref_known(v_e_2269_, 3);
v_a_2837_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2837_);
lean_dec_ref_known(v___x_2773_, 1);
v___y_2608_ = v___x_2741_;
v___y_2609_ = v_a_2641_;
v_a_2610_ = v_a_2837_;
goto v___jp_2607_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2269_, 3);
v___y_2626_ = v___x_2741_;
v___y_2627_ = v_a_2641_;
v___y_2628_ = v___x_2742_;
goto v___jp_2625_;
}
}
}
}
v___jp_2297_:
{
if (lean_obj_tag(v_res_2298_) == 0)
{
uint8_t v_contextDependent_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2366_; 
v_contextDependent_2308_ = lean_ctor_get_uint8(v_res_2298_, 1);
v_isSharedCheck_2366_ = !lean_is_exclusive(v_res_2298_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2310_ = v_res_2298_;
v_isShared_2311_ = v_isSharedCheck_2366_;
goto v_resetjp_2309_;
}
else
{
lean_dec(v_res_2298_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2366_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
uint8_t v___x_2312_; lean_object* v___x_2313_; lean_object* v___f_2314_; lean_object* v___x_2315_; 
v___x_2312_ = 1;
v___x_2313_ = lean_box(v___x_2312_);
v___f_2314_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2314_, 0, v___x_2313_);
lean_closure_set(v___f_2314_, 1, v_e_2269_);
v___x_2315_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2314_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2357_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2318_ = v___x_2315_;
v_isShared_2319_ = v_isSharedCheck_2357_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2357_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
if (lean_obj_tag(v_a_2316_) == 1)
{
lean_object* v_val_2320_; lean_object* v___x_2321_; 
lean_del_object(v___x_2318_);
lean_del_object(v___x_2310_);
v_val_2320_ = lean_ctor_get(v_a_2316_, 0);
lean_inc(v_val_2320_);
lean_dec_ref_known(v_a_2316_, 1);
v___x_2321_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2320_, v___y_2303_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v___x_2323_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc_n(v_a_2322_, 2);
lean_dec_ref_known(v___x_2321_, 1);
v___x_2323_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_2322_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2333_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2326_ = v___x_2323_;
v_isShared_2327_ = v_isSharedCheck_2333_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_a_2324_);
lean_dec(v___x_2323_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2333_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
uint8_t v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2328_ = 0;
v___x_2329_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2329_, 0, v_a_2322_);
lean_ctor_set(v___x_2329_, 1, v_a_2324_);
lean_ctor_set_uint8(v___x_2329_, sizeof(void*)*2, v_contextDependent_2308_);
lean_ctor_set_uint8(v___x_2329_, sizeof(void*)*2 + 1, v___x_2328_);
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v___x_2329_);
v___x_2331_ = v___x_2326_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
else
{
lean_object* v_a_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2341_; 
lean_dec(v_a_2322_);
v_a_2334_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2341_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2341_ == 0)
{
v___x_2336_ = v___x_2323_;
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_a_2334_);
lean_dec(v___x_2323_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2341_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2339_; 
if (v_isShared_2337_ == 0)
{
v___x_2339_ = v___x_2336_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
v___x_2339_ = v_reuseFailAlloc_2340_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
return v___x_2339_;
}
}
}
}
else
{
lean_object* v_a_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2349_; 
v_a_2342_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2344_ = v___x_2321_;
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_a_2342_);
lean_dec(v___x_2321_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2349_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2347_; 
if (v_isShared_2345_ == 0)
{
v___x_2347_ = v___x_2344_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
v___x_2347_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
return v___x_2347_;
}
}
}
}
else
{
uint8_t v___x_2350_; lean_object* v___x_2352_; 
lean_dec(v_a_2316_);
v___x_2350_ = 1;
if (v_isShared_2311_ == 0)
{
v___x_2352_ = v___x_2310_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_2356_, 1, v_contextDependent_2308_);
v___x_2352_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
lean_object* v___x_2354_; 
lean_ctor_set_uint8(v___x_2352_, 0, v___x_2350_);
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v___x_2352_);
v___x_2354_ = v___x_2318_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2352_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_del_object(v___x_2310_);
v_a_2358_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2315_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2315_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
}
else
{
lean_object* v_e_x27_2367_; lean_object* v_proof_2368_; uint8_t v_contextDependent_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2537_; 
v_e_x27_2367_ = lean_ctor_get(v_res_2298_, 0);
v_proof_2368_ = lean_ctor_get(v_res_2298_, 1);
v_contextDependent_2369_ = lean_ctor_get_uint8(v_res_2298_, sizeof(void*)*2 + 1);
v_isSharedCheck_2537_ = !lean_is_exclusive(v_res_2298_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2371_ = v_res_2298_;
v_isShared_2372_ = v_isSharedCheck_2537_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_proof_2368_);
lean_inc(v_e_x27_2367_);
lean_dec(v_res_2298_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2537_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2373_; 
lean_inc_ref(v_e_x27_2367_);
v___x_2373_ = l_Lean_Meta_Sym_inferType___redArg(v_e_x27_2367_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v_a_2374_; lean_object* v___x_2375_; uint8_t v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_a_2374_);
lean_dec_ref_known(v___x_2373_, 1);
v___x_2375_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1));
v___x_2376_ = 0;
v___x_2377_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2);
lean_inc(v_idx_2295_);
lean_inc(v_typeName_2294_);
v___x_2378_ = l_Lean_Expr_proj___override(v_typeName_2294_, v_idx_2295_, v___x_2377_);
v___x_2379_ = l_Lean_mkLambda(v___x_2375_, v___x_2376_, v_a_2374_, v___x_2378_);
lean_inc_ref(v___x_2379_);
v___x_2380_ = l_Lean_Meta_Sym_inferType___redArg(v___x_2379_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; uint8_t v___x_2382_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2381_);
lean_dec_ref_known(v___x_2380_, 1);
v___x_2382_ = l_Lean_Expr_isArrow(v_a_2381_);
if (v___x_2382_ == 0)
{
uint8_t v___x_2383_; lean_object* v___x_2384_; lean_object* v___f_2385_; lean_object* v___x_2386_; 
lean_dec(v_a_2381_);
v___x_2383_ = 1;
v___x_2384_ = lean_box(v___x_2383_);
lean_inc_ref(v_e_2269_);
v___f_2385_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2385_, 0, v___x_2384_);
lean_closure_set(v___f_2385_, 1, v_e_2269_);
v___x_2386_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2385_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v_a_2387_; 
v_a_2387_ = lean_ctor_get(v___x_2386_, 0);
lean_inc(v_a_2387_);
lean_dec_ref_known(v___x_2386_, 1);
if (lean_obj_tag(v_a_2387_) == 0)
{
lean_object* v___x_2388_; 
lean_del_object(v___x_2371_);
lean_inc_ref(v_e_x27_2367_);
lean_inc_ref(v_struct_2296_);
v___x_2388_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_struct_2296_, v_e_x27_2367_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2432_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2391_ = v___x_2388_;
v_isShared_2392_ = v_isSharedCheck_2432_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2388_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2432_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
uint8_t v___x_2393_; 
v___x_2393_ = lean_unbox(v_a_2389_);
lean_dec(v_a_2389_);
if (v___x_2393_ == 0)
{
uint8_t v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2397_; 
lean_dec_ref(v___x_2379_);
lean_dec_ref(v_proof_2368_);
lean_dec_ref(v_e_x27_2367_);
lean_dec_ref_known(v_e_2269_, 3);
v___x_2394_ = 1;
v___x_2395_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2395_, 0, v___x_2394_);
lean_ctor_set_uint8(v___x_2395_, 1, v_contextDependent_2369_);
if (v_isShared_2392_ == 0)
{
lean_ctor_set(v___x_2391_, 0, v___x_2395_);
v___x_2397_ = v___x_2391_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2395_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
else
{
lean_object* v___x_2399_; 
lean_del_object(v___x_2391_);
v___x_2399_ = l_Lean_Meta_mkHCongr(v___x_2379_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2400_; lean_object* v_proof_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_a_2400_);
lean_dec_ref_known(v___x_2399_, 1);
v_proof_2401_ = lean_ctor_get(v_a_2400_, 1);
lean_inc_ref(v_proof_2401_);
lean_dec(v_a_2400_);
lean_inc_ref(v_e_x27_2367_);
lean_inc_ref(v_struct_2296_);
v___x_2402_ = l_Lean_mkApp3(v_proof_2401_, v_struct_2296_, v_e_x27_2367_, v_proof_2368_);
v___x_2403_ = l_Lean_Meta_mkEqOfHEq(v___x_2402_, v___x_2382_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v_a_2404_; uint8_t v___x_2405_; 
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_a_2404_);
lean_dec_ref_known(v___x_2403_, 1);
v___x_2405_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2296_, v_e_x27_2367_);
if (v___x_2405_ == 0)
{
lean_object* v___x_2406_; 
lean_inc(v_idx_2295_);
lean_inc(v_typeName_2294_);
lean_dec_ref_known(v_e_2269_, 3);
v___x_2406_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2294_, v_idx_2295_, v_e_x27_2367_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2407_);
lean_dec_ref_known(v___x_2406_, 1);
v___y_2281_ = v_a_2404_;
v___y_2282_ = v___x_2382_;
v___y_2283_ = v_contextDependent_2369_;
v_a_2284_ = v_a_2407_;
goto v___jp_2280_;
}
else
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2415_; 
lean_dec(v_a_2404_);
v_a_2408_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2410_ = v___x_2406_;
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2406_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2415_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2413_; 
if (v_isShared_2411_ == 0)
{
v___x_2413_ = v___x_2410_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_a_2408_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
return v___x_2413_;
}
}
}
}
else
{
lean_dec_ref(v_e_x27_2367_);
v___y_2281_ = v_a_2404_;
v___y_2282_ = v___x_2382_;
v___y_2283_ = v_contextDependent_2369_;
v_a_2284_ = v_e_2269_;
goto v___jp_2280_;
}
}
else
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
lean_dec_ref(v_e_x27_2367_);
lean_dec_ref_known(v_e_2269_, 3);
v_a_2416_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2418_ = v___x_2403_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2403_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2416_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
lean_dec_ref(v_proof_2368_);
lean_dec_ref(v_e_x27_2367_);
lean_dec_ref_known(v_e_2269_, 3);
v_a_2424_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v___x_2399_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2399_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2424_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
}
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_dec_ref(v___x_2379_);
lean_dec_ref(v_proof_2368_);
lean_dec_ref(v_e_x27_2367_);
lean_dec_ref_known(v_e_2269_, 3);
v_a_2433_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2388_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2388_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
else
{
lean_object* v_val_2441_; lean_object* v___x_2442_; 
lean_dec_ref(v___x_2379_);
lean_dec_ref(v_proof_2368_);
lean_dec_ref(v_e_x27_2367_);
lean_dec_ref_known(v_e_2269_, 3);
v_val_2441_ = lean_ctor_get(v_a_2387_, 0);
lean_inc(v_val_2441_);
lean_dec_ref_known(v_a_2387_, 1);
v___x_2442_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_val_2441_, v___y_2303_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2444_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
lean_inc_n(v_a_2443_, 2);
lean_dec_ref_known(v___x_2442_, 1);
v___x_2444_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v_a_2443_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2455_; 
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2447_ = v___x_2444_;
v_isShared_2448_ = v_isSharedCheck_2455_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2444_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2455_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2450_; 
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 1, v_a_2445_);
lean_ctor_set(v___x_2371_, 0, v_a_2443_);
v___x_2450_ = v___x_2371_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2443_);
lean_ctor_set(v_reuseFailAlloc_2454_, 1, v_a_2445_);
v___x_2450_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
lean_object* v___x_2452_; 
lean_ctor_set_uint8(v___x_2450_, sizeof(void*)*2, v_contextDependent_2369_);
lean_ctor_set_uint8(v___x_2450_, sizeof(void*)*2 + 1, v___x_2382_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 0, v___x_2450_);
v___x_2452_ = v___x_2447_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v___x_2450_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
else
{
lean_object* v_a_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
lean_dec(v_a_2443_);
lean_del_object(v___x_2371_);
v_a_2456_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2444_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_a_2456_);
lean_dec(v___x_2444_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_a_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
else
{
lean_object* v_a_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2471_; 
lean_del_object(v___x_2371_);
v_a_2464_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2466_ = v___x_2442_;
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_a_2464_);
lean_dec(v___x_2442_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2471_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2469_; 
if (v_isShared_2467_ == 0)
{
v___x_2469_ = v___x_2466_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
}
}
else
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
lean_dec_ref(v___x_2379_);
lean_del_object(v___x_2371_);
lean_dec_ref(v_proof_2368_);
lean_dec_ref(v_e_x27_2367_);
lean_dec_ref_known(v_e_2269_, 3);
v_a_2472_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2386_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2386_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
else
{
lean_del_object(v___x_2371_);
if (lean_obj_tag(v_a_2381_) == 7)
{
lean_object* v_binderType_2480_; lean_object* v_body_2481_; lean_object* v___x_2482_; 
v_binderType_2480_ = lean_ctor_get(v_a_2381_, 1);
lean_inc_ref_n(v_binderType_2480_, 2);
v_body_2481_ = lean_ctor_get(v_a_2381_, 2);
lean_inc_ref(v_body_2481_);
lean_dec_ref_known(v_a_2381_, 3);
v___x_2482_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2480_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v_a_2483_; lean_object* v___x_2484_; 
v_a_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_a_2483_);
lean_dec_ref_known(v___x_2482_, 1);
lean_inc_ref(v_body_2481_);
v___x_2484_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_2481_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v_a_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; uint8_t v___x_2492_; 
v_a_2485_ = lean_ctor_get(v___x_2484_, 0);
lean_inc(v_a_2485_);
lean_dec_ref_known(v___x_2484_, 1);
v___x_2486_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4));
v___x_2487_ = lean_box(0);
v___x_2488_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2488_, 0, v_a_2485_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2489_, 0, v_a_2483_);
lean_ctor_set(v___x_2489_, 1, v___x_2488_);
v___x_2490_ = l_Lean_mkConst(v___x_2486_, v___x_2489_);
lean_inc_ref(v_e_x27_2367_);
lean_inc_ref(v_struct_2296_);
v___x_2491_ = l_Lean_mkApp6(v___x_2490_, v_binderType_2480_, v_body_2481_, v_struct_2296_, v_e_x27_2367_, v___x_2379_, v_proof_2368_);
v___x_2492_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2296_, v_e_x27_2367_);
if (v___x_2492_ == 0)
{
lean_object* v___x_2493_; 
lean_inc(v_idx_2295_);
lean_inc(v_typeName_2294_);
lean_dec_ref_known(v_e_2269_, 3);
v___x_2493_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2294_, v_idx_2295_, v_e_x27_2367_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_a_2494_; 
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_a_2494_);
lean_dec_ref_known(v___x_2493_, 1);
v___y_2288_ = v___x_2491_;
v___y_2289_ = v_contextDependent_2369_;
v_a_2290_ = v_a_2494_;
goto v___jp_2287_;
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_dec_ref(v___x_2491_);
v_a_2495_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2493_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2493_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
else
{
lean_dec_ref(v_e_x27_2367_);
v___y_2288_ = v___x_2491_;
v___y_2289_ = v_contextDependent_2369_;
v_a_2290_ = v_e_2269_;
goto v___jp_2287_;
}
}
else
{
lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
lean_dec(v_a_2483_);
lean_dec_ref(v_body_2481_);
lean_dec_ref(v_binderType_2480_);
lean_dec_ref(v___x_2379_);
lean_dec_ref(v_proof_2368_);
lean_dec_ref(v_e_x27_2367_);
lean_dec_ref_known(v_e_2269_, 3);
v_a_2503_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2505_ = v___x_2484_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2484_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
else
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2518_; 
lean_dec_ref(v_body_2481_);
lean_dec_ref(v_binderType_2480_);
lean_dec_ref(v___x_2379_);
lean_dec_ref(v_proof_2368_);
lean_dec_ref(v_e_x27_2367_);
lean_dec_ref_known(v_e_2269_, 3);
v_a_2511_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2513_ = v___x_2482_;
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2482_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2516_; 
if (v_isShared_2514_ == 0)
{
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
}
else
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
lean_dec(v_a_2381_);
lean_dec_ref(v___x_2379_);
lean_dec_ref(v_proof_2368_);
lean_dec_ref(v_e_x27_2367_);
lean_dec_ref_known(v_e_2269_, 3);
v___x_2519_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8);
v___x_2520_ = l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(v___x_2519_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_, v___y_2307_);
return v___x_2520_;
}
}
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
lean_dec_ref(v___x_2379_);
lean_del_object(v___x_2371_);
lean_dec_ref(v_proof_2368_);
lean_dec_ref(v_e_x27_2367_);
lean_dec_ref_known(v_e_2269_, 3);
v_a_2521_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2380_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2380_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2521_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2536_; 
lean_del_object(v___x_2371_);
lean_dec_ref(v_proof_2368_);
lean_dec_ref(v_e_x27_2367_);
lean_dec_ref_known(v_e_2269_, 3);
v_a_2529_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2531_ = v___x_2373_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2373_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2529_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
lean_dec_ref(v_e_2269_);
v___x_2843_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
return v___x_2844_;
}
v___jp_2280_:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2285_, 0, v_a_2284_);
lean_ctor_set(v___x_2285_, 1, v___y_2281_);
lean_ctor_set_uint8(v___x_2285_, sizeof(void*)*2, v___y_2283_);
lean_ctor_set_uint8(v___x_2285_, sizeof(void*)*2 + 1, v___y_2282_);
v___x_2286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
return v___x_2286_;
}
v___jp_2287_:
{
uint8_t v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2291_ = 0;
v___x_2292_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2292_, 0, v_a_2290_);
lean_ctor_set(v___x_2292_, 1, v___y_2288_);
lean_ctor_set_uint8(v___x_2292_, sizeof(void*)*2, v___y_2289_);
lean_ctor_set_uint8(v___x_2292_, sizeof(void*)*2 + 1, v___x_2291_);
v___x_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
return v___x_2293_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___boxed(lean_object* v_e_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(v_e_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_, v_a_2853_, v_a_2854_);
lean_dec(v_a_2854_);
lean_dec_ref(v_a_2853_);
lean_dec(v_a_2852_);
lean_dec_ref(v_a_2851_);
lean_dec(v_a_2850_);
lean_dec_ref(v_a_2849_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
lean_dec(v_a_2846_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5(lean_object* v_00_u03b1_2857_, lean_object* v_x_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_, lean_object* v___y_2865_, lean_object* v___y_2866_, lean_object* v___y_2867_){
_start:
{
lean_object* v___x_2869_; 
v___x_2869_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(v_x_2858_);
return v___x_2869_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___boxed(lean_object* v_00_u03b1_2870_, lean_object* v_x_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_, lean_object* v___y_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5(v_00_u03b1_2870_, v_x_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec(v___y_2876_);
lean_dec_ref(v___y_2875_);
lean_dec(v___y_2874_);
lean_dec_ref(v___y_2873_);
lean_dec(v___y_2872_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4(lean_object* v_oldTraces_2883_, lean_object* v_data_2884_, lean_object* v_ref_2885_, lean_object* v_msg_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___redArg(v_oldTraces_2883_, v_data_2884_, v_ref_2885_, v_msg_2886_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___boxed(lean_object* v_oldTraces_2898_, lean_object* v_data_2899_, lean_object* v_ref_2900_, lean_object* v_msg_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4(v_oldTraces_2898_, v_data_2899_, v_ref_2900_, v_msg_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec_ref(v___y_2905_);
lean_dec(v___y_2904_);
lean_dec_ref(v___y_2903_);
lean_dec(v___y_2902_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2913_, lean_object* v_a_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v___y_2923_; lean_object* v___x_2926_; uint8_t v_debug_2927_; 
v___x_2926_ = lean_st_ref_get(v___y_2916_);
v_debug_2927_ = lean_ctor_get_uint8(v___x_2926_, sizeof(void*)*10);
lean_dec(v___x_2926_);
if (v_debug_2927_ == 0)
{
v___y_2923_ = v___y_2916_;
goto v___jp_2922_;
}
else
{
lean_object* v___x_2928_; 
lean_inc_ref(v_f_2913_);
v___x_2928_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_2913_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_object* v___x_2929_; 
lean_dec_ref_known(v___x_2928_, 1);
lean_inc_ref(v_a_2914_);
v___x_2929_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_dec_ref_known(v___x_2929_, 1);
v___y_2923_ = v___y_2916_;
goto v___jp_2922_;
}
else
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
lean_dec_ref(v_a_2914_);
lean_dec_ref(v_f_2913_);
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2929_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2929_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
else
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
lean_dec_ref(v_a_2914_);
lean_dec_ref(v_f_2913_);
v_a_2938_ = lean_ctor_get(v___x_2928_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2928_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2940_ = v___x_2928_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2928_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2943_; 
if (v_isShared_2941_ == 0)
{
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2938_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
}
v___jp_2922_:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2924_ = l_Lean_Expr_app___override(v_f_2913_, v_a_2914_);
v___x_2925_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2924_, v___y_2923_);
return v___x_2925_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2946_, lean_object* v_a_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg(v_f_2946_, v_a_2947_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0(lean_object* v_args_2956_, lean_object* v_endIdx_2957_, lean_object* v_b_2958_, lean_object* v_i_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
uint8_t v___x_2970_; 
v___x_2970_ = lean_nat_dec_le(v_endIdx_2957_, v_i_2959_);
if (v___x_2970_ == 0)
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2971_ = l_Lean_instInhabitedExpr;
v___x_2972_ = lean_array_get_borrowed(v___x_2971_, v_args_2956_, v_i_2959_);
lean_inc(v___x_2972_);
v___x_2973_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg(v_b_2958_, v___x_2972_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
lean_inc(v_a_2974_);
lean_dec_ref_known(v___x_2973_, 1);
v___x_2975_ = lean_unsigned_to_nat(1u);
v___x_2976_ = lean_nat_add(v_i_2959_, v___x_2975_);
lean_dec(v_i_2959_);
v_b_2958_ = v_a_2974_;
v_i_2959_ = v___x_2976_;
goto _start;
}
else
{
lean_dec(v_i_2959_);
return v___x_2973_;
}
}
else
{
lean_object* v___x_2978_; 
lean_dec(v_i_2959_);
v___x_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2978_, 0, v_b_2958_);
return v___x_2978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0___boxed(lean_object* v_args_2979_, lean_object* v_endIdx_2980_, lean_object* v_b_2981_, lean_object* v_i_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_){
_start:
{
lean_object* v_res_2993_; 
v_res_2993_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0(v_args_2979_, v_endIdx_2980_, v_b_2981_, v_i_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_);
lean_dec(v___y_2991_);
lean_dec_ref(v___y_2990_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec(v_endIdx_2980_);
lean_dec_ref(v_args_2979_);
return v_res_2993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0(lean_object* v_f_2994_, lean_object* v_args_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_, lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3006_ = lean_unsigned_to_nat(0u);
v___x_3007_ = lean_array_get_size(v_args_2995_);
v___x_3008_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0(v_args_2995_, v___x_3007_, v_f_2994_, v___x_3006_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0___boxed(lean_object* v_f_3009_, lean_object* v_args_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0(v_f_3009_, v_args_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
lean_dec(v___y_3015_);
lean_dec_ref(v___y_3014_);
lean_dec(v___y_3013_);
lean_dec_ref(v___y_3012_);
lean_dec(v___y_3011_);
lean_dec_ref(v_args_3010_);
return v_res_3021_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0(void){
_start:
{
lean_object* v___x_3022_; lean_object* v_dummy_3023_; 
v___x_3022_ = lean_box(0);
v_dummy_3023_ = l_Lean_Expr_sort___override(v___x_3022_);
return v_dummy_3023_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2(void){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3025_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__1));
v___x_3026_ = l_Lean_stringToMessageData(v___x_3025_);
return v___x_3026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(lean_object* v_e_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_, lean_object* v_a_3030_, lean_object* v_a_3031_, lean_object* v_a_3032_, lean_object* v_a_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_){
_start:
{
uint8_t v___x_3041_; 
v___x_3041_ = l_Lean_Expr_isApp(v_e_3027_);
if (v___x_3041_ == 0)
{
lean_object* v___x_3042_; lean_object* v___x_3043_; 
lean_dec_ref(v_e_3027_);
v___x_3042_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3042_, 0, v___x_3041_);
lean_ctor_set_uint8(v___x_3042_, 1, v___x_3041_);
v___x_3043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3042_);
return v___x_3043_;
}
else
{
lean_object* v_fn_3044_; uint8_t v___x_3045_; 
v_fn_3044_ = l_Lean_Expr_getAppFn(v_e_3027_);
v___x_3045_ = l_Lean_Expr_isLambda(v_fn_3044_);
if (v___x_3045_ == 0)
{
uint8_t v___x_3046_; 
v___x_3046_ = l_Lean_Expr_isConst(v_fn_3044_);
if (v___x_3046_ == 0)
{
lean_object* v___x_3047_; 
lean_inc(v_a_3036_);
lean_inc_ref(v_a_3035_);
lean_inc(v_a_3034_);
lean_inc_ref(v_a_3033_);
lean_inc(v_a_3032_);
lean_inc_ref(v_a_3031_);
lean_inc(v_a_3030_);
lean_inc_ref(v_a_3029_);
lean_inc(v_a_3028_);
lean_inc_ref(v_fn_3044_);
v___x_3047_ = lean_sym_simp(v_fn_3044_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_object* v_a_3048_; 
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
if (lean_obj_tag(v_a_3048_) == 0)
{
lean_dec_ref_known(v_a_3048_, 0);
lean_dec_ref(v_fn_3044_);
lean_dec_ref(v_e_3027_);
return v___x_3047_;
}
else
{
lean_object* v_e_x27_3049_; lean_object* v_proof_3050_; uint8_t v_contextDependent_3051_; lean_object* v___x_3053_; uint8_t v_isShared_3054_; uint8_t v_isSharedCheck_3155_; 
lean_dec_ref_known(v___x_3047_, 1);
v_e_x27_3049_ = lean_ctor_get(v_a_3048_, 0);
v_proof_3050_ = lean_ctor_get(v_a_3048_, 1);
v_contextDependent_3051_ = lean_ctor_get_uint8(v_a_3048_, sizeof(void*)*2 + 1);
v_isSharedCheck_3155_ = !lean_is_exclusive(v_a_3048_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3053_ = v_a_3048_;
v_isShared_3054_ = v_isSharedCheck_3155_;
goto v_resetjp_3052_;
}
else
{
lean_inc(v_proof_3050_);
lean_inc(v_e_x27_3049_);
lean_dec(v_a_3048_);
v___x_3053_ = lean_box(0);
v_isShared_3054_ = v_isSharedCheck_3155_;
goto v_resetjp_3052_;
}
v_resetjp_3052_:
{
lean_object* v___x_3055_; 
lean_inc_ref(v_e_x27_3049_);
v___x_3055_ = l_Lean_Meta_Sym_inferType___redArg(v_e_x27_3049_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v_a_3056_; lean_object* v___x_3057_; lean_object* v_dummy_3058_; lean_object* v_nargs_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; 
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc(v_a_3056_);
lean_dec_ref_known(v___x_3055_, 1);
v___x_3057_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2);
v_dummy_3058_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0);
v_nargs_3059_ = l_Lean_Expr_getAppNumArgs(v_e_3027_);
lean_inc(v_nargs_3059_);
v___x_3060_ = lean_mk_array(v_nargs_3059_, v_dummy_3058_);
v___x_3061_ = lean_unsigned_to_nat(1u);
v___x_3062_ = lean_nat_sub(v_nargs_3059_, v___x_3061_);
lean_dec(v_nargs_3059_);
lean_inc_ref(v_e_3027_);
v___x_3063_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3027_, v___x_3060_, v___x_3062_);
v___x_3064_ = l_Lean_mkAppN(v___x_3057_, v___x_3063_);
lean_inc_ref(v_e_x27_3049_);
v___x_3065_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0(v_e_x27_3049_, v___x_3063_, v_a_3028_, v_a_3029_, v_a_3030_, v_a_3031_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_);
lean_dec_ref(v___x_3063_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v_a_3066_; lean_object* v___x_3067_; 
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
lean_inc(v_a_3066_);
lean_dec_ref_known(v___x_3065_, 1);
lean_inc_ref(v_e_3027_);
v___x_3067_ = l_Lean_Meta_Sym_inferType___redArg(v_e_3027_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_object* v_a_3068_; lean_object* v___x_3069_; uint8_t v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; 
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_a_3068_);
lean_dec_ref_known(v___x_3067_, 1);
v___x_3069_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1));
v___x_3070_ = 0;
lean_inc_n(v_a_3056_, 2);
v___x_3071_ = l_Lean_mkLambda(v___x_3069_, v___x_3070_, v_a_3056_, v___x_3064_);
v___x_3072_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_3056_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v_a_3073_; lean_object* v___x_3074_; 
v_a_3073_ = lean_ctor_get(v___x_3072_, 0);
lean_inc(v_a_3073_);
lean_dec_ref_known(v___x_3072_, 1);
lean_inc(v_a_3068_);
v___x_3074_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_3068_, v_a_3032_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v_options_3075_; lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3114_; 
v_options_3075_ = lean_ctor_get(v_a_3035_, 2);
v_a_3076_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3078_ = v___x_3074_;
v_isShared_3079_ = v_isSharedCheck_3114_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_dec(v___x_3074_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3114_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v_inheritedTraceOptions_3080_; uint8_t v_hasTrace_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v_inheritedTraceOptions_3080_ = lean_ctor_get(v_a_3035_, 13);
v_hasTrace_3081_ = lean_ctor_get_uint8(v_options_3075_, sizeof(void*)*1);
v___x_3082_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4));
v___x_3083_ = lean_box(0);
v___x_3084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3084_, 0, v_a_3076_);
lean_ctor_set(v___x_3084_, 1, v___x_3083_);
v___x_3085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3085_, 0, v_a_3073_);
lean_ctor_set(v___x_3085_, 1, v___x_3084_);
v___x_3086_ = l_Lean_mkConst(v___x_3082_, v___x_3085_);
v___x_3087_ = l_Lean_mkApp6(v___x_3086_, v_a_3056_, v_a_3068_, v_fn_3044_, v_e_x27_3049_, v___x_3071_, v_proof_3050_);
if (v_hasTrace_3081_ == 0)
{
lean_dec_ref(v_e_3027_);
goto v___jp_3088_;
}
else
{
lean_object* v___x_3095_; lean_object* v___x_3096_; uint8_t v___x_3097_; 
v___x_3095_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_3096_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3);
v___x_3097_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3080_, v_options_3075_, v___x_3096_);
if (v___x_3097_ == 0)
{
lean_dec_ref(v_e_3027_);
goto v___jp_3088_;
}
else
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; 
v___x_3098_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2);
v___x_3099_ = l_Lean_indentExpr(v_e_3027_);
v___x_3100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3098_);
lean_ctor_set(v___x_3100_, 1, v___x_3099_);
v___x_3101_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_3102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3102_, 0, v___x_3100_);
lean_ctor_set(v___x_3102_, 1, v___x_3101_);
lean_inc(v_a_3066_);
v___x_3103_ = l_Lean_indentExpr(v_a_3066_);
v___x_3104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3102_);
lean_ctor_set(v___x_3104_, 1, v___x_3103_);
v___x_3105_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_3095_, v___x_3104_, v_a_3033_, v_a_3034_, v_a_3035_, v_a_3036_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_dec_ref_known(v___x_3105_, 1);
goto v___jp_3088_;
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
lean_dec_ref(v___x_3087_);
lean_del_object(v___x_3078_);
lean_dec(v_a_3066_);
lean_del_object(v___x_3053_);
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v___x_3105_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3105_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3111_; 
if (v_isShared_3109_ == 0)
{
v___x_3111_ = v___x_3108_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
}
v___jp_3088_:
{
lean_object* v___x_3090_; 
if (v_isShared_3054_ == 0)
{
lean_ctor_set(v___x_3053_, 1, v___x_3087_);
lean_ctor_set(v___x_3053_, 0, v_a_3066_);
v___x_3090_ = v___x_3053_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3066_);
lean_ctor_set(v_reuseFailAlloc_3094_, 1, v___x_3087_);
v___x_3090_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
lean_object* v___x_3092_; 
lean_ctor_set_uint8(v___x_3090_, sizeof(void*)*2, v_contextDependent_3051_);
lean_ctor_set_uint8(v___x_3090_, sizeof(void*)*2 + 1, v___x_3046_);
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 0, v___x_3090_);
v___x_3092_ = v___x_3078_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v___x_3090_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
}
else
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3122_; 
lean_dec(v_a_3073_);
lean_dec_ref(v___x_3071_);
lean_dec(v_a_3068_);
lean_dec(v_a_3066_);
lean_dec(v_a_3056_);
lean_del_object(v___x_3053_);
lean_dec_ref(v_proof_3050_);
lean_dec_ref(v_e_x27_3049_);
lean_dec_ref(v_fn_3044_);
lean_dec_ref(v_e_3027_);
v_a_3115_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3117_ = v___x_3074_;
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3074_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3115_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
}
else
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
lean_dec_ref(v___x_3071_);
lean_dec(v_a_3068_);
lean_dec(v_a_3066_);
lean_dec(v_a_3056_);
lean_del_object(v___x_3053_);
lean_dec_ref(v_proof_3050_);
lean_dec_ref(v_e_x27_3049_);
lean_dec_ref(v_fn_3044_);
lean_dec_ref(v_e_3027_);
v_a_3123_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3072_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3072_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
lean_dec(v_a_3066_);
lean_dec_ref(v___x_3064_);
lean_dec(v_a_3056_);
lean_del_object(v___x_3053_);
lean_dec_ref(v_proof_3050_);
lean_dec_ref(v_e_x27_3049_);
lean_dec_ref(v_fn_3044_);
lean_dec_ref(v_e_3027_);
v_a_3131_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3067_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3067_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
lean_dec_ref(v___x_3064_);
lean_dec(v_a_3056_);
lean_del_object(v___x_3053_);
lean_dec_ref(v_proof_3050_);
lean_dec_ref(v_e_x27_3049_);
lean_dec_ref(v_fn_3044_);
lean_dec_ref(v_e_3027_);
v_a_3139_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_3065_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3065_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
else
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
lean_del_object(v___x_3053_);
lean_dec_ref(v_proof_3050_);
lean_dec_ref(v_e_x27_3049_);
lean_dec_ref(v_fn_3044_);
lean_dec_ref(v_e_3027_);
v_a_3147_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3055_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3055_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_fn_3044_);
lean_dec_ref(v_e_3027_);
return v___x_3047_;
}
}
else
{
lean_dec_ref(v_fn_3044_);
lean_dec_ref(v_e_3027_);
goto v___jp_3038_;
}
}
else
{
lean_dec_ref(v_fn_3044_);
lean_dec_ref(v_e_3027_);
goto v___jp_3038_;
}
}
v___jp_3038_:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3039_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
return v___x_3040_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___boxed(lean_object* v_e_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_, lean_object* v_a_3162_, lean_object* v_a_3163_, lean_object* v_a_3164_, lean_object* v_a_3165_, lean_object* v_a_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(v_e_3156_, v_a_3157_, v_a_3158_, v_a_3159_, v_a_3160_, v_a_3161_, v_a_3162_, v_a_3163_, v_a_3164_, v_a_3165_);
lean_dec(v_a_3165_);
lean_dec_ref(v_a_3164_);
lean_dec(v_a_3163_);
lean_dec_ref(v_a_3162_);
lean_dec(v_a_3161_);
lean_dec_ref(v_a_3160_);
lean_dec(v_a_3159_);
lean_dec_ref(v_a_3158_);
lean_dec(v_a_3157_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1(lean_object* v_f_3168_, lean_object* v_a_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_){
_start:
{
lean_object* v___x_3180_; 
v___x_3180_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg(v_f_3168_, v_a_3169_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_);
return v___x_3180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___boxed(lean_object* v_f_3181_, lean_object* v_a_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1(v_f_3181_, v_a_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
lean_dec(v___y_3191_);
lean_dec_ref(v___y_3190_);
lean_dec(v___y_3189_);
lean_dec_ref(v___y_3188_);
lean_dec(v___y_3187_);
lean_dec_ref(v___y_3186_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
return v_res_3193_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1(void){
_start:
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3195_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__0));
v___x_3196_ = l_Lean_stringToMessageData(v___x_3195_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(lean_object* v_e_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_, lean_object* v_a_3202_, lean_object* v_a_3203_, lean_object* v_a_3204_, lean_object* v_a_3205_, lean_object* v_a_3206_){
_start:
{
if (lean_obj_tag(v_e_3197_) == 4)
{
lean_object* v_declName_3208_; lean_object* v_us_3209_; lean_object* v___x_3210_; 
v_declName_3208_ = lean_ctor_get(v_e_3197_, 0);
v_us_3209_ = lean_ctor_get(v_e_3197_, 1);
lean_inc(v_declName_3208_);
v___x_3210_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(v_declName_3208_, v_a_3198_, v_a_3199_, v_a_3200_, v_a_3201_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3337_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3213_ = v___x_3210_;
v_isShared_3214_ = v_isSharedCheck_3337_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3210_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3337_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
uint8_t v___x_3215_; 
v___x_3215_ = l_Lean_ConstantInfo_isDefinition(v_a_3211_);
if (v___x_3215_ == 0)
{
lean_object* v___x_3216_; lean_object* v___x_3218_; 
lean_dec(v_a_3211_);
lean_dec_ref_known(v_e_3197_, 2);
v___x_3216_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3216_, 0, v___x_3215_);
lean_ctor_set_uint8(v___x_3216_, 1, v___x_3215_);
if (v_isShared_3214_ == 0)
{
lean_ctor_set(v___x_3213_, 0, v___x_3216_);
v___x_3218_ = v___x_3213_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v___x_3216_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
else
{
lean_object* v___x_3220_; 
v___x_3220_ = l_Lean_ConstantInfo_type(v_a_3211_);
if (lean_obj_tag(v___x_3220_) == 7)
{
lean_object* v___x_3221_; lean_object* v___x_3223_; 
lean_dec_ref_known(v___x_3220_, 3);
lean_dec(v_a_3211_);
lean_dec_ref_known(v_e_3197_, 2);
v___x_3221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
if (v_isShared_3214_ == 0)
{
lean_ctor_set(v___x_3213_, 0, v___x_3221_);
v___x_3223_ = v___x_3213_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v___x_3221_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
else
{
lean_object* v___x_3225_; 
v___x_3225_ = l_Lean_Meta_whnfD(v___x_3220_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3328_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3228_ = v___x_3225_;
v_isShared_3229_ = v_isSharedCheck_3328_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3225_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3328_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
uint8_t v___x_3230_; lean_object* v___y_3232_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; uint8_t v___y_3257_; 
v___x_3230_ = 0;
if (lean_obj_tag(v_a_3226_) == 7)
{
lean_object* v___x_3319_; lean_object* v___x_3321_; 
lean_dec_ref_known(v_a_3226_, 3);
lean_del_object(v___x_3228_);
lean_dec(v_a_3211_);
lean_dec_ref_known(v_e_3197_, 2);
v___x_3319_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
if (v_isShared_3214_ == 0)
{
lean_ctor_set(v___x_3213_, 0, v___x_3319_);
v___x_3321_ = v___x_3213_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3319_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
else
{
uint8_t v___x_3323_; 
lean_dec(v_a_3226_);
lean_del_object(v___x_3213_);
v___x_3323_ = l_Lean_ConstantInfo_hasValue(v_a_3211_, v___x_3230_);
if (v___x_3323_ == 0)
{
v___y_3257_ = v___x_3323_;
goto v___jp_3256_;
}
else
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; uint8_t v___x_3327_; 
v___x_3324_ = l_Lean_ConstantInfo_levelParams(v_a_3211_);
v___x_3325_ = l_List_lengthTR___redArg(v___x_3324_);
lean_dec(v___x_3324_);
v___x_3326_ = l_List_lengthTR___redArg(v_us_3209_);
v___x_3327_ = lean_nat_dec_eq(v___x_3325_, v___x_3326_);
lean_dec(v___x_3326_);
lean_dec(v___x_3325_);
v___y_3257_ = v___x_3327_;
goto v___jp_3256_;
}
}
v___jp_3231_:
{
lean_object* v___x_3238_; 
lean_inc_ref(v___y_3232_);
v___x_3238_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3247_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3241_ = v___x_3238_;
v_isShared_3242_ = v_isSharedCheck_3247_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3238_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3247_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3243_; lean_object* v___x_3245_; 
v___x_3243_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3243_, 0, v___y_3232_);
lean_ctor_set(v___x_3243_, 1, v_a_3239_);
lean_ctor_set_uint8(v___x_3243_, sizeof(void*)*2, v___x_3230_);
lean_ctor_set_uint8(v___x_3243_, sizeof(void*)*2 + 1, v___x_3230_);
if (v_isShared_3242_ == 0)
{
lean_ctor_set(v___x_3241_, 0, v___x_3243_);
v___x_3245_ = v___x_3241_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v___x_3243_);
v___x_3245_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
return v___x_3245_;
}
}
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_dec_ref(v___y_3232_);
v_a_3248_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3238_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3238_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
v___jp_3256_:
{
if (v___y_3257_ == 0)
{
lean_object* v___x_3258_; lean_object* v___x_3260_; 
lean_dec(v_a_3211_);
lean_dec_ref_known(v_e_3197_, 2);
v___x_3258_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v___x_3258_);
v___x_3260_ = v___x_3228_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v___x_3258_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
else
{
lean_object* v___x_3262_; 
lean_del_object(v___x_3228_);
lean_inc(v_us_3209_);
v___x_3262_ = l_Lean_Core_instantiateValueLevelParams(v_a_3211_, v_us_3209_, v___x_3230_, v_a_3205_, v_a_3206_);
lean_dec(v_a_3211_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_object* v_a_3263_; lean_object* v___x_3264_; 
v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
lean_inc(v_a_3263_);
lean_dec_ref_known(v___x_3262_, 1);
v___x_3264_ = l_Lean_Meta_Sym_unfoldReducible(v_a_3263_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_);
if (lean_obj_tag(v___x_3264_) == 0)
{
lean_object* v_a_3265_; lean_object* v___x_3266_; 
v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
lean_inc(v_a_3265_);
lean_dec_ref_known(v___x_3264_, 1);
v___x_3266_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_3265_, v_a_3202_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_options_3267_; uint8_t v_hasTrace_3268_; 
v_options_3267_ = lean_ctor_get(v_a_3205_, 2);
v_hasTrace_3268_ = lean_ctor_get_uint8(v_options_3267_, sizeof(void*)*1);
if (v_hasTrace_3268_ == 0)
{
lean_object* v_a_3269_; 
lean_dec_ref_known(v_e_3197_, 2);
v_a_3269_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_a_3269_);
lean_dec_ref_known(v___x_3266_, 1);
v___y_3232_ = v_a_3269_;
v___y_3233_ = v_a_3202_;
v___y_3234_ = v_a_3203_;
v___y_3235_ = v_a_3204_;
v___y_3236_ = v_a_3205_;
v___y_3237_ = v_a_3206_;
goto v___jp_3231_;
}
else
{
lean_object* v_a_3270_; lean_object* v_inheritedTraceOptions_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; uint8_t v___x_3274_; 
v_a_3270_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_a_3270_);
lean_dec_ref_known(v___x_3266_, 1);
v_inheritedTraceOptions_3271_ = lean_ctor_get(v_a_3205_, 13);
v___x_3272_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1));
v___x_3273_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2);
v___x_3274_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3271_, v_options_3267_, v___x_3273_);
if (v___x_3274_ == 0)
{
lean_dec_ref_known(v_e_3197_, 2);
v___y_3232_ = v_a_3270_;
v___y_3233_ = v_a_3202_;
v___y_3234_ = v_a_3203_;
v___y_3235_ = v_a_3204_;
v___y_3236_ = v_a_3205_;
v___y_3237_ = v_a_3206_;
goto v___jp_3231_;
}
else
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3275_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1);
lean_inc(v_declName_3208_);
v___x_3276_ = l_Lean_MessageData_ofName(v_declName_3208_);
v___x_3277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3275_);
lean_ctor_set(v___x_3277_, 1, v___x_3276_);
v___x_3278_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8);
v___x_3279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3277_);
lean_ctor_set(v___x_3279_, 1, v___x_3278_);
v___x_3280_ = l_Lean_indentExpr(v_e_3197_);
v___x_3281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3279_);
lean_ctor_set(v___x_3281_, 1, v___x_3280_);
v___x_3282_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_3283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3281_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
lean_inc(v_a_3270_);
v___x_3284_ = l_Lean_indentExpr(v_a_3270_);
v___x_3285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3283_);
lean_ctor_set(v___x_3285_, 1, v___x_3284_);
v___x_3286_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_3272_, v___x_3285_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_dec_ref_known(v___x_3286_, 1);
v___y_3232_ = v_a_3270_;
v___y_3233_ = v_a_3202_;
v___y_3234_ = v_a_3203_;
v___y_3235_ = v_a_3204_;
v___y_3236_ = v_a_3205_;
v___y_3237_ = v_a_3206_;
goto v___jp_3231_;
}
else
{
lean_object* v_a_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3294_; 
lean_dec(v_a_3270_);
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3294_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3294_ == 0)
{
v___x_3289_ = v___x_3286_;
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_a_3287_);
lean_dec(v___x_3286_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3294_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v___x_3292_; 
if (v_isShared_3290_ == 0)
{
v___x_3292_ = v___x_3289_;
goto v_reusejp_3291_;
}
else
{
lean_object* v_reuseFailAlloc_3293_; 
v_reuseFailAlloc_3293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3293_, 0, v_a_3287_);
v___x_3292_ = v_reuseFailAlloc_3293_;
goto v_reusejp_3291_;
}
v_reusejp_3291_:
{
return v___x_3292_;
}
}
}
}
}
}
else
{
lean_object* v_a_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3302_; 
lean_dec_ref_known(v_e_3197_, 2);
v_a_3295_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3302_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3302_ == 0)
{
v___x_3297_ = v___x_3266_;
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_a_3295_);
lean_dec(v___x_3266_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3302_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3300_; 
if (v_isShared_3298_ == 0)
{
v___x_3300_ = v___x_3297_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3301_; 
v_reuseFailAlloc_3301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3301_, 0, v_a_3295_);
v___x_3300_ = v_reuseFailAlloc_3301_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
return v___x_3300_;
}
}
}
}
else
{
lean_object* v_a_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3310_; 
lean_dec_ref_known(v_e_3197_, 2);
v_a_3303_ = lean_ctor_get(v___x_3264_, 0);
v_isSharedCheck_3310_ = !lean_is_exclusive(v___x_3264_);
if (v_isSharedCheck_3310_ == 0)
{
v___x_3305_ = v___x_3264_;
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_a_3303_);
lean_dec(v___x_3264_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3310_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3308_; 
if (v_isShared_3306_ == 0)
{
v___x_3308_ = v___x_3305_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_a_3303_);
v___x_3308_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
return v___x_3308_;
}
}
}
}
else
{
lean_object* v_a_3311_; lean_object* v___x_3313_; uint8_t v_isShared_3314_; uint8_t v_isSharedCheck_3318_; 
lean_dec_ref_known(v_e_3197_, 2);
v_a_3311_ = lean_ctor_get(v___x_3262_, 0);
v_isSharedCheck_3318_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3318_ == 0)
{
v___x_3313_ = v___x_3262_;
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
else
{
lean_inc(v_a_3311_);
lean_dec(v___x_3262_);
v___x_3313_ = lean_box(0);
v_isShared_3314_ = v_isSharedCheck_3318_;
goto v_resetjp_3312_;
}
v_resetjp_3312_:
{
lean_object* v___x_3316_; 
if (v_isShared_3314_ == 0)
{
v___x_3316_ = v___x_3313_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_a_3311_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3336_; 
lean_del_object(v___x_3213_);
lean_dec(v_a_3211_);
lean_dec_ref_known(v_e_3197_, 2);
v_a_3329_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3331_ = v___x_3225_;
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3225_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3334_; 
if (v_isShared_3332_ == 0)
{
v___x_3334_ = v___x_3331_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_a_3329_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3338_; lean_object* v___x_3340_; uint8_t v_isShared_3341_; uint8_t v_isSharedCheck_3345_; 
lean_dec_ref_known(v_e_3197_, 2);
v_a_3338_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3340_ = v___x_3210_;
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
else
{
lean_inc(v_a_3338_);
lean_dec(v___x_3210_);
v___x_3340_ = lean_box(0);
v_isShared_3341_ = v_isSharedCheck_3345_;
goto v_resetjp_3339_;
}
v_resetjp_3339_:
{
lean_object* v___x_3343_; 
if (v_isShared_3341_ == 0)
{
v___x_3343_ = v___x_3340_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v_a_3338_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
}
else
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
lean_dec_ref(v_e_3197_);
v___x_3346_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3347_, 0, v___x_3346_);
return v___x_3347_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___boxed(lean_object* v_e_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_){
_start:
{
lean_object* v_res_3359_; 
v_res_3359_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(v_e_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_);
lean_dec(v_a_3357_);
lean_dec_ref(v_a_3356_);
lean_dec(v_a_3355_);
lean_dec_ref(v_a_3354_);
lean_dec(v_a_3353_);
lean_dec_ref(v_a_3352_);
lean_dec(v_a_3351_);
lean_dec_ref(v_a_3350_);
lean_dec(v_a_3349_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(lean_object* v_x_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_){
_start:
{
lean_object* v___x_3372_; 
lean_inc_ref(v___y_3361_);
v___x_3372_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
if (lean_obj_tag(v___x_3372_) == 0)
{
lean_object* v_a_3373_; 
v_a_3373_ = lean_ctor_get(v___x_3372_, 0);
lean_inc(v_a_3373_);
if (lean_obj_tag(v_a_3373_) == 0)
{
uint8_t v_done_3374_; 
v_done_3374_ = lean_ctor_get_uint8(v_a_3373_, 0);
if (v_done_3374_ == 0)
{
uint8_t v_contextDependent_3375_; lean_object* v___x_3376_; 
lean_dec_ref_known(v___x_3372_, 1);
v_contextDependent_3375_ = lean_ctor_get_uint8(v_a_3373_, 1);
lean_dec_ref_known(v_a_3373_, 0);
v___x_3376_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v_a_3377_; uint8_t v___y_3379_; 
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
lean_inc(v_a_3377_);
if (v_contextDependent_3375_ == 0)
{
lean_dec(v_a_3377_);
return v___x_3376_;
}
else
{
if (lean_obj_tag(v_a_3377_) == 0)
{
uint8_t v_contextDependent_3389_; 
v_contextDependent_3389_ = lean_ctor_get_uint8(v_a_3377_, 1);
v___y_3379_ = v_contextDependent_3389_;
goto v___jp_3378_;
}
else
{
uint8_t v___x_3390_; 
v___x_3390_ = 0;
v___y_3379_ = v___x_3390_;
goto v___jp_3378_;
}
}
v___jp_3378_:
{
if (v___y_3379_ == 0)
{
lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3387_; 
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3387_ == 0)
{
lean_object* v_unused_3388_; 
v_unused_3388_ = lean_ctor_get(v___x_3376_, 0);
lean_dec(v_unused_3388_);
v___x_3381_ = v___x_3376_;
v_isShared_3382_ = v_isSharedCheck_3387_;
goto v_resetjp_3380_;
}
else
{
lean_dec(v___x_3376_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3387_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3383_; lean_object* v___x_3385_; 
v___x_3383_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3377_);
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 0, v___x_3383_);
v___x_3385_ = v___x_3381_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3383_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
return v___x_3385_;
}
}
}
else
{
lean_dec(v_a_3377_);
return v___x_3376_;
}
}
}
else
{
return v___x_3376_;
}
}
else
{
lean_dec_ref_known(v_a_3373_, 0);
lean_dec_ref(v___y_3361_);
return v___x_3372_;
}
}
else
{
lean_dec_ref_known(v_a_3373_, 2);
lean_dec_ref(v___y_3361_);
return v___x_3372_;
}
}
else
{
lean_dec_ref(v___y_3361_);
return v___x_3372_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0___boxed(lean_object* v_x_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v_x_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v___y_3393_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(lean_object* v_e_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_){
_start:
{
switch(lean_obj_tag(v_e_3407_))
{
case 9:
{
lean_object* v___x_3421_; 
v___x_3421_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(v_e_3407_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_);
return v___x_3421_;
}
case 11:
{
lean_object* v___x_3422_; 
v___x_3422_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(v_e_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_);
return v___x_3422_;
}
case 4:
{
lean_object* v___x_3423_; 
lean_inc_ref(v_e_3407_);
v___x_3423_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleOpaqueConst(v_e_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v_a_3424_; lean_object* v___x_3425_; 
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_a_3424_);
v___x_3425_ = lean_box(0);
if (lean_obj_tag(v_a_3424_) == 0)
{
uint8_t v_done_3426_; 
v_done_3426_ = lean_ctor_get_uint8(v_a_3424_, 0);
if (v_done_3426_ == 0)
{
uint8_t v_contextDependent_3427_; lean_object* v___x_3428_; 
lean_dec_ref_known(v___x_3423_, 1);
v_contextDependent_3427_ = lean_ctor_get_uint8(v_a_3424_, 1);
lean_dec_ref_known(v_a_3424_, 0);
v___x_3428_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v___x_3425_, v_e_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_a_3429_; uint8_t v___y_3431_; 
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_a_3429_);
if (v_contextDependent_3427_ == 0)
{
lean_dec(v_a_3429_);
return v___x_3428_;
}
else
{
if (lean_obj_tag(v_a_3429_) == 0)
{
uint8_t v_contextDependent_3441_; 
v_contextDependent_3441_ = lean_ctor_get_uint8(v_a_3429_, 1);
v___y_3431_ = v_contextDependent_3441_;
goto v___jp_3430_;
}
else
{
uint8_t v_contextDependent_3442_; 
v_contextDependent_3442_ = lean_ctor_get_uint8(v_a_3429_, sizeof(void*)*2 + 1);
v___y_3431_ = v_contextDependent_3442_;
goto v___jp_3430_;
}
}
v___jp_3430_:
{
if (v___y_3431_ == 0)
{
lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3439_; 
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3439_ == 0)
{
lean_object* v_unused_3440_; 
v_unused_3440_ = lean_ctor_get(v___x_3428_, 0);
lean_dec(v_unused_3440_);
v___x_3433_ = v___x_3428_;
v_isShared_3434_ = v_isSharedCheck_3439_;
goto v_resetjp_3432_;
}
else
{
lean_dec(v___x_3428_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3439_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v___x_3435_; lean_object* v___x_3437_; 
v___x_3435_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3429_);
if (v_isShared_3434_ == 0)
{
lean_ctor_set(v___x_3433_, 0, v___x_3435_);
v___x_3437_ = v___x_3433_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v___x_3435_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
else
{
lean_dec(v_a_3429_);
return v___x_3428_;
}
}
}
else
{
return v___x_3428_;
}
}
else
{
lean_dec_ref_known(v_a_3424_, 0);
lean_dec_ref_known(v_e_3407_, 2);
return v___x_3423_;
}
}
else
{
uint8_t v_done_3443_; 
v_done_3443_ = lean_ctor_get_uint8(v_a_3424_, sizeof(void*)*2);
if (v_done_3443_ == 0)
{
lean_object* v_e_x27_3444_; lean_object* v_proof_3445_; uint8_t v_contextDependent_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3496_; 
lean_dec_ref_known(v___x_3423_, 1);
v_e_x27_3444_ = lean_ctor_get(v_a_3424_, 0);
v_proof_3445_ = lean_ctor_get(v_a_3424_, 1);
v_contextDependent_3446_ = lean_ctor_get_uint8(v_a_3424_, sizeof(void*)*2 + 1);
v_isSharedCheck_3496_ = !lean_is_exclusive(v_a_3424_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3448_ = v_a_3424_;
v_isShared_3449_ = v_isSharedCheck_3496_;
goto v_resetjp_3447_;
}
else
{
lean_inc(v_proof_3445_);
lean_inc(v_e_x27_3444_);
lean_dec(v_a_3424_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3496_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3450_; 
lean_inc_ref(v_e_x27_3444_);
v___x_3450_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v___x_3425_, v_e_x27_3444_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3495_; 
v_a_3451_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3453_ = v___x_3450_;
v_isShared_3454_ = v_isSharedCheck_3495_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3450_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3495_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
if (lean_obj_tag(v_a_3451_) == 0)
{
uint8_t v_done_3455_; uint8_t v_contextDependent_3456_; uint8_t v___y_3458_; 
lean_dec_ref_known(v_e_3407_, 2);
v_done_3455_ = lean_ctor_get_uint8(v_a_3451_, 0);
v_contextDependent_3456_ = lean_ctor_get_uint8(v_a_3451_, 1);
lean_dec_ref_known(v_a_3451_, 0);
if (v_contextDependent_3446_ == 0)
{
v___y_3458_ = v_contextDependent_3456_;
goto v___jp_3457_;
}
else
{
v___y_3458_ = v_contextDependent_3446_;
goto v___jp_3457_;
}
v___jp_3457_:
{
lean_object* v___x_3460_; 
if (v_isShared_3449_ == 0)
{
v___x_3460_ = v___x_3448_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_e_x27_3444_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_proof_3445_);
v___x_3460_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
lean_object* v___x_3462_; 
lean_ctor_set_uint8(v___x_3460_, sizeof(void*)*2, v_done_3455_);
lean_ctor_set_uint8(v___x_3460_, sizeof(void*)*2 + 1, v___y_3458_);
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 0, v___x_3460_);
v___x_3462_ = v___x_3453_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3460_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
}
else
{
lean_object* v_e_x27_3465_; lean_object* v_proof_3466_; uint8_t v_done_3467_; uint8_t v_contextDependent_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3494_; 
lean_del_object(v___x_3453_);
lean_del_object(v___x_3448_);
v_e_x27_3465_ = lean_ctor_get(v_a_3451_, 0);
v_proof_3466_ = lean_ctor_get(v_a_3451_, 1);
v_done_3467_ = lean_ctor_get_uint8(v_a_3451_, sizeof(void*)*2);
v_contextDependent_3468_ = lean_ctor_get_uint8(v_a_3451_, sizeof(void*)*2 + 1);
v_isSharedCheck_3494_ = !lean_is_exclusive(v_a_3451_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3470_ = v_a_3451_;
v_isShared_3471_ = v_isSharedCheck_3494_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_proof_3466_);
lean_inc(v_e_x27_3465_);
lean_dec(v_a_3451_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3494_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3472_; 
lean_inc_ref(v_e_x27_3465_);
v___x_3472_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v_e_3407_, v_e_x27_3444_, v_proof_3445_, v_e_x27_3465_, v_proof_3466_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_);
if (lean_obj_tag(v___x_3472_) == 0)
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3485_; 
v_a_3473_ = lean_ctor_get(v___x_3472_, 0);
v_isSharedCheck_3485_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3475_ = v___x_3472_;
v_isShared_3476_ = v_isSharedCheck_3485_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3472_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3485_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
uint8_t v___y_3478_; 
if (v_contextDependent_3446_ == 0)
{
v___y_3478_ = v_contextDependent_3468_;
goto v___jp_3477_;
}
else
{
v___y_3478_ = v_contextDependent_3446_;
goto v___jp_3477_;
}
v___jp_3477_:
{
lean_object* v___x_3480_; 
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 1, v_a_3473_);
v___x_3480_ = v___x_3470_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3484_; 
v_reuseFailAlloc_3484_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_e_x27_3465_);
lean_ctor_set(v_reuseFailAlloc_3484_, 1, v_a_3473_);
lean_ctor_set_uint8(v_reuseFailAlloc_3484_, sizeof(void*)*2, v_done_3467_);
v___x_3480_ = v_reuseFailAlloc_3484_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
lean_object* v___x_3482_; 
lean_ctor_set_uint8(v___x_3480_, sizeof(void*)*2 + 1, v___y_3478_);
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 0, v___x_3480_);
v___x_3482_ = v___x_3475_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3480_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
}
else
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3493_; 
lean_del_object(v___x_3470_);
lean_dec_ref(v_e_x27_3465_);
v_a_3486_ = lean_ctor_get(v___x_3472_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3488_ = v___x_3472_;
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3472_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3491_; 
if (v_isShared_3489_ == 0)
{
v___x_3491_ = v___x_3488_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3486_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3448_);
lean_dec_ref(v_proof_3445_);
lean_dec_ref(v_e_x27_3444_);
lean_dec_ref_known(v_e_3407_, 2);
return v___x_3450_;
}
}
}
else
{
lean_dec_ref_known(v_a_3424_, 2);
lean_dec_ref_known(v_e_3407_, 2);
return v___x_3423_;
}
}
}
else
{
lean_dec_ref_known(v_e_3407_, 2);
return v___x_3423_;
}
}
case 5:
{
lean_object* v___x_3497_; 
lean_inc_ref(v_e_3407_);
v___x_3497_ = l_Lean_Meta_Tactic_Cbv_tryMatcher(v_e_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3498_);
if (lean_obj_tag(v_a_3498_) == 0)
{
uint8_t v_done_3499_; 
v_done_3499_ = lean_ctor_get_uint8(v_a_3498_, 0);
if (v_done_3499_ == 0)
{
uint8_t v_contextDependent_3500_; lean_object* v___x_3501_; 
lean_dec_ref_known(v___x_3497_, 1);
v_contextDependent_3500_ = lean_ctor_get_uint8(v_a_3498_, 1);
lean_dec_ref_known(v_a_3498_, 0);
v___x_3501_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(v_e_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_object* v_a_3502_; uint8_t v___y_3504_; 
v_a_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_a_3502_);
if (v_contextDependent_3500_ == 0)
{
lean_dec(v_a_3502_);
return v___x_3501_;
}
else
{
if (lean_obj_tag(v_a_3502_) == 0)
{
uint8_t v_contextDependent_3514_; 
v_contextDependent_3514_ = lean_ctor_get_uint8(v_a_3502_, 1);
v___y_3504_ = v_contextDependent_3514_;
goto v___jp_3503_;
}
else
{
uint8_t v_contextDependent_3515_; 
v_contextDependent_3515_ = lean_ctor_get_uint8(v_a_3502_, sizeof(void*)*2 + 1);
v___y_3504_ = v_contextDependent_3515_;
goto v___jp_3503_;
}
}
v___jp_3503_:
{
if (v___y_3504_ == 0)
{
lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3512_; 
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3501_);
if (v_isSharedCheck_3512_ == 0)
{
lean_object* v_unused_3513_; 
v_unused_3513_ = lean_ctor_get(v___x_3501_, 0);
lean_dec(v_unused_3513_);
v___x_3506_ = v___x_3501_;
v_isShared_3507_ = v_isSharedCheck_3512_;
goto v_resetjp_3505_;
}
else
{
lean_dec(v___x_3501_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3512_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3508_; lean_object* v___x_3510_; 
v___x_3508_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3502_);
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 0, v___x_3508_);
v___x_3510_ = v___x_3506_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v___x_3508_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
else
{
lean_dec(v_a_3502_);
return v___x_3501_;
}
}
}
else
{
return v___x_3501_;
}
}
else
{
lean_dec_ref_known(v_a_3498_, 0);
lean_dec_ref_known(v_e_3407_, 2);
return v___x_3497_;
}
}
else
{
lean_dec_ref_known(v_a_3498_, 2);
lean_dec_ref_known(v_e_3407_, 2);
return v___x_3497_;
}
}
else
{
lean_dec_ref_known(v_e_3407_, 2);
return v___x_3497_;
}
}
case 8:
{
uint8_t v___x_3516_; 
v___x_3516_ = l_Lean_Expr_letNondep_x21(v_e_3407_);
if (v___x_3516_ == 0)
{
lean_object* v___x_3517_; 
v___x_3517_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(v_e_3407_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_);
return v___x_3517_;
}
else
{
lean_object* v___x_3518_; 
v___x_3518_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_e_3407_, v_a_3411_, v_a_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_);
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3530_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3530_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3530_ == 0)
{
v___x_3521_ = v___x_3518_;
v_isShared_3522_ = v_isSharedCheck_3530_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3518_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3530_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v_e_3523_; lean_object* v_h_3524_; uint8_t v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3528_; 
v_e_3523_ = lean_ctor_get(v_a_3519_, 2);
lean_inc_ref(v_e_3523_);
v_h_3524_ = lean_ctor_get(v_a_3519_, 3);
lean_inc_ref(v_h_3524_);
lean_dec(v_a_3519_);
v___x_3525_ = 0;
v___x_3526_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3526_, 0, v_e_3523_);
lean_ctor_set(v___x_3526_, 1, v_h_3524_);
lean_ctor_set_uint8(v___x_3526_, sizeof(void*)*2, v___x_3525_);
lean_ctor_set_uint8(v___x_3526_, sizeof(void*)*2 + 1, v___x_3525_);
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 0, v___x_3526_);
v___x_3528_ = v___x_3521_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3529_; 
v_reuseFailAlloc_3529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3526_);
v___x_3528_ = v_reuseFailAlloc_3529_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
return v___x_3528_;
}
}
}
else
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
v_a_3531_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3533_ = v___x_3518_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3518_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3531_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
}
case 7:
{
lean_dec_ref_known(v_e_3407_, 3);
goto v___jp_3418_;
}
case 6:
{
lean_dec_ref_known(v_e_3407_, 3);
goto v___jp_3418_;
}
case 1:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; 
lean_dec_ref_known(v_e_3407_, 1);
v___x_3539_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3540_, 0, v___x_3539_);
return v___x_3540_;
}
case 2:
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
lean_dec_ref_known(v_e_3407_, 1);
v___x_3541_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3542_, 0, v___x_3541_);
return v___x_3542_;
}
case 0:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; 
lean_dec_ref_known(v_e_3407_, 1);
v___x_3543_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3543_);
return v___x_3544_;
}
case 3:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; 
lean_dec_ref_known(v_e_3407_, 1);
v___x_3545_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3546_, 0, v___x_3545_);
return v___x_3546_;
}
default: 
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
lean_dec_ref(v_e_3407_);
v___x_3547_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_3548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3548_, 0, v___x_3547_);
return v___x_3548_;
}
}
v___jp_3418_:
{
lean_object* v___x_3419_; lean_object* v___x_3420_; 
v___x_3419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3419_);
return v___x_3420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___boxed(lean_object* v_e_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_){
_start:
{
lean_object* v_res_3560_; 
v_res_3560_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(v_e_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_);
lean_dec(v_a_3558_);
lean_dec_ref(v_a_3557_);
lean_dec(v_a_3556_);
lean_dec_ref(v_a_3555_);
lean_dec(v_a_3554_);
lean_dec_ref(v_a_3553_);
lean_dec(v_a_3552_);
lean_dec_ref(v_a_3551_);
lean_dec(v_a_3550_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre(lean_object* v_simprocs_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_){
_start:
{
lean_object* v___y_3574_; lean_object* v___y_3575_; uint8_t v___y_3576_; lean_object* v___x_3579_; 
lean_inc_ref(v_a_3562_);
v___x_3579_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(v_a_3562_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_object* v_a_3580_; 
v_a_3580_ = lean_ctor_get(v___x_3579_, 0);
lean_inc(v_a_3580_);
if (lean_obj_tag(v_a_3580_) == 0)
{
uint8_t v_done_3581_; uint8_t v_contextDependent_3582_; lean_object* v___y_3584_; lean_object* v_a_3585_; lean_object* v___y_3589_; lean_object* v___y_3590_; uint8_t v___y_3591_; lean_object* v___y_3595_; 
v_done_3581_ = lean_ctor_get_uint8(v_a_3580_, 0);
v_contextDependent_3582_ = lean_ctor_get_uint8(v_a_3580_, 1);
lean_dec_ref_known(v_a_3580_, 0);
if (v_done_3581_ == 0)
{
lean_object* v___x_3597_; 
lean_dec_ref_known(v___x_3579_, 1);
lean_inc_ref(v_a_3562_);
v___x_3597_ = l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(v_a_3562_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
lean_inc(v_a_3598_);
if (lean_obj_tag(v_a_3598_) == 0)
{
uint8_t v_done_3599_; uint8_t v_contextDependent_3600_; lean_object* v___y_3602_; lean_object* v_a_3603_; lean_object* v___y_3607_; 
v_done_3599_ = lean_ctor_get_uint8(v_a_3598_, 0);
v_contextDependent_3600_ = lean_ctor_get_uint8(v_a_3598_, 1);
lean_dec_ref_known(v_a_3598_, 0);
if (v_done_3599_ == 0)
{
lean_object* v_pre_3609_; lean_object* v_erased_3610_; lean_object* v___x_3611_; 
lean_dec_ref_known(v___x_3597_, 1);
v_pre_3609_ = lean_ctor_get(v_simprocs_3561_, 0);
v_erased_3610_ = lean_ctor_get(v_simprocs_3561_, 4);
lean_inc_ref(v_a_3562_);
v___x_3611_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_pre_3609_, v_erased_3610_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v_a_3612_; 
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
lean_inc(v_a_3612_);
if (lean_obj_tag(v_a_3612_) == 0)
{
uint8_t v_done_3613_; 
v_done_3613_ = lean_ctor_get_uint8(v_a_3612_, 0);
if (v_done_3613_ == 0)
{
uint8_t v_contextDependent_3614_; lean_object* v___x_3615_; 
lean_dec_ref_known(v___x_3611_, 1);
v_contextDependent_3614_ = lean_ctor_get_uint8(v_a_3612_, 1);
lean_dec_ref_known(v_a_3612_, 0);
v___x_3615_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_a_3616_; uint8_t v___y_3618_; 
v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc(v_a_3616_);
if (v_contextDependent_3614_ == 0)
{
lean_dec(v_a_3616_);
v___y_3607_ = v___x_3615_;
goto v___jp_3606_;
}
else
{
if (lean_obj_tag(v_a_3616_) == 0)
{
uint8_t v_contextDependent_3628_; 
v_contextDependent_3628_ = lean_ctor_get_uint8(v_a_3616_, 1);
v___y_3618_ = v_contextDependent_3628_;
goto v___jp_3617_;
}
else
{
uint8_t v_contextDependent_3629_; 
v_contextDependent_3629_ = lean_ctor_get_uint8(v_a_3616_, sizeof(void*)*2 + 1);
v___y_3618_ = v_contextDependent_3629_;
goto v___jp_3617_;
}
}
v___jp_3617_:
{
if (v___y_3618_ == 0)
{
lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3626_; 
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3626_ == 0)
{
lean_object* v_unused_3627_; 
v_unused_3627_ = lean_ctor_get(v___x_3615_, 0);
lean_dec(v_unused_3627_);
v___x_3620_ = v___x_3615_;
v_isShared_3621_ = v_isSharedCheck_3626_;
goto v_resetjp_3619_;
}
else
{
lean_dec(v___x_3615_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3626_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3622_; lean_object* v___x_3624_; 
v___x_3622_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3616_);
lean_inc_ref(v___x_3622_);
if (v_isShared_3621_ == 0)
{
lean_ctor_set(v___x_3620_, 0, v___x_3622_);
v___x_3624_ = v___x_3620_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3622_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
v___y_3602_ = v___x_3624_;
v_a_3603_ = v___x_3622_;
goto v___jp_3601_;
}
}
}
else
{
lean_dec(v_a_3616_);
v___y_3607_ = v___x_3615_;
goto v___jp_3606_;
}
}
}
else
{
v___y_3607_ = v___x_3615_;
goto v___jp_3606_;
}
}
else
{
lean_dec_ref_known(v_a_3612_, 0);
lean_dec_ref(v_a_3562_);
v___y_3607_ = v___x_3611_;
goto v___jp_3606_;
}
}
else
{
lean_dec_ref_known(v_a_3612_, 2);
lean_dec_ref(v_a_3562_);
v___y_3607_ = v___x_3611_;
goto v___jp_3606_;
}
}
else
{
lean_dec_ref(v_a_3562_);
v___y_3607_ = v___x_3611_;
goto v___jp_3606_;
}
}
else
{
lean_dec_ref(v_a_3562_);
v___y_3595_ = v___x_3597_;
goto v___jp_3594_;
}
v___jp_3601_:
{
if (v_contextDependent_3600_ == 0)
{
v___y_3584_ = v___y_3602_;
v_a_3585_ = v_a_3603_;
goto v___jp_3583_;
}
else
{
if (lean_obj_tag(v_a_3603_) == 0)
{
uint8_t v_contextDependent_3604_; 
v_contextDependent_3604_ = lean_ctor_get_uint8(v_a_3603_, 1);
v___y_3589_ = v_a_3603_;
v___y_3590_ = v___y_3602_;
v___y_3591_ = v_contextDependent_3604_;
goto v___jp_3588_;
}
else
{
uint8_t v_contextDependent_3605_; 
v_contextDependent_3605_ = lean_ctor_get_uint8(v_a_3603_, sizeof(void*)*2 + 1);
v___y_3589_ = v_a_3603_;
v___y_3590_ = v___y_3602_;
v___y_3591_ = v_contextDependent_3605_;
goto v___jp_3588_;
}
}
}
v___jp_3606_:
{
if (lean_obj_tag(v___y_3607_) == 0)
{
lean_object* v_a_3608_; 
v_a_3608_ = lean_ctor_get(v___y_3607_, 0);
lean_inc(v_a_3608_);
v___y_3602_ = v___y_3607_;
v_a_3603_ = v_a_3608_;
goto v___jp_3601_;
}
else
{
return v___y_3607_;
}
}
}
else
{
lean_dec_ref_known(v_a_3598_, 2);
lean_dec_ref(v_a_3562_);
v___y_3595_ = v___x_3597_;
goto v___jp_3594_;
}
}
else
{
lean_dec_ref(v_a_3562_);
v___y_3595_ = v___x_3597_;
goto v___jp_3594_;
}
}
else
{
lean_dec_ref(v_a_3562_);
return v___x_3579_;
}
v___jp_3583_:
{
if (v_contextDependent_3582_ == 0)
{
lean_dec_ref(v_a_3585_);
return v___y_3584_;
}
else
{
if (lean_obj_tag(v_a_3585_) == 0)
{
uint8_t v_contextDependent_3586_; 
v_contextDependent_3586_ = lean_ctor_get_uint8(v_a_3585_, 1);
v___y_3574_ = v___y_3584_;
v___y_3575_ = v_a_3585_;
v___y_3576_ = v_contextDependent_3586_;
goto v___jp_3573_;
}
else
{
uint8_t v_contextDependent_3587_; 
v_contextDependent_3587_ = lean_ctor_get_uint8(v_a_3585_, sizeof(void*)*2 + 1);
v___y_3574_ = v___y_3584_;
v___y_3575_ = v_a_3585_;
v___y_3576_ = v_contextDependent_3587_;
goto v___jp_3573_;
}
}
}
v___jp_3588_:
{
if (v___y_3591_ == 0)
{
lean_object* v___x_3592_; lean_object* v___x_3593_; 
lean_dec_ref(v___y_3590_);
v___x_3592_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3589_);
lean_inc_ref(v___x_3592_);
v___x_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3592_);
v___y_3584_ = v___x_3593_;
v_a_3585_ = v___x_3592_;
goto v___jp_3583_;
}
else
{
v___y_3584_ = v___y_3590_;
v_a_3585_ = v___y_3589_;
goto v___jp_3583_;
}
}
v___jp_3594_:
{
if (lean_obj_tag(v___y_3595_) == 0)
{
lean_object* v_a_3596_; 
v_a_3596_ = lean_ctor_get(v___y_3595_, 0);
lean_inc(v_a_3596_);
v___y_3584_ = v___y_3595_;
v_a_3585_ = v_a_3596_;
goto v___jp_3583_;
}
else
{
return v___y_3595_;
}
}
}
else
{
lean_dec_ref_known(v_a_3580_, 2);
lean_dec_ref(v_a_3562_);
return v___x_3579_;
}
}
else
{
lean_dec_ref(v_a_3562_);
return v___x_3579_;
}
v___jp_3573_:
{
if (v___y_3576_ == 0)
{
lean_object* v___x_3577_; lean_object* v___x_3578_; 
lean_dec_ref(v___y_3574_);
v___x_3577_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3575_);
v___x_3578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
return v___x_3578_;
}
else
{
lean_dec_ref(v___y_3575_);
return v___y_3574_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre___boxed(lean_object* v_simprocs_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_){
_start:
{
lean_object* v_res_3642_; 
v_res_3642_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre(v_simprocs_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_);
lean_dec(v_a_3640_);
lean_dec_ref(v_a_3639_);
lean_dec(v_a_3638_);
lean_dec_ref(v_a_3637_);
lean_dec(v_a_3636_);
lean_dec_ref(v_a_3635_);
lean_dec(v_a_3634_);
lean_dec_ref(v_a_3633_);
lean_dec(v_a_3632_);
lean_dec_ref(v_simprocs_3630_);
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost(lean_object* v_simprocs_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_){
_start:
{
lean_object* v___y_3656_; lean_object* v___y_3657_; uint8_t v___y_3658_; lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3661_ = lean_unsigned_to_nat(255u);
lean_inc_ref(v_a_3644_);
v___x_3662_ = l_Lean_Meta_Sym_Simp_evalGround___redArg(v___x_3661_, v_a_3644_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v_a_3663_; 
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
lean_inc(v_a_3663_);
if (lean_obj_tag(v_a_3663_) == 0)
{
uint8_t v_done_3664_; uint8_t v_contextDependent_3665_; lean_object* v___y_3667_; lean_object* v_a_3668_; lean_object* v___y_3672_; lean_object* v___y_3673_; uint8_t v___y_3674_; lean_object* v___y_3678_; 
v_done_3664_ = lean_ctor_get_uint8(v_a_3663_, 0);
v_contextDependent_3665_ = lean_ctor_get_uint8(v_a_3663_, 1);
lean_dec_ref_known(v_a_3663_, 0);
if (v_done_3664_ == 0)
{
lean_object* v_eval_3680_; lean_object* v_post_3681_; lean_object* v_erased_3682_; lean_object* v___x_3683_; 
lean_dec_ref_known(v___x_3662_, 1);
v_eval_3680_ = lean_ctor_get(v_simprocs_3643_, 1);
v_post_3681_ = lean_ctor_get(v_simprocs_3643_, 2);
v_erased_3682_ = lean_ctor_get(v_simprocs_3643_, 4);
lean_inc_ref(v_a_3644_);
v___x_3683_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_eval_3680_, v_erased_3682_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v_a_3684_; 
v_a_3684_ = lean_ctor_get(v___x_3683_, 0);
lean_inc(v_a_3684_);
if (lean_obj_tag(v_a_3684_) == 0)
{
uint8_t v_done_3685_; uint8_t v_contextDependent_3686_; lean_object* v___y_3688_; lean_object* v_a_3689_; lean_object* v___y_3693_; 
v_done_3685_ = lean_ctor_get_uint8(v_a_3684_, 0);
v_contextDependent_3686_ = lean_ctor_get_uint8(v_a_3684_, 1);
lean_dec_ref_known(v_a_3684_, 0);
if (v_done_3685_ == 0)
{
lean_object* v___x_3695_; 
lean_dec_ref_known(v___x_3683_, 1);
lean_inc_ref(v_a_3644_);
v___x_3695_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp(v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
lean_inc(v_a_3696_);
if (lean_obj_tag(v_a_3696_) == 0)
{
uint8_t v_done_3697_; 
v_done_3697_ = lean_ctor_get_uint8(v_a_3696_, 0);
if (v_done_3697_ == 0)
{
uint8_t v_contextDependent_3698_; lean_object* v___x_3699_; 
lean_dec_ref_known(v___x_3695_, 1);
v_contextDependent_3698_ = lean_ctor_get_uint8(v_a_3696_, 1);
lean_dec_ref_known(v_a_3696_, 0);
v___x_3699_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_post_3681_, v_erased_3682_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_);
if (lean_obj_tag(v___x_3699_) == 0)
{
lean_object* v_a_3700_; uint8_t v___y_3702_; 
v_a_3700_ = lean_ctor_get(v___x_3699_, 0);
lean_inc(v_a_3700_);
if (v_contextDependent_3698_ == 0)
{
lean_dec(v_a_3700_);
v___y_3693_ = v___x_3699_;
goto v___jp_3692_;
}
else
{
if (lean_obj_tag(v_a_3700_) == 0)
{
uint8_t v_contextDependent_3712_; 
v_contextDependent_3712_ = lean_ctor_get_uint8(v_a_3700_, 1);
v___y_3702_ = v_contextDependent_3712_;
goto v___jp_3701_;
}
else
{
uint8_t v_contextDependent_3713_; 
v_contextDependent_3713_ = lean_ctor_get_uint8(v_a_3700_, sizeof(void*)*2 + 1);
v___y_3702_ = v_contextDependent_3713_;
goto v___jp_3701_;
}
}
v___jp_3701_:
{
if (v___y_3702_ == 0)
{
lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3710_; 
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3710_ == 0)
{
lean_object* v_unused_3711_; 
v_unused_3711_ = lean_ctor_get(v___x_3699_, 0);
lean_dec(v_unused_3711_);
v___x_3704_ = v___x_3699_;
v_isShared_3705_ = v_isSharedCheck_3710_;
goto v_resetjp_3703_;
}
else
{
lean_dec(v___x_3699_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3710_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3706_; lean_object* v___x_3708_; 
v___x_3706_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3700_);
lean_inc_ref(v___x_3706_);
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 0, v___x_3706_);
v___x_3708_ = v___x_3704_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3706_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
v___y_3688_ = v___x_3708_;
v_a_3689_ = v___x_3706_;
goto v___jp_3687_;
}
}
}
else
{
lean_dec(v_a_3700_);
v___y_3693_ = v___x_3699_;
goto v___jp_3692_;
}
}
}
else
{
v___y_3693_ = v___x_3699_;
goto v___jp_3692_;
}
}
else
{
lean_dec_ref_known(v_a_3696_, 0);
lean_dec_ref(v_a_3644_);
v___y_3693_ = v___x_3695_;
goto v___jp_3692_;
}
}
else
{
lean_dec_ref_known(v_a_3696_, 2);
lean_dec_ref(v_a_3644_);
v___y_3693_ = v___x_3695_;
goto v___jp_3692_;
}
}
else
{
lean_dec_ref(v_a_3644_);
v___y_3693_ = v___x_3695_;
goto v___jp_3692_;
}
}
else
{
lean_dec_ref(v_a_3644_);
v___y_3678_ = v___x_3683_;
goto v___jp_3677_;
}
v___jp_3687_:
{
if (v_contextDependent_3686_ == 0)
{
v___y_3667_ = v___y_3688_;
v_a_3668_ = v_a_3689_;
goto v___jp_3666_;
}
else
{
if (lean_obj_tag(v_a_3689_) == 0)
{
uint8_t v_contextDependent_3690_; 
v_contextDependent_3690_ = lean_ctor_get_uint8(v_a_3689_, 1);
v___y_3672_ = v_a_3689_;
v___y_3673_ = v___y_3688_;
v___y_3674_ = v_contextDependent_3690_;
goto v___jp_3671_;
}
else
{
uint8_t v_contextDependent_3691_; 
v_contextDependent_3691_ = lean_ctor_get_uint8(v_a_3689_, sizeof(void*)*2 + 1);
v___y_3672_ = v_a_3689_;
v___y_3673_ = v___y_3688_;
v___y_3674_ = v_contextDependent_3691_;
goto v___jp_3671_;
}
}
}
v___jp_3692_:
{
if (lean_obj_tag(v___y_3693_) == 0)
{
lean_object* v_a_3694_; 
v_a_3694_ = lean_ctor_get(v___y_3693_, 0);
lean_inc(v_a_3694_);
v___y_3688_ = v___y_3693_;
v_a_3689_ = v_a_3694_;
goto v___jp_3687_;
}
else
{
return v___y_3693_;
}
}
}
else
{
lean_dec_ref_known(v_a_3684_, 2);
lean_dec_ref(v_a_3644_);
v___y_3678_ = v___x_3683_;
goto v___jp_3677_;
}
}
else
{
lean_dec_ref(v_a_3644_);
v___y_3678_ = v___x_3683_;
goto v___jp_3677_;
}
}
else
{
lean_dec_ref(v_a_3644_);
return v___x_3662_;
}
v___jp_3666_:
{
if (v_contextDependent_3665_ == 0)
{
lean_dec_ref(v_a_3668_);
return v___y_3667_;
}
else
{
if (lean_obj_tag(v_a_3668_) == 0)
{
uint8_t v_contextDependent_3669_; 
v_contextDependent_3669_ = lean_ctor_get_uint8(v_a_3668_, 1);
v___y_3656_ = v___y_3667_;
v___y_3657_ = v_a_3668_;
v___y_3658_ = v_contextDependent_3669_;
goto v___jp_3655_;
}
else
{
uint8_t v_contextDependent_3670_; 
v_contextDependent_3670_ = lean_ctor_get_uint8(v_a_3668_, sizeof(void*)*2 + 1);
v___y_3656_ = v___y_3667_;
v___y_3657_ = v_a_3668_;
v___y_3658_ = v_contextDependent_3670_;
goto v___jp_3655_;
}
}
}
v___jp_3671_:
{
if (v___y_3674_ == 0)
{
lean_object* v___x_3675_; lean_object* v___x_3676_; 
lean_dec_ref(v___y_3673_);
v___x_3675_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3672_);
lean_inc_ref(v___x_3675_);
v___x_3676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3675_);
v___y_3667_ = v___x_3676_;
v_a_3668_ = v___x_3675_;
goto v___jp_3666_;
}
else
{
v___y_3667_ = v___y_3673_;
v_a_3668_ = v___y_3672_;
goto v___jp_3666_;
}
}
v___jp_3677_:
{
if (lean_obj_tag(v___y_3678_) == 0)
{
lean_object* v_a_3679_; 
v_a_3679_ = lean_ctor_get(v___y_3678_, 0);
lean_inc(v_a_3679_);
v___y_3667_ = v___y_3678_;
v_a_3668_ = v_a_3679_;
goto v___jp_3666_;
}
else
{
return v___y_3678_;
}
}
}
else
{
lean_dec_ref_known(v_a_3663_, 2);
lean_dec_ref(v_a_3644_);
return v___x_3662_;
}
}
else
{
lean_dec_ref(v_a_3644_);
return v___x_3662_;
}
v___jp_3655_:
{
if (v___y_3658_ == 0)
{
lean_object* v___x_3659_; lean_object* v___x_3660_; 
lean_dec_ref(v___y_3656_);
v___x_3659_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3657_);
v___x_3660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3659_);
return v___x_3660_;
}
else
{
lean_dec_ref(v___y_3657_);
return v___y_3656_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost___boxed(lean_object* v_simprocs_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_, lean_object* v_a_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_){
_start:
{
lean_object* v_res_3726_; 
v_res_3726_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost(v_simprocs_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_, v_a_3719_, v_a_3720_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_);
lean_dec(v_a_3724_);
lean_dec_ref(v_a_3723_);
lean_dec(v_a_3722_);
lean_dec_ref(v_a_3721_);
lean_dec(v_a_3720_);
lean_dec_ref(v_a_3719_);
lean_dec(v_a_3718_);
lean_dec_ref(v_a_3717_);
lean_dec(v_a_3716_);
lean_dec_ref(v_simprocs_3714_);
return v_res_3726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(lean_object* v_simprocs_3727_){
_start:
{
lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
lean_inc_ref(v_simprocs_3727_);
v___x_3728_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre___boxed), 12, 1);
lean_closure_set(v___x_3728_, 0, v_simprocs_3727_);
v___x_3729_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost___boxed), 12, 1);
lean_closure_set(v___x_3729_, 0, v_simprocs_3727_);
v___x_3730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3728_);
lean_ctor_set(v___x_3730_, 1, v___x_3729_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(lean_object* v_e_3731_, lean_object* v_config_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_){
_start:
{
lean_object* v___x_3740_; 
v___x_3740_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3738_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v_a_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; 
v_a_3741_ = lean_ctor_get(v___x_3740_, 0);
lean_inc(v_a_3741_);
lean_dec_ref_known(v___x_3740_, 1);
v___x_3742_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_3741_);
v___x_3743_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3743_, 0, v_e_3731_);
v___x_3744_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_3743_, v___x_3742_, v_config_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_);
return v___x_3744_;
}
else
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3752_; 
lean_dec_ref(v_config_3732_);
lean_dec_ref(v_e_3731_);
v_a_3745_ = lean_ctor_get(v___x_3740_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3747_ = v___x_3740_;
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3740_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3752_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3750_; 
if (v_isShared_3748_ == 0)
{
v___x_3750_ = v___x_3747_;
goto v_reusejp_3749_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3745_);
v___x_3750_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3749_;
}
v_reusejp_3749_:
{
return v___x_3750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___boxed(lean_object* v_e_3753_, lean_object* v_config_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_){
_start:
{
lean_object* v_res_3762_; 
v_res_3762_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_e_3753_, v_config_3754_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_);
lean_dec(v_a_3760_);
lean_dec_ref(v_a_3759_);
lean_dec(v_a_3758_);
lean_dec_ref(v_a_3757_);
lean_dec(v_a_3756_);
lean_dec_ref(v_a_3755_);
return v_res_3762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(lean_object* v___y_3763_){
_start:
{
lean_object* v___x_3765_; lean_object* v_traceState_3766_; lean_object* v_traces_3767_; lean_object* v___x_3768_; lean_object* v_traceState_3769_; lean_object* v_env_3770_; lean_object* v_nextMacroScope_3771_; lean_object* v_ngen_3772_; lean_object* v_auxDeclNGen_3773_; lean_object* v_cache_3774_; lean_object* v_messages_3775_; lean_object* v_infoState_3776_; lean_object* v_snapshotTasks_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3798_; 
v___x_3765_ = lean_st_ref_get(v___y_3763_);
v_traceState_3766_ = lean_ctor_get(v___x_3765_, 4);
lean_inc_ref(v_traceState_3766_);
lean_dec(v___x_3765_);
v_traces_3767_ = lean_ctor_get(v_traceState_3766_, 0);
lean_inc_ref(v_traces_3767_);
lean_dec_ref(v_traceState_3766_);
v___x_3768_ = lean_st_ref_take(v___y_3763_);
v_traceState_3769_ = lean_ctor_get(v___x_3768_, 4);
v_env_3770_ = lean_ctor_get(v___x_3768_, 0);
v_nextMacroScope_3771_ = lean_ctor_get(v___x_3768_, 1);
v_ngen_3772_ = lean_ctor_get(v___x_3768_, 2);
v_auxDeclNGen_3773_ = lean_ctor_get(v___x_3768_, 3);
v_cache_3774_ = lean_ctor_get(v___x_3768_, 5);
v_messages_3775_ = lean_ctor_get(v___x_3768_, 6);
v_infoState_3776_ = lean_ctor_get(v___x_3768_, 7);
v_snapshotTasks_3777_ = lean_ctor_get(v___x_3768_, 8);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3779_ = v___x_3768_;
v_isShared_3780_ = v_isSharedCheck_3798_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_snapshotTasks_3777_);
lean_inc(v_infoState_3776_);
lean_inc(v_messages_3775_);
lean_inc(v_cache_3774_);
lean_inc(v_traceState_3769_);
lean_inc(v_auxDeclNGen_3773_);
lean_inc(v_ngen_3772_);
lean_inc(v_nextMacroScope_3771_);
lean_inc(v_env_3770_);
lean_dec(v___x_3768_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3798_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
uint64_t v_tid_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3796_; 
v_tid_3781_ = lean_ctor_get_uint64(v_traceState_3769_, sizeof(void*)*1);
v_isSharedCheck_3796_ = !lean_is_exclusive(v_traceState_3769_);
if (v_isSharedCheck_3796_ == 0)
{
lean_object* v_unused_3797_; 
v_unused_3797_ = lean_ctor_get(v_traceState_3769_, 0);
lean_dec(v_unused_3797_);
v___x_3783_ = v_traceState_3769_;
v_isShared_3784_ = v_isSharedCheck_3796_;
goto v_resetjp_3782_;
}
else
{
lean_dec(v_traceState_3769_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3796_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3789_; 
v___x_3785_ = lean_unsigned_to_nat(32u);
v___x_3786_ = lean_mk_empty_array_with_capacity(v___x_3785_);
lean_dec_ref(v___x_3786_);
v___x_3787_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1);
if (v_isShared_3784_ == 0)
{
lean_ctor_set(v___x_3783_, 0, v___x_3787_);
v___x_3789_ = v___x_3783_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3795_; 
v_reuseFailAlloc_3795_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3795_, 0, v___x_3787_);
lean_ctor_set_uint64(v_reuseFailAlloc_3795_, sizeof(void*)*1, v_tid_3781_);
v___x_3789_ = v_reuseFailAlloc_3795_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
lean_object* v___x_3791_; 
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 4, v___x_3789_);
v___x_3791_ = v___x_3779_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_env_3770_);
lean_ctor_set(v_reuseFailAlloc_3794_, 1, v_nextMacroScope_3771_);
lean_ctor_set(v_reuseFailAlloc_3794_, 2, v_ngen_3772_);
lean_ctor_set(v_reuseFailAlloc_3794_, 3, v_auxDeclNGen_3773_);
lean_ctor_set(v_reuseFailAlloc_3794_, 4, v___x_3789_);
lean_ctor_set(v_reuseFailAlloc_3794_, 5, v_cache_3774_);
lean_ctor_set(v_reuseFailAlloc_3794_, 6, v_messages_3775_);
lean_ctor_set(v_reuseFailAlloc_3794_, 7, v_infoState_3776_);
lean_ctor_set(v_reuseFailAlloc_3794_, 8, v_snapshotTasks_3777_);
v___x_3791_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; 
v___x_3792_ = lean_st_ref_set(v___y_3763_, v___x_3791_);
v___x_3793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3793_, 0, v_traces_3767_);
return v___x_3793_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg___boxed(lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v___y_3799_);
lean_dec(v___y_3799_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0(lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
lean_object* v___x_3807_; 
v___x_3807_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v___y_3805_);
return v___x_3807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___boxed(lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
lean_object* v_res_3813_; 
v_res_3813_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0(v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
lean_dec(v___y_3811_);
lean_dec_ref(v___y_3810_);
lean_dec(v___y_3809_);
lean_dec_ref(v___y_3808_);
return v_res_3813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0(lean_object* v_a_3814_, lean_object* v___x_3815_, lean_object* v___x_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
lean_object* v___x_3824_; 
v___x_3824_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_3814_, v___y_3818_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
lean_inc(v_a_3825_);
lean_dec_ref_known(v___x_3824_, 1);
v___x_3826_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3826_, 0, v_a_3825_);
v___x_3827_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_3826_, v___x_3815_, v___x_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_, v___y_3822_);
return v___x_3827_;
}
else
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
lean_dec_ref(v___x_3816_);
lean_dec_ref(v___x_3815_);
v_a_3828_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___x_3824_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3824_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed(lean_object* v_a_3836_, lean_object* v___x_3837_, lean_object* v___x_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_){
_start:
{
lean_object* v_res_3846_; 
v_res_3846_ = l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0(v_a_3836_, v___x_3837_, v___x_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec(v___y_3840_);
lean_dec_ref(v___y_3839_);
return v_res_3846_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3848_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__0));
v___x_3849_ = l_Lean_stringToMessageData(v___x_3848_);
return v___x_3849_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3851_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__2));
v___x_3852_ = l_Lean_stringToMessageData(v___x_3851_);
return v___x_3852_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3854_; lean_object* v___x_3855_; 
v___x_3854_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__4));
v___x_3855_ = l_Lean_stringToMessageData(v___x_3854_);
return v___x_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1(lean_object* v_e_3856_, lean_object* v_x_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_){
_start:
{
if (lean_obj_tag(v_x_3857_) == 0)
{
lean_object* v_a_3863_; lean_object* v___x_3865_; uint8_t v_isShared_3866_; uint8_t v_isSharedCheck_3873_; 
lean_dec_ref(v_e_3856_);
v_a_3863_ = lean_ctor_get(v_x_3857_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v_x_3857_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3865_ = v_x_3857_;
v_isShared_3866_ = v_isSharedCheck_3873_;
goto v_resetjp_3864_;
}
else
{
lean_inc(v_a_3863_);
lean_dec(v_x_3857_);
v___x_3865_ = lean_box(0);
v_isShared_3866_ = v_isSharedCheck_3873_;
goto v_resetjp_3864_;
}
v_resetjp_3864_:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3871_; 
v___x_3867_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1);
v___x_3868_ = l_Lean_Exception_toMessageData(v_a_3863_);
v___x_3869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3869_, 0, v___x_3867_);
lean_ctor_set(v___x_3869_, 1, v___x_3868_);
if (v_isShared_3866_ == 0)
{
lean_ctor_set(v___x_3865_, 0, v___x_3869_);
v___x_3871_ = v___x_3865_;
goto v_reusejp_3870_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3869_);
v___x_3871_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3870_;
}
v_reusejp_3870_:
{
return v___x_3871_;
}
}
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3876_; uint8_t v_isShared_3877_; uint8_t v_isSharedCheck_3895_; 
v_a_3874_ = lean_ctor_get(v_x_3857_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v_x_3857_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3876_ = v_x_3857_;
v_isShared_3877_ = v_isSharedCheck_3895_;
goto v_resetjp_3875_;
}
else
{
lean_inc(v_a_3874_);
lean_dec(v_x_3857_);
v___x_3876_ = lean_box(0);
v_isShared_3877_ = v_isSharedCheck_3895_;
goto v_resetjp_3875_;
}
v_resetjp_3875_:
{
if (lean_obj_tag(v_a_3874_) == 0)
{
lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3882_; 
lean_dec_ref_known(v_a_3874_, 0);
v___x_3878_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3);
v___x_3879_ = l_Lean_indentExpr(v_e_3856_);
v___x_3880_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3878_);
lean_ctor_set(v___x_3880_, 1, v___x_3879_);
if (v_isShared_3877_ == 0)
{
lean_ctor_set_tag(v___x_3876_, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3880_);
v___x_3882_ = v___x_3876_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v___x_3880_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
else
{
lean_object* v_e_x27_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3893_; 
v_e_x27_3884_ = lean_ctor_get(v_a_3874_, 0);
lean_inc_ref(v_e_x27_3884_);
lean_dec_ref_known(v_a_3874_, 2);
v___x_3885_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5);
v___x_3886_ = l_Lean_indentExpr(v_e_3856_);
v___x_3887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3885_);
lean_ctor_set(v___x_3887_, 1, v___x_3886_);
v___x_3888_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_3889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3887_);
lean_ctor_set(v___x_3889_, 1, v___x_3888_);
v___x_3890_ = l_Lean_indentExpr(v_e_x27_3884_);
v___x_3891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3889_);
lean_ctor_set(v___x_3891_, 1, v___x_3890_);
if (v_isShared_3877_ == 0)
{
lean_ctor_set_tag(v___x_3876_, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3891_);
v___x_3893_ = v___x_3876_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v___x_3891_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___boxed(lean_object* v_e_3896_, lean_object* v_x_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_){
_start:
{
lean_object* v_res_3903_; 
v_res_3903_ = l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1(v_e_3896_, v_x_3897_, v___y_3898_, v___y_3899_, v___y_3900_, v___y_3901_);
lean_dec(v___y_3901_);
lean_dec_ref(v___y_3900_);
lean_dec(v___y_3899_);
lean_dec_ref(v___y_3898_);
return v_res_3903_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(lean_object* v_x_3904_){
_start:
{
if (lean_obj_tag(v_x_3904_) == 0)
{
lean_object* v_a_3906_; lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3913_; 
v_a_3906_ = lean_ctor_get(v_x_3904_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v_x_3904_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3908_ = v_x_3904_;
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
else
{
lean_inc(v_a_3906_);
lean_dec(v_x_3904_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3913_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3911_; 
if (v_isShared_3909_ == 0)
{
lean_ctor_set_tag(v___x_3908_, 1);
v___x_3911_ = v___x_3908_;
goto v_reusejp_3910_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v_a_3906_);
v___x_3911_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3910_;
}
v_reusejp_3910_:
{
return v___x_3911_;
}
}
}
else
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3921_; 
v_a_3914_ = lean_ctor_get(v_x_3904_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v_x_3904_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3916_ = v_x_3904_;
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v_x_3904_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
v_resetjp_3915_:
{
lean_object* v___x_3919_; 
if (v_isShared_3917_ == 0)
{
lean_ctor_set_tag(v___x_3916_, 0);
v___x_3919_ = v___x_3916_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg___boxed(lean_object* v_x_3922_, lean_object* v___y_3923_){
_start:
{
lean_object* v_res_3924_; 
v_res_3924_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_x_3922_);
return v_res_3924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(lean_object* v_oldTraces_3925_, lean_object* v_data_3926_, lean_object* v_ref_3927_, lean_object* v_msg_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_){
_start:
{
lean_object* v_fileName_3934_; lean_object* v_fileMap_3935_; lean_object* v_options_3936_; lean_object* v_currRecDepth_3937_; lean_object* v_maxRecDepth_3938_; lean_object* v_ref_3939_; lean_object* v_currNamespace_3940_; lean_object* v_openDecls_3941_; lean_object* v_initHeartbeats_3942_; lean_object* v_maxHeartbeats_3943_; lean_object* v_quotContext_3944_; lean_object* v_currMacroScope_3945_; uint8_t v_diag_3946_; lean_object* v_cancelTk_x3f_3947_; uint8_t v_suppressElabErrors_3948_; lean_object* v_inheritedTraceOptions_3949_; lean_object* v___x_3950_; lean_object* v_traceState_3951_; lean_object* v_traces_3952_; lean_object* v_ref_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; size_t v_sz_3956_; size_t v___x_3957_; lean_object* v___x_3958_; lean_object* v_msg_3959_; lean_object* v___x_3960_; lean_object* v_a_3961_; lean_object* v___x_3963_; uint8_t v_isShared_3964_; uint8_t v_isSharedCheck_3998_; 
v_fileName_3934_ = lean_ctor_get(v___y_3931_, 0);
v_fileMap_3935_ = lean_ctor_get(v___y_3931_, 1);
v_options_3936_ = lean_ctor_get(v___y_3931_, 2);
v_currRecDepth_3937_ = lean_ctor_get(v___y_3931_, 3);
v_maxRecDepth_3938_ = lean_ctor_get(v___y_3931_, 4);
v_ref_3939_ = lean_ctor_get(v___y_3931_, 5);
v_currNamespace_3940_ = lean_ctor_get(v___y_3931_, 6);
v_openDecls_3941_ = lean_ctor_get(v___y_3931_, 7);
v_initHeartbeats_3942_ = lean_ctor_get(v___y_3931_, 8);
v_maxHeartbeats_3943_ = lean_ctor_get(v___y_3931_, 9);
v_quotContext_3944_ = lean_ctor_get(v___y_3931_, 10);
v_currMacroScope_3945_ = lean_ctor_get(v___y_3931_, 11);
v_diag_3946_ = lean_ctor_get_uint8(v___y_3931_, sizeof(void*)*14);
v_cancelTk_x3f_3947_ = lean_ctor_get(v___y_3931_, 12);
v_suppressElabErrors_3948_ = lean_ctor_get_uint8(v___y_3931_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3949_ = lean_ctor_get(v___y_3931_, 13);
v___x_3950_ = lean_st_ref_get(v___y_3932_);
v_traceState_3951_ = lean_ctor_get(v___x_3950_, 4);
lean_inc_ref(v_traceState_3951_);
lean_dec(v___x_3950_);
v_traces_3952_ = lean_ctor_get(v_traceState_3951_, 0);
lean_inc_ref(v_traces_3952_);
lean_dec_ref(v_traceState_3951_);
v_ref_3953_ = l_Lean_replaceRef(v_ref_3927_, v_ref_3939_);
lean_inc_ref(v_inheritedTraceOptions_3949_);
lean_inc(v_cancelTk_x3f_3947_);
lean_inc(v_currMacroScope_3945_);
lean_inc(v_quotContext_3944_);
lean_inc(v_maxHeartbeats_3943_);
lean_inc(v_initHeartbeats_3942_);
lean_inc(v_openDecls_3941_);
lean_inc(v_currNamespace_3940_);
lean_inc(v_maxRecDepth_3938_);
lean_inc(v_currRecDepth_3937_);
lean_inc_ref(v_options_3936_);
lean_inc_ref(v_fileMap_3935_);
lean_inc_ref(v_fileName_3934_);
v___x_3954_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3954_, 0, v_fileName_3934_);
lean_ctor_set(v___x_3954_, 1, v_fileMap_3935_);
lean_ctor_set(v___x_3954_, 2, v_options_3936_);
lean_ctor_set(v___x_3954_, 3, v_currRecDepth_3937_);
lean_ctor_set(v___x_3954_, 4, v_maxRecDepth_3938_);
lean_ctor_set(v___x_3954_, 5, v_ref_3953_);
lean_ctor_set(v___x_3954_, 6, v_currNamespace_3940_);
lean_ctor_set(v___x_3954_, 7, v_openDecls_3941_);
lean_ctor_set(v___x_3954_, 8, v_initHeartbeats_3942_);
lean_ctor_set(v___x_3954_, 9, v_maxHeartbeats_3943_);
lean_ctor_set(v___x_3954_, 10, v_quotContext_3944_);
lean_ctor_set(v___x_3954_, 11, v_currMacroScope_3945_);
lean_ctor_set(v___x_3954_, 12, v_cancelTk_x3f_3947_);
lean_ctor_set(v___x_3954_, 13, v_inheritedTraceOptions_3949_);
lean_ctor_set_uint8(v___x_3954_, sizeof(void*)*14, v_diag_3946_);
lean_ctor_set_uint8(v___x_3954_, sizeof(void*)*14 + 1, v_suppressElabErrors_3948_);
v___x_3955_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3952_);
lean_dec_ref(v_traces_3952_);
v_sz_3956_ = lean_array_size(v___x_3955_);
v___x_3957_ = ((size_t)0ULL);
v___x_3958_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5(v_sz_3956_, v___x_3957_, v___x_3955_);
v_msg_3959_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3959_, 0, v_data_3926_);
lean_ctor_set(v_msg_3959_, 1, v_msg_3928_);
lean_ctor_set(v_msg_3959_, 2, v___x_3958_);
v___x_3960_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_3959_, v___y_3929_, v___y_3930_, v___x_3954_, v___y_3932_);
lean_dec_ref_known(v___x_3954_, 14);
v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3963_ = v___x_3960_;
v_isShared_3964_ = v_isSharedCheck_3998_;
goto v_resetjp_3962_;
}
else
{
lean_inc(v_a_3961_);
lean_dec(v___x_3960_);
v___x_3963_ = lean_box(0);
v_isShared_3964_ = v_isSharedCheck_3998_;
goto v_resetjp_3962_;
}
v_resetjp_3962_:
{
lean_object* v___x_3965_; lean_object* v_traceState_3966_; lean_object* v_env_3967_; lean_object* v_nextMacroScope_3968_; lean_object* v_ngen_3969_; lean_object* v_auxDeclNGen_3970_; lean_object* v_cache_3971_; lean_object* v_messages_3972_; lean_object* v_infoState_3973_; lean_object* v_snapshotTasks_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3997_; 
v___x_3965_ = lean_st_ref_take(v___y_3932_);
v_traceState_3966_ = lean_ctor_get(v___x_3965_, 4);
v_env_3967_ = lean_ctor_get(v___x_3965_, 0);
v_nextMacroScope_3968_ = lean_ctor_get(v___x_3965_, 1);
v_ngen_3969_ = lean_ctor_get(v___x_3965_, 2);
v_auxDeclNGen_3970_ = lean_ctor_get(v___x_3965_, 3);
v_cache_3971_ = lean_ctor_get(v___x_3965_, 5);
v_messages_3972_ = lean_ctor_get(v___x_3965_, 6);
v_infoState_3973_ = lean_ctor_get(v___x_3965_, 7);
v_snapshotTasks_3974_ = lean_ctor_get(v___x_3965_, 8);
v_isSharedCheck_3997_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_3997_ == 0)
{
v___x_3976_ = v___x_3965_;
v_isShared_3977_ = v_isSharedCheck_3997_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_snapshotTasks_3974_);
lean_inc(v_infoState_3973_);
lean_inc(v_messages_3972_);
lean_inc(v_cache_3971_);
lean_inc(v_traceState_3966_);
lean_inc(v_auxDeclNGen_3970_);
lean_inc(v_ngen_3969_);
lean_inc(v_nextMacroScope_3968_);
lean_inc(v_env_3967_);
lean_dec(v___x_3965_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3997_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
uint64_t v_tid_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3995_; 
v_tid_3978_ = lean_ctor_get_uint64(v_traceState_3966_, sizeof(void*)*1);
v_isSharedCheck_3995_ = !lean_is_exclusive(v_traceState_3966_);
if (v_isSharedCheck_3995_ == 0)
{
lean_object* v_unused_3996_; 
v_unused_3996_ = lean_ctor_get(v_traceState_3966_, 0);
lean_dec(v_unused_3996_);
v___x_3980_ = v_traceState_3966_;
v_isShared_3981_ = v_isSharedCheck_3995_;
goto v_resetjp_3979_;
}
else
{
lean_dec(v_traceState_3966_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_3995_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3985_; 
v___x_3982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3982_, 0, v_ref_3927_);
lean_ctor_set(v___x_3982_, 1, v_a_3961_);
v___x_3983_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3925_, v___x_3982_);
if (v_isShared_3981_ == 0)
{
lean_ctor_set(v___x_3980_, 0, v___x_3983_);
v___x_3985_ = v___x_3980_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v___x_3983_);
lean_ctor_set_uint64(v_reuseFailAlloc_3994_, sizeof(void*)*1, v_tid_3978_);
v___x_3985_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
lean_object* v___x_3987_; 
if (v_isShared_3977_ == 0)
{
lean_ctor_set(v___x_3976_, 4, v___x_3985_);
v___x_3987_ = v___x_3976_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_env_3967_);
lean_ctor_set(v_reuseFailAlloc_3993_, 1, v_nextMacroScope_3968_);
lean_ctor_set(v_reuseFailAlloc_3993_, 2, v_ngen_3969_);
lean_ctor_set(v_reuseFailAlloc_3993_, 3, v_auxDeclNGen_3970_);
lean_ctor_set(v_reuseFailAlloc_3993_, 4, v___x_3985_);
lean_ctor_set(v_reuseFailAlloc_3993_, 5, v_cache_3971_);
lean_ctor_set(v_reuseFailAlloc_3993_, 6, v_messages_3972_);
lean_ctor_set(v_reuseFailAlloc_3993_, 7, v_infoState_3973_);
lean_ctor_set(v_reuseFailAlloc_3993_, 8, v_snapshotTasks_3974_);
v___x_3987_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3991_; 
v___x_3988_ = lean_st_ref_set(v___y_3932_, v___x_3987_);
v___x_3989_ = lean_box(0);
if (v_isShared_3964_ == 0)
{
lean_ctor_set(v___x_3963_, 0, v___x_3989_);
v___x_3991_ = v___x_3963_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v___x_3989_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1___boxed(lean_object* v_oldTraces_3999_, lean_object* v_data_4000_, lean_object* v_ref_4001_, lean_object* v_msg_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_){
_start:
{
lean_object* v_res_4008_; 
v_res_4008_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(v_oldTraces_3999_, v_data_4000_, v_ref_4001_, v_msg_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
lean_dec(v___y_4004_);
lean_dec_ref(v___y_4003_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(lean_object* v_cls_4009_, uint8_t v_collapsed_4010_, lean_object* v_tag_4011_, lean_object* v_opts_4012_, uint8_t v_clsEnabled_4013_, lean_object* v_oldTraces_4014_, lean_object* v_msg_4015_, lean_object* v_resStartStop_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v_fst_4022_; lean_object* v_snd_4023_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v_data_4027_; lean_object* v_fst_4038_; lean_object* v_snd_4039_; lean_object* v___x_4040_; uint8_t v___x_4041_; lean_object* v___y_4043_; lean_object* v_a_4044_; uint8_t v___y_4059_; double v___y_4090_; 
v_fst_4022_ = lean_ctor_get(v_resStartStop_4016_, 0);
lean_inc(v_fst_4022_);
v_snd_4023_ = lean_ctor_get(v_resStartStop_4016_, 1);
lean_inc(v_snd_4023_);
lean_dec_ref(v_resStartStop_4016_);
v_fst_4038_ = lean_ctor_get(v_snd_4023_, 0);
lean_inc(v_fst_4038_);
v_snd_4039_ = lean_ctor_get(v_snd_4023_, 1);
lean_inc(v_snd_4039_);
lean_dec(v_snd_4023_);
v___x_4040_ = l_Lean_trace_profiler;
v___x_4041_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4012_, v___x_4040_);
if (v___x_4041_ == 0)
{
v___y_4059_ = v___x_4041_;
goto v___jp_4058_;
}
else
{
lean_object* v___x_4095_; uint8_t v___x_4096_; 
v___x_4095_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4096_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4012_, v___x_4095_);
if (v___x_4096_ == 0)
{
lean_object* v___x_4097_; lean_object* v___x_4098_; double v___x_4099_; double v___x_4100_; double v___x_4101_; 
v___x_4097_ = l_Lean_trace_profiler_threshold;
v___x_4098_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4012_, v___x_4097_);
v___x_4099_ = lean_float_of_nat(v___x_4098_);
v___x_4100_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2);
v___x_4101_ = lean_float_div(v___x_4099_, v___x_4100_);
v___y_4090_ = v___x_4101_;
goto v___jp_4089_;
}
else
{
lean_object* v___x_4102_; lean_object* v___x_4103_; double v___x_4104_; 
v___x_4102_ = l_Lean_trace_profiler_threshold;
v___x_4103_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4012_, v___x_4102_);
v___x_4104_ = lean_float_of_nat(v___x_4103_);
v___y_4090_ = v___x_4104_;
goto v___jp_4089_;
}
}
v___jp_4024_:
{
lean_object* v___x_4028_; 
lean_inc(v___y_4026_);
v___x_4028_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(v_oldTraces_4014_, v_data_4027_, v___y_4026_, v___y_4025_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v___x_4029_; 
lean_dec_ref_known(v___x_4028_, 1);
v___x_4029_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_4022_);
return v___x_4029_;
}
else
{
lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4037_; 
lean_dec(v_fst_4022_);
v_a_4030_ = lean_ctor_get(v___x_4028_, 0);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4032_ = v___x_4028_;
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v___x_4028_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4037_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
lean_object* v___x_4035_; 
if (v_isShared_4033_ == 0)
{
v___x_4035_ = v___x_4032_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v_a_4030_);
v___x_4035_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
return v___x_4035_;
}
}
}
}
v___jp_4042_:
{
uint8_t v_result_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; double v___x_4048_; lean_object* v_data_4049_; 
v_result_4045_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(v_fst_4022_);
v___x_4046_ = lean_box(v_result_4045_);
v___x_4047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4046_);
v___x_4048_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_4011_);
lean_inc_ref(v___x_4047_);
lean_inc(v_cls_4009_);
v_data_4049_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4049_, 0, v_cls_4009_);
lean_ctor_set(v_data_4049_, 1, v___x_4047_);
lean_ctor_set(v_data_4049_, 2, v_tag_4011_);
lean_ctor_set_float(v_data_4049_, sizeof(void*)*3, v___x_4048_);
lean_ctor_set_float(v_data_4049_, sizeof(void*)*3 + 8, v___x_4048_);
lean_ctor_set_uint8(v_data_4049_, sizeof(void*)*3 + 16, v_collapsed_4010_);
if (v___x_4041_ == 0)
{
lean_dec_ref_known(v___x_4047_, 1);
lean_dec(v_snd_4039_);
lean_dec(v_fst_4038_);
lean_dec_ref(v_tag_4011_);
lean_dec(v_cls_4009_);
v___y_4025_ = v_a_4044_;
v___y_4026_ = v___y_4043_;
v_data_4027_ = v_data_4049_;
goto v___jp_4024_;
}
else
{
lean_object* v_data_4050_; double v___x_4051_; double v___x_4052_; 
lean_dec_ref_known(v_data_4049_, 3);
v_data_4050_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4050_, 0, v_cls_4009_);
lean_ctor_set(v_data_4050_, 1, v___x_4047_);
lean_ctor_set(v_data_4050_, 2, v_tag_4011_);
v___x_4051_ = lean_unbox_float(v_fst_4038_);
lean_dec(v_fst_4038_);
lean_ctor_set_float(v_data_4050_, sizeof(void*)*3, v___x_4051_);
v___x_4052_ = lean_unbox_float(v_snd_4039_);
lean_dec(v_snd_4039_);
lean_ctor_set_float(v_data_4050_, sizeof(void*)*3 + 8, v___x_4052_);
lean_ctor_set_uint8(v_data_4050_, sizeof(void*)*3 + 16, v_collapsed_4010_);
v___y_4025_ = v_a_4044_;
v___y_4026_ = v___y_4043_;
v_data_4027_ = v_data_4050_;
goto v___jp_4024_;
}
}
v___jp_4053_:
{
lean_object* v_ref_4054_; lean_object* v___x_4055_; 
v_ref_4054_ = lean_ctor_get(v___y_4019_, 5);
lean_inc(v___y_4020_);
lean_inc_ref(v___y_4019_);
lean_inc(v___y_4018_);
lean_inc_ref(v___y_4017_);
lean_inc(v_fst_4022_);
v___x_4055_ = lean_apply_6(v_msg_4015_, v_fst_4022_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, lean_box(0));
if (lean_obj_tag(v___x_4055_) == 0)
{
lean_object* v_a_4056_; 
v_a_4056_ = lean_ctor_get(v___x_4055_, 0);
lean_inc(v_a_4056_);
lean_dec_ref_known(v___x_4055_, 1);
v___y_4043_ = v_ref_4054_;
v_a_4044_ = v_a_4056_;
goto v___jp_4042_;
}
else
{
lean_object* v___x_4057_; 
lean_dec_ref_known(v___x_4055_, 1);
v___x_4057_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
v___y_4043_ = v_ref_4054_;
v_a_4044_ = v___x_4057_;
goto v___jp_4042_;
}
}
v___jp_4058_:
{
if (v_clsEnabled_4013_ == 0)
{
if (v___y_4059_ == 0)
{
lean_object* v___x_4060_; lean_object* v_traceState_4061_; lean_object* v_env_4062_; lean_object* v_nextMacroScope_4063_; lean_object* v_ngen_4064_; lean_object* v_auxDeclNGen_4065_; lean_object* v_cache_4066_; lean_object* v_messages_4067_; lean_object* v_infoState_4068_; lean_object* v_snapshotTasks_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4088_; 
lean_dec(v_snd_4039_);
lean_dec(v_fst_4038_);
lean_dec_ref(v_msg_4015_);
lean_dec_ref(v_tag_4011_);
lean_dec(v_cls_4009_);
v___x_4060_ = lean_st_ref_take(v___y_4020_);
v_traceState_4061_ = lean_ctor_get(v___x_4060_, 4);
v_env_4062_ = lean_ctor_get(v___x_4060_, 0);
v_nextMacroScope_4063_ = lean_ctor_get(v___x_4060_, 1);
v_ngen_4064_ = lean_ctor_get(v___x_4060_, 2);
v_auxDeclNGen_4065_ = lean_ctor_get(v___x_4060_, 3);
v_cache_4066_ = lean_ctor_get(v___x_4060_, 5);
v_messages_4067_ = lean_ctor_get(v___x_4060_, 6);
v_infoState_4068_ = lean_ctor_get(v___x_4060_, 7);
v_snapshotTasks_4069_ = lean_ctor_get(v___x_4060_, 8);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4071_ = v___x_4060_;
v_isShared_4072_ = v_isSharedCheck_4088_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_snapshotTasks_4069_);
lean_inc(v_infoState_4068_);
lean_inc(v_messages_4067_);
lean_inc(v_cache_4066_);
lean_inc(v_traceState_4061_);
lean_inc(v_auxDeclNGen_4065_);
lean_inc(v_ngen_4064_);
lean_inc(v_nextMacroScope_4063_);
lean_inc(v_env_4062_);
lean_dec(v___x_4060_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4088_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
uint64_t v_tid_4073_; lean_object* v_traces_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4087_; 
v_tid_4073_ = lean_ctor_get_uint64(v_traceState_4061_, sizeof(void*)*1);
v_traces_4074_ = lean_ctor_get(v_traceState_4061_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v_traceState_4061_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4076_ = v_traceState_4061_;
v_isShared_4077_ = v_isSharedCheck_4087_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_traces_4074_);
lean_dec(v_traceState_4061_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4087_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v___x_4078_; lean_object* v___x_4080_; 
v___x_4078_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4014_, v_traces_4074_);
lean_dec_ref(v_traces_4074_);
if (v_isShared_4077_ == 0)
{
lean_ctor_set(v___x_4076_, 0, v___x_4078_);
v___x_4080_ = v___x_4076_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v___x_4078_);
lean_ctor_set_uint64(v_reuseFailAlloc_4086_, sizeof(void*)*1, v_tid_4073_);
v___x_4080_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
lean_object* v___x_4082_; 
if (v_isShared_4072_ == 0)
{
lean_ctor_set(v___x_4071_, 4, v___x_4080_);
v___x_4082_ = v___x_4071_;
goto v_reusejp_4081_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_env_4062_);
lean_ctor_set(v_reuseFailAlloc_4085_, 1, v_nextMacroScope_4063_);
lean_ctor_set(v_reuseFailAlloc_4085_, 2, v_ngen_4064_);
lean_ctor_set(v_reuseFailAlloc_4085_, 3, v_auxDeclNGen_4065_);
lean_ctor_set(v_reuseFailAlloc_4085_, 4, v___x_4080_);
lean_ctor_set(v_reuseFailAlloc_4085_, 5, v_cache_4066_);
lean_ctor_set(v_reuseFailAlloc_4085_, 6, v_messages_4067_);
lean_ctor_set(v_reuseFailAlloc_4085_, 7, v_infoState_4068_);
lean_ctor_set(v_reuseFailAlloc_4085_, 8, v_snapshotTasks_4069_);
v___x_4082_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4081_;
}
v_reusejp_4081_:
{
lean_object* v___x_4083_; lean_object* v___x_4084_; 
v___x_4083_ = lean_st_ref_set(v___y_4020_, v___x_4082_);
v___x_4084_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_4022_);
return v___x_4084_;
}
}
}
}
}
else
{
goto v___jp_4053_;
}
}
else
{
goto v___jp_4053_;
}
}
v___jp_4089_:
{
double v___x_4091_; double v___x_4092_; double v___x_4093_; uint8_t v___x_4094_; 
v___x_4091_ = lean_unbox_float(v_snd_4039_);
v___x_4092_ = lean_unbox_float(v_fst_4038_);
v___x_4093_ = lean_float_sub(v___x_4091_, v___x_4092_);
v___x_4094_ = lean_float_decLt(v___y_4090_, v___x_4093_);
v___y_4059_ = v___x_4094_;
goto v___jp_4058_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1___boxed(lean_object* v_cls_4105_, lean_object* v_collapsed_4106_, lean_object* v_tag_4107_, lean_object* v_opts_4108_, lean_object* v_clsEnabled_4109_, lean_object* v_oldTraces_4110_, lean_object* v_msg_4111_, lean_object* v_resStartStop_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
uint8_t v_collapsed_boxed_4118_; uint8_t v_clsEnabled_boxed_4119_; lean_object* v_res_4120_; 
v_collapsed_boxed_4118_ = lean_unbox(v_collapsed_4106_);
v_clsEnabled_boxed_4119_ = lean_unbox(v_clsEnabled_4109_);
v_res_4120_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(v_cls_4105_, v_collapsed_boxed_4118_, v_tag_4107_, v_opts_4108_, v_clsEnabled_boxed_4119_, v_oldTraces_4110_, v_msg_4111_, v_resStartStop_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec_ref(v_opts_4108_);
return v_res_4120_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1(void){
_start:
{
lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4125_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_4126_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
v___x_4127_ = l_Lean_Name_append(v___x_4126_, v___x_4125_);
return v___x_4127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry(lean_object* v_e_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_){
_start:
{
lean_object* v_options_4134_; uint8_t v_hasTrace_4135_; 
v_options_4134_ = lean_ctor_get(v_a_4131_, 2);
v_hasTrace_4135_ = lean_ctor_get_uint8(v_options_4134_, sizeof(void*)*1);
if (v_hasTrace_4135_ == 0)
{
lean_object* v___x_4136_; 
v___x_4136_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4132_);
if (lean_obj_tag(v___x_4136_) == 0)
{
lean_object* v_a_4137_; lean_object* v___x_4138_; 
v_a_4137_ = lean_ctor_get(v___x_4136_, 0);
lean_inc(v_a_4137_);
lean_dec_ref_known(v___x_4136_, 1);
v___x_4138_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___f_4145_; lean_object* v___x_4146_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4139_);
lean_dec_ref_known(v___x_4138_, 1);
v___x_4140_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4141_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4134_, v___x_4140_);
v___x_4142_ = lean_unsigned_to_nat(2u);
v___x_4143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4141_);
lean_ctor_set(v___x_4143_, 1, v___x_4142_);
v___x_4144_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4137_);
v___f_4145_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4145_, 0, v_a_4139_);
lean_closure_set(v___f_4145_, 1, v___x_4144_);
lean_closure_set(v___f_4145_, 2, v___x_4143_);
v___x_4146_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_4145_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
return v___x_4146_;
}
else
{
lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4154_; 
lean_dec(v_a_4137_);
v_a_4147_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4149_ = v___x_4138_;
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_dec(v___x_4138_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4152_; 
if (v_isShared_4150_ == 0)
{
v___x_4152_ = v___x_4149_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4147_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
else
{
lean_object* v_a_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4162_; 
lean_dec_ref(v_e_4128_);
v_a_4155_ = lean_ctor_get(v___x_4136_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4157_ = v___x_4136_;
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_a_4155_);
lean_dec(v___x_4136_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4160_; 
if (v_isShared_4158_ == 0)
{
v___x_4160_ = v___x_4157_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4155_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_4163_; lean_object* v___f_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; uint8_t v___x_4168_; lean_object* v___y_4170_; lean_object* v___y_4171_; lean_object* v_a_4172_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v_a_4187_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v_a_4192_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v_a_4204_; 
v_inheritedTraceOptions_4163_ = lean_ctor_get(v_a_4131_, 13);
lean_inc_ref(v_e_4128_);
v___f_4164_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___boxed), 7, 1);
lean_closure_set(v___f_4164_, 0, v_e_4128_);
v___x_4165_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_4166_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_4167_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_4168_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4163_, v_options_4134_, v___x_4167_);
if (v___x_4168_ == 0)
{
lean_object* v___x_4257_; uint8_t v___x_4258_; 
v___x_4257_ = l_Lean_trace_profiler;
v___x_4258_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_4134_, v___x_4257_);
if (v___x_4258_ == 0)
{
lean_object* v___x_4259_; 
lean_dec_ref(v___f_4164_);
v___x_4259_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4132_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_object* v_a_4260_; lean_object* v___x_4261_; 
v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
lean_inc(v_a_4260_);
lean_dec_ref_known(v___x_4259_, 1);
v___x_4261_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4261_) == 0)
{
lean_object* v_a_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___f_4268_; lean_object* v___x_4269_; 
v_a_4262_ = lean_ctor_get(v___x_4261_, 0);
lean_inc(v_a_4262_);
lean_dec_ref_known(v___x_4261_, 1);
v___x_4263_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4264_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4134_, v___x_4263_);
v___x_4265_ = lean_unsigned_to_nat(2u);
v___x_4266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4266_, 0, v___x_4264_);
lean_ctor_set(v___x_4266_, 1, v___x_4265_);
v___x_4267_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4260_);
v___f_4268_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4268_, 0, v_a_4262_);
lean_closure_set(v___f_4268_, 1, v___x_4267_);
lean_closure_set(v___f_4268_, 2, v___x_4266_);
v___x_4269_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_4268_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
return v___x_4269_;
}
else
{
lean_object* v_a_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4277_; 
lean_dec(v_a_4260_);
v_a_4270_ = lean_ctor_get(v___x_4261_, 0);
v_isSharedCheck_4277_ = !lean_is_exclusive(v___x_4261_);
if (v_isSharedCheck_4277_ == 0)
{
v___x_4272_ = v___x_4261_;
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_a_4270_);
lean_dec(v___x_4261_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4275_; 
if (v_isShared_4273_ == 0)
{
v___x_4275_ = v___x_4272_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v_a_4270_);
v___x_4275_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
return v___x_4275_;
}
}
}
}
else
{
lean_object* v_a_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4285_; 
lean_dec_ref(v_e_4128_);
v_a_4278_ = lean_ctor_get(v___x_4259_, 0);
v_isSharedCheck_4285_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4285_ == 0)
{
v___x_4280_ = v___x_4259_;
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_a_4278_);
lean_dec(v___x_4259_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v___x_4283_; 
if (v_isShared_4281_ == 0)
{
v___x_4283_ = v___x_4280_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_a_4278_);
v___x_4283_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
return v___x_4283_;
}
}
}
}
else
{
goto v___jp_4206_;
}
}
else
{
goto v___jp_4206_;
}
v___jp_4169_:
{
lean_object* v___x_4173_; double v___x_4174_; double v___x_4175_; double v___x_4176_; double v___x_4177_; double v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4173_ = lean_io_mono_nanos_now();
v___x_4174_ = lean_float_of_nat(v___y_4171_);
v___x_4175_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_4176_ = lean_float_div(v___x_4174_, v___x_4175_);
v___x_4177_ = lean_float_of_nat(v___x_4173_);
v___x_4178_ = lean_float_div(v___x_4177_, v___x_4175_);
v___x_4179_ = lean_box_float(v___x_4176_);
v___x_4180_ = lean_box_float(v___x_4178_);
v___x_4181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4179_);
lean_ctor_set(v___x_4181_, 1, v___x_4180_);
v___x_4182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4182_, 0, v_a_4172_);
lean_ctor_set(v___x_4182_, 1, v___x_4181_);
v___x_4183_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(v___x_4165_, v_hasTrace_4135_, v___x_4166_, v_options_4134_, v___x_4168_, v___y_4170_, v___f_4164_, v___x_4182_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
return v___x_4183_;
}
v___jp_4184_:
{
lean_object* v___x_4188_; 
v___x_4188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4188_, 0, v_a_4187_);
v___y_4170_ = v___y_4185_;
v___y_4171_ = v___y_4186_;
v_a_4172_ = v___x_4188_;
goto v___jp_4169_;
}
v___jp_4189_:
{
lean_object* v___x_4193_; double v___x_4194_; double v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4193_ = lean_io_get_num_heartbeats();
v___x_4194_ = lean_float_of_nat(v___y_4191_);
v___x_4195_ = lean_float_of_nat(v___x_4193_);
v___x_4196_ = lean_box_float(v___x_4194_);
v___x_4197_ = lean_box_float(v___x_4195_);
v___x_4198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4198_, 0, v___x_4196_);
lean_ctor_set(v___x_4198_, 1, v___x_4197_);
v___x_4199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4199_, 0, v_a_4192_);
lean_ctor_set(v___x_4199_, 1, v___x_4198_);
v___x_4200_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(v___x_4165_, v_hasTrace_4135_, v___x_4166_, v_options_4134_, v___x_4168_, v___y_4190_, v___f_4164_, v___x_4199_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
return v___x_4200_;
}
v___jp_4201_:
{
lean_object* v___x_4205_; 
v___x_4205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4205_, 0, v_a_4204_);
v___y_4190_ = v___y_4202_;
v___y_4191_ = v___y_4203_;
v_a_4192_ = v___x_4205_;
goto v___jp_4189_;
}
v___jp_4206_:
{
lean_object* v___x_4207_; lean_object* v_a_4208_; lean_object* v___x_4209_; uint8_t v___x_4210_; 
v___x_4207_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v_a_4132_);
v_a_4208_ = lean_ctor_get(v___x_4207_, 0);
lean_inc(v_a_4208_);
lean_dec_ref(v___x_4207_);
v___x_4209_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4210_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_4134_, v___x_4209_);
if (v___x_4210_ == 0)
{
lean_object* v___x_4211_; lean_object* v___x_4212_; 
v___x_4211_ = lean_io_mono_nanos_now();
v___x_4212_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4132_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_object* v_a_4213_; lean_object* v___x_4214_; 
v_a_4213_ = lean_ctor_get(v___x_4212_, 0);
lean_inc(v_a_4213_);
lean_dec_ref_known(v___x_4212_, 1);
v___x_4214_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4214_) == 0)
{
lean_object* v_a_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; lean_object* v___f_4221_; lean_object* v___x_4222_; 
v_a_4215_ = lean_ctor_get(v___x_4214_, 0);
lean_inc(v_a_4215_);
lean_dec_ref_known(v___x_4214_, 1);
v___x_4216_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4217_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4134_, v___x_4216_);
v___x_4218_ = lean_unsigned_to_nat(2u);
v___x_4219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4219_, 0, v___x_4217_);
lean_ctor_set(v___x_4219_, 1, v___x_4218_);
v___x_4220_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4213_);
v___f_4221_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4221_, 0, v_a_4215_);
lean_closure_set(v___f_4221_, 1, v___x_4220_);
lean_closure_set(v___f_4221_, 2, v___x_4219_);
v___x_4222_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_4221_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4222_) == 0)
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4230_; 
v_a_4223_ = lean_ctor_get(v___x_4222_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_4222_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4225_ = v___x_4222_;
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4222_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4228_; 
if (v_isShared_4226_ == 0)
{
lean_ctor_set_tag(v___x_4225_, 1);
v___x_4228_ = v___x_4225_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_a_4223_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
v___y_4170_ = v_a_4208_;
v___y_4171_ = v___x_4211_;
v_a_4172_ = v___x_4228_;
goto v___jp_4169_;
}
}
}
else
{
lean_object* v_a_4231_; 
v_a_4231_ = lean_ctor_get(v___x_4222_, 0);
lean_inc(v_a_4231_);
lean_dec_ref_known(v___x_4222_, 1);
v___y_4185_ = v_a_4208_;
v___y_4186_ = v___x_4211_;
v_a_4187_ = v_a_4231_;
goto v___jp_4184_;
}
}
else
{
lean_object* v_a_4232_; 
lean_dec(v_a_4213_);
v_a_4232_ = lean_ctor_get(v___x_4214_, 0);
lean_inc(v_a_4232_);
lean_dec_ref_known(v___x_4214_, 1);
v___y_4185_ = v_a_4208_;
v___y_4186_ = v___x_4211_;
v_a_4187_ = v_a_4232_;
goto v___jp_4184_;
}
}
else
{
lean_object* v_a_4233_; 
lean_dec_ref(v_e_4128_);
v_a_4233_ = lean_ctor_get(v___x_4212_, 0);
lean_inc(v_a_4233_);
lean_dec_ref_known(v___x_4212_, 1);
v___y_4185_ = v_a_4208_;
v___y_4186_ = v___x_4211_;
v_a_4187_ = v_a_4233_;
goto v___jp_4184_;
}
}
else
{
lean_object* v___x_4234_; lean_object* v___x_4235_; 
v___x_4234_ = lean_io_get_num_heartbeats();
v___x_4235_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4132_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v_a_4236_; lean_object* v___x_4237_; 
v_a_4236_ = lean_ctor_get(v___x_4235_, 0);
lean_inc(v_a_4236_);
lean_dec_ref_known(v___x_4235_, 1);
v___x_4237_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_object* v_a_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___f_4244_; lean_object* v___x_4245_; 
v_a_4238_ = lean_ctor_get(v___x_4237_, 0);
lean_inc(v_a_4238_);
lean_dec_ref_known(v___x_4237_, 1);
v___x_4239_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4240_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4134_, v___x_4239_);
v___x_4241_ = lean_unsigned_to_nat(2u);
v___x_4242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4240_);
lean_ctor_set(v___x_4242_, 1, v___x_4241_);
v___x_4243_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4236_);
v___f_4244_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4244_, 0, v_a_4238_);
lean_closure_set(v___f_4244_, 1, v___x_4243_);
lean_closure_set(v___f_4244_, 2, v___x_4242_);
v___x_4245_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_4244_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
if (lean_obj_tag(v___x_4245_) == 0)
{
lean_object* v_a_4246_; lean_object* v___x_4248_; uint8_t v_isShared_4249_; uint8_t v_isSharedCheck_4253_; 
v_a_4246_ = lean_ctor_get(v___x_4245_, 0);
v_isSharedCheck_4253_ = !lean_is_exclusive(v___x_4245_);
if (v_isSharedCheck_4253_ == 0)
{
v___x_4248_ = v___x_4245_;
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
else
{
lean_inc(v_a_4246_);
lean_dec(v___x_4245_);
v___x_4248_ = lean_box(0);
v_isShared_4249_ = v_isSharedCheck_4253_;
goto v_resetjp_4247_;
}
v_resetjp_4247_:
{
lean_object* v___x_4251_; 
if (v_isShared_4249_ == 0)
{
lean_ctor_set_tag(v___x_4248_, 1);
v___x_4251_ = v___x_4248_;
goto v_reusejp_4250_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_a_4246_);
v___x_4251_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4250_;
}
v_reusejp_4250_:
{
v___y_4190_ = v_a_4208_;
v___y_4191_ = v___x_4234_;
v_a_4192_ = v___x_4251_;
goto v___jp_4189_;
}
}
}
else
{
lean_object* v_a_4254_; 
v_a_4254_ = lean_ctor_get(v___x_4245_, 0);
lean_inc(v_a_4254_);
lean_dec_ref_known(v___x_4245_, 1);
v___y_4202_ = v_a_4208_;
v___y_4203_ = v___x_4234_;
v_a_4204_ = v_a_4254_;
goto v___jp_4201_;
}
}
else
{
lean_object* v_a_4255_; 
lean_dec(v_a_4236_);
v_a_4255_ = lean_ctor_get(v___x_4237_, 0);
lean_inc(v_a_4255_);
lean_dec_ref_known(v___x_4237_, 1);
v___y_4202_ = v_a_4208_;
v___y_4203_ = v___x_4234_;
v_a_4204_ = v_a_4255_;
goto v___jp_4201_;
}
}
else
{
lean_object* v_a_4256_; 
lean_dec_ref(v_e_4128_);
v_a_4256_ = lean_ctor_get(v___x_4235_, 0);
lean_inc(v_a_4256_);
lean_dec_ref_known(v___x_4235_, 1);
v___y_4202_ = v_a_4208_;
v___y_4203_ = v___x_4234_;
v_a_4204_ = v_a_4256_;
goto v___jp_4201_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___boxed(lean_object* v_e_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l_Lean_Meta_Tactic_Cbv_cbvEntry(v_e_4286_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_);
lean_dec(v_a_4290_);
lean_dec_ref(v_a_4289_);
lean_dec(v_a_4288_);
lean_dec_ref(v_a_4287_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2(lean_object* v_00_u03b1_4293_, lean_object* v_x_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_){
_start:
{
lean_object* v___x_4300_; 
v___x_4300_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_x_4294_);
return v___x_4300_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___boxed(lean_object* v_00_u03b1_4301_, lean_object* v_x_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_){
_start:
{
lean_object* v_res_4308_; 
v_res_4308_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2(v_00_u03b1_4301_, v_x_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
return v_res_4308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(lean_object* v___y_4309_){
_start:
{
lean_object* v___x_4311_; lean_object* v_traceState_4312_; lean_object* v_traces_4313_; lean_object* v___x_4314_; lean_object* v_traceState_4315_; lean_object* v_env_4316_; lean_object* v_nextMacroScope_4317_; lean_object* v_ngen_4318_; lean_object* v_auxDeclNGen_4319_; lean_object* v_cache_4320_; lean_object* v_messages_4321_; lean_object* v_infoState_4322_; lean_object* v_snapshotTasks_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4344_; 
v___x_4311_ = lean_st_ref_get(v___y_4309_);
v_traceState_4312_ = lean_ctor_get(v___x_4311_, 4);
lean_inc_ref(v_traceState_4312_);
lean_dec(v___x_4311_);
v_traces_4313_ = lean_ctor_get(v_traceState_4312_, 0);
lean_inc_ref(v_traces_4313_);
lean_dec_ref(v_traceState_4312_);
v___x_4314_ = lean_st_ref_take(v___y_4309_);
v_traceState_4315_ = lean_ctor_get(v___x_4314_, 4);
v_env_4316_ = lean_ctor_get(v___x_4314_, 0);
v_nextMacroScope_4317_ = lean_ctor_get(v___x_4314_, 1);
v_ngen_4318_ = lean_ctor_get(v___x_4314_, 2);
v_auxDeclNGen_4319_ = lean_ctor_get(v___x_4314_, 3);
v_cache_4320_ = lean_ctor_get(v___x_4314_, 5);
v_messages_4321_ = lean_ctor_get(v___x_4314_, 6);
v_infoState_4322_ = lean_ctor_get(v___x_4314_, 7);
v_snapshotTasks_4323_ = lean_ctor_get(v___x_4314_, 8);
v_isSharedCheck_4344_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4344_ == 0)
{
v___x_4325_ = v___x_4314_;
v_isShared_4326_ = v_isSharedCheck_4344_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_snapshotTasks_4323_);
lean_inc(v_infoState_4322_);
lean_inc(v_messages_4321_);
lean_inc(v_cache_4320_);
lean_inc(v_traceState_4315_);
lean_inc(v_auxDeclNGen_4319_);
lean_inc(v_ngen_4318_);
lean_inc(v_nextMacroScope_4317_);
lean_inc(v_env_4316_);
lean_dec(v___x_4314_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4344_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
uint64_t v_tid_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4342_; 
v_tid_4327_ = lean_ctor_get_uint64(v_traceState_4315_, sizeof(void*)*1);
v_isSharedCheck_4342_ = !lean_is_exclusive(v_traceState_4315_);
if (v_isSharedCheck_4342_ == 0)
{
lean_object* v_unused_4343_; 
v_unused_4343_ = lean_ctor_get(v_traceState_4315_, 0);
lean_dec(v_unused_4343_);
v___x_4329_ = v_traceState_4315_;
v_isShared_4330_ = v_isSharedCheck_4342_;
goto v_resetjp_4328_;
}
else
{
lean_dec(v_traceState_4315_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4342_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4335_; 
v___x_4331_ = lean_unsigned_to_nat(32u);
v___x_4332_ = lean_mk_empty_array_with_capacity(v___x_4331_);
lean_dec_ref(v___x_4332_);
v___x_4333_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1);
if (v_isShared_4330_ == 0)
{
lean_ctor_set(v___x_4329_, 0, v___x_4333_);
v___x_4335_ = v___x_4329_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v___x_4333_);
lean_ctor_set_uint64(v_reuseFailAlloc_4341_, sizeof(void*)*1, v_tid_4327_);
v___x_4335_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
lean_object* v___x_4337_; 
if (v_isShared_4326_ == 0)
{
lean_ctor_set(v___x_4325_, 4, v___x_4335_);
v___x_4337_ = v___x_4325_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_env_4316_);
lean_ctor_set(v_reuseFailAlloc_4340_, 1, v_nextMacroScope_4317_);
lean_ctor_set(v_reuseFailAlloc_4340_, 2, v_ngen_4318_);
lean_ctor_set(v_reuseFailAlloc_4340_, 3, v_auxDeclNGen_4319_);
lean_ctor_set(v_reuseFailAlloc_4340_, 4, v___x_4335_);
lean_ctor_set(v_reuseFailAlloc_4340_, 5, v_cache_4320_);
lean_ctor_set(v_reuseFailAlloc_4340_, 6, v_messages_4321_);
lean_ctor_set(v_reuseFailAlloc_4340_, 7, v_infoState_4322_);
lean_ctor_set(v_reuseFailAlloc_4340_, 8, v_snapshotTasks_4323_);
v___x_4337_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
lean_object* v___x_4338_; lean_object* v___x_4339_; 
v___x_4338_ = lean_st_ref_set(v___y_4309_, v___x_4337_);
v___x_4339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4339_, 0, v_traces_4313_);
return v___x_4339_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg___boxed(lean_object* v___y_4345_, lean_object* v___y_4346_){
_start:
{
lean_object* v_res_4347_; 
v_res_4347_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(v___y_4345_);
lean_dec(v___y_4345_);
return v_res_4347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1(lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_){
_start:
{
lean_object* v___x_4355_; 
v___x_4355_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(v___y_4353_);
return v___x_4355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___boxed(lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_){
_start:
{
lean_object* v_res_4363_; 
v_res_4363_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1(v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_);
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
lean_dec(v___y_4359_);
lean_dec_ref(v___y_4358_);
lean_dec(v___y_4357_);
lean_dec_ref(v___y_4356_);
return v_res_4363_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0(lean_object* v_x_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
lean_object* v___x_4372_; 
lean_inc(v___y_4366_);
lean_inc_ref(v___y_4365_);
v___x_4372_ = lean_apply_7(v_x_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_, lean_box(0));
return v___x_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0___boxed(lean_object* v_x_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_){
_start:
{
lean_object* v_res_4381_; 
v_res_4381_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0(v_x_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4374_);
return v_res_4381_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg(lean_object* v_mvarId_4382_, lean_object* v_x_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_){
_start:
{
lean_object* v___f_4391_; lean_object* v___x_4392_; 
lean_inc(v___y_4385_);
lean_inc_ref(v___y_4384_);
v___f_4391_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4391_, 0, v_x_4383_);
lean_closure_set(v___f_4391_, 1, v___y_4384_);
lean_closure_set(v___f_4391_, 2, v___y_4385_);
v___x_4392_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4382_, v___f_4391_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_);
if (lean_obj_tag(v___x_4392_) == 0)
{
return v___x_4392_;
}
else
{
lean_object* v_a_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4400_; 
v_a_4393_ = lean_ctor_get(v___x_4392_, 0);
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4392_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4395_ = v___x_4392_;
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_a_4393_);
lean_dec(v___x_4392_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4400_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v___x_4398_; 
if (v_isShared_4396_ == 0)
{
v___x_4398_ = v___x_4395_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v_a_4393_);
v___x_4398_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
return v___x_4398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___boxed(lean_object* v_mvarId_4401_, lean_object* v_x_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_){
_start:
{
lean_object* v_res_4410_; 
v_res_4410_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg(v_mvarId_4401_, v_x_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_);
lean_dec(v___y_4408_);
lean_dec_ref(v___y_4407_);
lean_dec(v___y_4406_);
lean_dec_ref(v___y_4405_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
return v_res_4410_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4(lean_object* v_00_u03b1_4411_, lean_object* v_mvarId_4412_, lean_object* v_x_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
lean_object* v___x_4421_; 
v___x_4421_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg(v_mvarId_4412_, v_x_4413_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_);
return v___x_4421_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___boxed(lean_object* v_00_u03b1_4422_, lean_object* v_mvarId_4423_, lean_object* v_x_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_){
_start:
{
lean_object* v_res_4432_; 
v_res_4432_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4(v_00_u03b1_4422_, v_mvarId_4423_, v_x_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_);
lean_dec(v___y_4430_);
lean_dec_ref(v___y_4429_);
lean_dec(v___y_4428_);
lean_dec_ref(v___y_4427_);
lean_dec(v___y_4426_);
lean_dec_ref(v___y_4425_);
return v_res_4432_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4434_; lean_object* v___x_4435_; 
v___x_4434_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__0));
v___x_4435_ = l_Lean_stringToMessageData(v___x_4434_);
return v___x_4435_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4437_; lean_object* v___x_4438_; 
v___x_4437_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__2));
v___x_4438_ = l_Lean_stringToMessageData(v___x_4437_);
return v___x_4438_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4440_; lean_object* v___x_4441_; 
v___x_4440_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__4));
v___x_4441_ = l_Lean_stringToMessageData(v___x_4440_);
return v___x_4441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0(lean_object* v_a_4442_, lean_object* v_x_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_){
_start:
{
if (lean_obj_tag(v_x_4443_) == 0)
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4461_; 
lean_dec_ref(v_a_4442_);
v_a_4451_ = lean_ctor_get(v_x_4443_, 0);
v_isSharedCheck_4461_ = !lean_is_exclusive(v_x_4443_);
if (v_isSharedCheck_4461_ == 0)
{
v___x_4453_ = v_x_4443_;
v_isShared_4454_ = v_isSharedCheck_4461_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v_x_4443_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4461_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4459_; 
v___x_4455_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1);
v___x_4456_ = l_Lean_Exception_toMessageData(v_a_4451_);
v___x_4457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4457_, 0, v___x_4455_);
lean_ctor_set(v___x_4457_, 1, v___x_4456_);
if (v_isShared_4454_ == 0)
{
lean_ctor_set(v___x_4453_, 0, v___x_4457_);
v___x_4459_ = v___x_4453_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v___x_4457_);
v___x_4459_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
return v___x_4459_;
}
}
}
else
{
lean_object* v_a_4462_; lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4481_; 
v_a_4462_ = lean_ctor_get(v_x_4443_, 0);
v_isSharedCheck_4481_ = !lean_is_exclusive(v_x_4443_);
if (v_isSharedCheck_4481_ == 0)
{
v___x_4464_ = v_x_4443_;
v_isShared_4465_ = v_isSharedCheck_4481_;
goto v_resetjp_4463_;
}
else
{
lean_inc(v_a_4462_);
lean_dec(v_x_4443_);
v___x_4464_ = lean_box(0);
v_isShared_4465_ = v_isSharedCheck_4481_;
goto v_resetjp_4463_;
}
v_resetjp_4463_:
{
if (lean_obj_tag(v_a_4462_) == 0)
{
lean_object* v___x_4466_; lean_object* v___x_4468_; 
lean_dec_ref_known(v_a_4462_, 0);
lean_dec_ref(v_a_4442_);
v___x_4466_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3);
if (v_isShared_4465_ == 0)
{
lean_ctor_set_tag(v___x_4464_, 0);
lean_ctor_set(v___x_4464_, 0, v___x_4466_);
v___x_4468_ = v___x_4464_;
goto v_reusejp_4467_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v___x_4466_);
v___x_4468_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4467_;
}
v_reusejp_4467_:
{
return v___x_4468_;
}
}
else
{
lean_object* v_e_x27_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4479_; 
v_e_x27_4470_ = lean_ctor_get(v_a_4462_, 0);
lean_inc_ref(v_e_x27_4470_);
lean_dec_ref_known(v_a_4462_, 2);
v___x_4471_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5, &l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5);
v___x_4472_ = l_Lean_indentExpr(v_a_4442_);
v___x_4473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4473_, 0, v___x_4471_);
lean_ctor_set(v___x_4473_, 1, v___x_4472_);
v___x_4474_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_4475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4475_, 0, v___x_4473_);
lean_ctor_set(v___x_4475_, 1, v___x_4474_);
v___x_4476_ = l_Lean_indentExpr(v_e_x27_4470_);
v___x_4477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4477_, 0, v___x_4475_);
lean_ctor_set(v___x_4477_, 1, v___x_4476_);
if (v_isShared_4465_ == 0)
{
lean_ctor_set_tag(v___x_4464_, 0);
lean_ctor_set(v___x_4464_, 0, v___x_4477_);
v___x_4479_ = v___x_4464_;
goto v_reusejp_4478_;
}
else
{
lean_object* v_reuseFailAlloc_4480_; 
v_reuseFailAlloc_4480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4480_, 0, v___x_4477_);
v___x_4479_ = v_reuseFailAlloc_4480_;
goto v_reusejp_4478_;
}
v_reusejp_4478_:
{
return v___x_4479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___boxed(lean_object* v_a_4482_, lean_object* v_x_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_){
_start:
{
lean_object* v_res_4491_; 
v_res_4491_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0(v_a_4482_, v_x_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_);
lean_dec(v___y_4489_);
lean_dec_ref(v___y_4488_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
lean_dec(v___y_4485_);
lean_dec_ref(v___y_4484_);
return v_res_4491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg(lean_object* v_oldTraces_4492_, lean_object* v_data_4493_, lean_object* v_ref_4494_, lean_object* v_msg_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_){
_start:
{
lean_object* v_fileName_4501_; lean_object* v_fileMap_4502_; lean_object* v_options_4503_; lean_object* v_currRecDepth_4504_; lean_object* v_maxRecDepth_4505_; lean_object* v_ref_4506_; lean_object* v_currNamespace_4507_; lean_object* v_openDecls_4508_; lean_object* v_initHeartbeats_4509_; lean_object* v_maxHeartbeats_4510_; lean_object* v_quotContext_4511_; lean_object* v_currMacroScope_4512_; uint8_t v_diag_4513_; lean_object* v_cancelTk_x3f_4514_; uint8_t v_suppressElabErrors_4515_; lean_object* v_inheritedTraceOptions_4516_; lean_object* v___x_4517_; lean_object* v_traceState_4518_; lean_object* v_traces_4519_; lean_object* v_ref_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; size_t v_sz_4523_; size_t v___x_4524_; lean_object* v___x_4525_; lean_object* v_msg_4526_; lean_object* v___x_4527_; lean_object* v_a_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4565_; 
v_fileName_4501_ = lean_ctor_get(v___y_4498_, 0);
v_fileMap_4502_ = lean_ctor_get(v___y_4498_, 1);
v_options_4503_ = lean_ctor_get(v___y_4498_, 2);
v_currRecDepth_4504_ = lean_ctor_get(v___y_4498_, 3);
v_maxRecDepth_4505_ = lean_ctor_get(v___y_4498_, 4);
v_ref_4506_ = lean_ctor_get(v___y_4498_, 5);
v_currNamespace_4507_ = lean_ctor_get(v___y_4498_, 6);
v_openDecls_4508_ = lean_ctor_get(v___y_4498_, 7);
v_initHeartbeats_4509_ = lean_ctor_get(v___y_4498_, 8);
v_maxHeartbeats_4510_ = lean_ctor_get(v___y_4498_, 9);
v_quotContext_4511_ = lean_ctor_get(v___y_4498_, 10);
v_currMacroScope_4512_ = lean_ctor_get(v___y_4498_, 11);
v_diag_4513_ = lean_ctor_get_uint8(v___y_4498_, sizeof(void*)*14);
v_cancelTk_x3f_4514_ = lean_ctor_get(v___y_4498_, 12);
v_suppressElabErrors_4515_ = lean_ctor_get_uint8(v___y_4498_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4516_ = lean_ctor_get(v___y_4498_, 13);
v___x_4517_ = lean_st_ref_get(v___y_4499_);
v_traceState_4518_ = lean_ctor_get(v___x_4517_, 4);
lean_inc_ref(v_traceState_4518_);
lean_dec(v___x_4517_);
v_traces_4519_ = lean_ctor_get(v_traceState_4518_, 0);
lean_inc_ref(v_traces_4519_);
lean_dec_ref(v_traceState_4518_);
v_ref_4520_ = l_Lean_replaceRef(v_ref_4494_, v_ref_4506_);
lean_inc_ref(v_inheritedTraceOptions_4516_);
lean_inc(v_cancelTk_x3f_4514_);
lean_inc(v_currMacroScope_4512_);
lean_inc(v_quotContext_4511_);
lean_inc(v_maxHeartbeats_4510_);
lean_inc(v_initHeartbeats_4509_);
lean_inc(v_openDecls_4508_);
lean_inc(v_currNamespace_4507_);
lean_inc(v_maxRecDepth_4505_);
lean_inc(v_currRecDepth_4504_);
lean_inc_ref(v_options_4503_);
lean_inc_ref(v_fileMap_4502_);
lean_inc_ref(v_fileName_4501_);
v___x_4521_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4521_, 0, v_fileName_4501_);
lean_ctor_set(v___x_4521_, 1, v_fileMap_4502_);
lean_ctor_set(v___x_4521_, 2, v_options_4503_);
lean_ctor_set(v___x_4521_, 3, v_currRecDepth_4504_);
lean_ctor_set(v___x_4521_, 4, v_maxRecDepth_4505_);
lean_ctor_set(v___x_4521_, 5, v_ref_4520_);
lean_ctor_set(v___x_4521_, 6, v_currNamespace_4507_);
lean_ctor_set(v___x_4521_, 7, v_openDecls_4508_);
lean_ctor_set(v___x_4521_, 8, v_initHeartbeats_4509_);
lean_ctor_set(v___x_4521_, 9, v_maxHeartbeats_4510_);
lean_ctor_set(v___x_4521_, 10, v_quotContext_4511_);
lean_ctor_set(v___x_4521_, 11, v_currMacroScope_4512_);
lean_ctor_set(v___x_4521_, 12, v_cancelTk_x3f_4514_);
lean_ctor_set(v___x_4521_, 13, v_inheritedTraceOptions_4516_);
lean_ctor_set_uint8(v___x_4521_, sizeof(void*)*14, v_diag_4513_);
lean_ctor_set_uint8(v___x_4521_, sizeof(void*)*14 + 1, v_suppressElabErrors_4515_);
v___x_4522_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4519_);
lean_dec_ref(v_traces_4519_);
v_sz_4523_ = lean_array_size(v___x_4522_);
v___x_4524_ = ((size_t)0ULL);
v___x_4525_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5(v_sz_4523_, v___x_4524_, v___x_4522_);
v_msg_4526_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4526_, 0, v_data_4493_);
lean_ctor_set(v_msg_4526_, 1, v_msg_4495_);
lean_ctor_set(v_msg_4526_, 2, v___x_4525_);
v___x_4527_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_4526_, v___y_4496_, v___y_4497_, v___x_4521_, v___y_4499_);
lean_dec_ref_known(v___x_4521_, 14);
v_a_4528_ = lean_ctor_get(v___x_4527_, 0);
v_isSharedCheck_4565_ = !lean_is_exclusive(v___x_4527_);
if (v_isSharedCheck_4565_ == 0)
{
v___x_4530_ = v___x_4527_;
v_isShared_4531_ = v_isSharedCheck_4565_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_a_4528_);
lean_dec(v___x_4527_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4565_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
lean_object* v___x_4532_; lean_object* v_traceState_4533_; lean_object* v_env_4534_; lean_object* v_nextMacroScope_4535_; lean_object* v_ngen_4536_; lean_object* v_auxDeclNGen_4537_; lean_object* v_cache_4538_; lean_object* v_messages_4539_; lean_object* v_infoState_4540_; lean_object* v_snapshotTasks_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4564_; 
v___x_4532_ = lean_st_ref_take(v___y_4499_);
v_traceState_4533_ = lean_ctor_get(v___x_4532_, 4);
v_env_4534_ = lean_ctor_get(v___x_4532_, 0);
v_nextMacroScope_4535_ = lean_ctor_get(v___x_4532_, 1);
v_ngen_4536_ = lean_ctor_get(v___x_4532_, 2);
v_auxDeclNGen_4537_ = lean_ctor_get(v___x_4532_, 3);
v_cache_4538_ = lean_ctor_get(v___x_4532_, 5);
v_messages_4539_ = lean_ctor_get(v___x_4532_, 6);
v_infoState_4540_ = lean_ctor_get(v___x_4532_, 7);
v_snapshotTasks_4541_ = lean_ctor_get(v___x_4532_, 8);
v_isSharedCheck_4564_ = !lean_is_exclusive(v___x_4532_);
if (v_isSharedCheck_4564_ == 0)
{
v___x_4543_ = v___x_4532_;
v_isShared_4544_ = v_isSharedCheck_4564_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_snapshotTasks_4541_);
lean_inc(v_infoState_4540_);
lean_inc(v_messages_4539_);
lean_inc(v_cache_4538_);
lean_inc(v_traceState_4533_);
lean_inc(v_auxDeclNGen_4537_);
lean_inc(v_ngen_4536_);
lean_inc(v_nextMacroScope_4535_);
lean_inc(v_env_4534_);
lean_dec(v___x_4532_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4564_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
uint64_t v_tid_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4562_; 
v_tid_4545_ = lean_ctor_get_uint64(v_traceState_4533_, sizeof(void*)*1);
v_isSharedCheck_4562_ = !lean_is_exclusive(v_traceState_4533_);
if (v_isSharedCheck_4562_ == 0)
{
lean_object* v_unused_4563_; 
v_unused_4563_ = lean_ctor_get(v_traceState_4533_, 0);
lean_dec(v_unused_4563_);
v___x_4547_ = v_traceState_4533_;
v_isShared_4548_ = v_isSharedCheck_4562_;
goto v_resetjp_4546_;
}
else
{
lean_dec(v_traceState_4533_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4562_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4552_; 
v___x_4549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4549_, 0, v_ref_4494_);
lean_ctor_set(v___x_4549_, 1, v_a_4528_);
v___x_4550_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4492_, v___x_4549_);
if (v_isShared_4548_ == 0)
{
lean_ctor_set(v___x_4547_, 0, v___x_4550_);
v___x_4552_ = v___x_4547_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v___x_4550_);
lean_ctor_set_uint64(v_reuseFailAlloc_4561_, sizeof(void*)*1, v_tid_4545_);
v___x_4552_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
lean_object* v___x_4554_; 
if (v_isShared_4544_ == 0)
{
lean_ctor_set(v___x_4543_, 4, v___x_4552_);
v___x_4554_ = v___x_4543_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_env_4534_);
lean_ctor_set(v_reuseFailAlloc_4560_, 1, v_nextMacroScope_4535_);
lean_ctor_set(v_reuseFailAlloc_4560_, 2, v_ngen_4536_);
lean_ctor_set(v_reuseFailAlloc_4560_, 3, v_auxDeclNGen_4537_);
lean_ctor_set(v_reuseFailAlloc_4560_, 4, v___x_4552_);
lean_ctor_set(v_reuseFailAlloc_4560_, 5, v_cache_4538_);
lean_ctor_set(v_reuseFailAlloc_4560_, 6, v_messages_4539_);
lean_ctor_set(v_reuseFailAlloc_4560_, 7, v_infoState_4540_);
lean_ctor_set(v_reuseFailAlloc_4560_, 8, v_snapshotTasks_4541_);
v___x_4554_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4558_; 
v___x_4555_ = lean_st_ref_set(v___y_4499_, v___x_4554_);
v___x_4556_ = lean_box(0);
if (v_isShared_4531_ == 0)
{
lean_ctor_set(v___x_4530_, 0, v___x_4556_);
v___x_4558_ = v___x_4530_;
goto v_reusejp_4557_;
}
else
{
lean_object* v_reuseFailAlloc_4559_; 
v_reuseFailAlloc_4559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4559_, 0, v___x_4556_);
v___x_4558_ = v_reuseFailAlloc_4559_;
goto v_reusejp_4557_;
}
v_reusejp_4557_:
{
return v___x_4558_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg___boxed(lean_object* v_oldTraces_4566_, lean_object* v_data_4567_, lean_object* v_ref_4568_, lean_object* v_msg_4569_, lean_object* v___y_4570_, lean_object* v___y_4571_, lean_object* v___y_4572_, lean_object* v___y_4573_, lean_object* v___y_4574_){
_start:
{
lean_object* v_res_4575_; 
v_res_4575_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg(v_oldTraces_4566_, v_data_4567_, v_ref_4568_, v_msg_4569_, v___y_4570_, v___y_4571_, v___y_4572_, v___y_4573_);
lean_dec(v___y_4573_);
lean_dec_ref(v___y_4572_);
lean_dec(v___y_4571_);
lean_dec_ref(v___y_4570_);
return v_res_4575_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(lean_object* v_x_4576_){
_start:
{
if (lean_obj_tag(v_x_4576_) == 0)
{
lean_object* v_a_4578_; lean_object* v___x_4580_; uint8_t v_isShared_4581_; uint8_t v_isSharedCheck_4585_; 
v_a_4578_ = lean_ctor_get(v_x_4576_, 0);
v_isSharedCheck_4585_ = !lean_is_exclusive(v_x_4576_);
if (v_isSharedCheck_4585_ == 0)
{
v___x_4580_ = v_x_4576_;
v_isShared_4581_ = v_isSharedCheck_4585_;
goto v_resetjp_4579_;
}
else
{
lean_inc(v_a_4578_);
lean_dec(v_x_4576_);
v___x_4580_ = lean_box(0);
v_isShared_4581_ = v_isSharedCheck_4585_;
goto v_resetjp_4579_;
}
v_resetjp_4579_:
{
lean_object* v___x_4583_; 
if (v_isShared_4581_ == 0)
{
lean_ctor_set_tag(v___x_4580_, 1);
v___x_4583_ = v___x_4580_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4584_; 
v_reuseFailAlloc_4584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4584_, 0, v_a_4578_);
v___x_4583_ = v_reuseFailAlloc_4584_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
return v___x_4583_;
}
}
}
else
{
lean_object* v_a_4586_; lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4593_; 
v_a_4586_ = lean_ctor_get(v_x_4576_, 0);
v_isSharedCheck_4593_ = !lean_is_exclusive(v_x_4576_);
if (v_isSharedCheck_4593_ == 0)
{
v___x_4588_ = v_x_4576_;
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
else
{
lean_inc(v_a_4586_);
lean_dec(v_x_4576_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
lean_object* v___x_4591_; 
if (v_isShared_4589_ == 0)
{
lean_ctor_set_tag(v___x_4588_, 0);
v___x_4591_ = v___x_4588_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v_a_4586_);
v___x_4591_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
return v___x_4591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg___boxed(lean_object* v_x_4594_, lean_object* v___y_4595_){
_start:
{
lean_object* v_res_4596_; 
v_res_4596_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(v_x_4594_);
return v_res_4596_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(lean_object* v_cls_4597_, uint8_t v_collapsed_4598_, lean_object* v_tag_4599_, lean_object* v_opts_4600_, uint8_t v_clsEnabled_4601_, lean_object* v_oldTraces_4602_, lean_object* v_msg_4603_, lean_object* v_resStartStop_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_){
_start:
{
lean_object* v_fst_4612_; lean_object* v_snd_4613_; lean_object* v___y_4615_; lean_object* v___y_4616_; lean_object* v_data_4617_; lean_object* v_fst_4628_; lean_object* v_snd_4629_; lean_object* v___x_4630_; uint8_t v___x_4631_; lean_object* v___y_4633_; lean_object* v_a_4634_; uint8_t v___y_4649_; double v___y_4680_; 
v_fst_4612_ = lean_ctor_get(v_resStartStop_4604_, 0);
lean_inc(v_fst_4612_);
v_snd_4613_ = lean_ctor_get(v_resStartStop_4604_, 1);
lean_inc(v_snd_4613_);
lean_dec_ref(v_resStartStop_4604_);
v_fst_4628_ = lean_ctor_get(v_snd_4613_, 0);
lean_inc(v_fst_4628_);
v_snd_4629_ = lean_ctor_get(v_snd_4613_, 1);
lean_inc(v_snd_4629_);
lean_dec(v_snd_4613_);
v___x_4630_ = l_Lean_trace_profiler;
v___x_4631_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4600_, v___x_4630_);
if (v___x_4631_ == 0)
{
v___y_4649_ = v___x_4631_;
goto v___jp_4648_;
}
else
{
lean_object* v___x_4685_; uint8_t v___x_4686_; 
v___x_4685_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4686_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4600_, v___x_4685_);
if (v___x_4686_ == 0)
{
lean_object* v___x_4687_; lean_object* v___x_4688_; double v___x_4689_; double v___x_4690_; double v___x_4691_; 
v___x_4687_ = l_Lean_trace_profiler_threshold;
v___x_4688_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4600_, v___x_4687_);
v___x_4689_ = lean_float_of_nat(v___x_4688_);
v___x_4690_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2);
v___x_4691_ = lean_float_div(v___x_4689_, v___x_4690_);
v___y_4680_ = v___x_4691_;
goto v___jp_4679_;
}
else
{
lean_object* v___x_4692_; lean_object* v___x_4693_; double v___x_4694_; 
v___x_4692_ = l_Lean_trace_profiler_threshold;
v___x_4693_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4600_, v___x_4692_);
v___x_4694_ = lean_float_of_nat(v___x_4693_);
v___y_4680_ = v___x_4694_;
goto v___jp_4679_;
}
}
v___jp_4614_:
{
lean_object* v___x_4618_; 
lean_inc(v___y_4615_);
v___x_4618_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg(v_oldTraces_4602_, v_data_4617_, v___y_4615_, v___y_4616_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_);
if (lean_obj_tag(v___x_4618_) == 0)
{
lean_object* v___x_4619_; 
lean_dec_ref_known(v___x_4618_, 1);
v___x_4619_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(v_fst_4612_);
return v___x_4619_;
}
else
{
lean_object* v_a_4620_; lean_object* v___x_4622_; uint8_t v_isShared_4623_; uint8_t v_isSharedCheck_4627_; 
lean_dec(v_fst_4612_);
v_a_4620_ = lean_ctor_get(v___x_4618_, 0);
v_isSharedCheck_4627_ = !lean_is_exclusive(v___x_4618_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_4622_ = v___x_4618_;
v_isShared_4623_ = v_isSharedCheck_4627_;
goto v_resetjp_4621_;
}
else
{
lean_inc(v_a_4620_);
lean_dec(v___x_4618_);
v___x_4622_ = lean_box(0);
v_isShared_4623_ = v_isSharedCheck_4627_;
goto v_resetjp_4621_;
}
v_resetjp_4621_:
{
lean_object* v___x_4625_; 
if (v_isShared_4623_ == 0)
{
v___x_4625_ = v___x_4622_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v_a_4620_);
v___x_4625_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
return v___x_4625_;
}
}
}
}
v___jp_4632_:
{
uint8_t v_result_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; double v___x_4638_; lean_object* v_data_4639_; 
v_result_4635_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(v_fst_4612_);
v___x_4636_ = lean_box(v_result_4635_);
v___x_4637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4637_, 0, v___x_4636_);
v___x_4638_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_4599_);
lean_inc_ref(v___x_4637_);
lean_inc(v_cls_4597_);
v_data_4639_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4639_, 0, v_cls_4597_);
lean_ctor_set(v_data_4639_, 1, v___x_4637_);
lean_ctor_set(v_data_4639_, 2, v_tag_4599_);
lean_ctor_set_float(v_data_4639_, sizeof(void*)*3, v___x_4638_);
lean_ctor_set_float(v_data_4639_, sizeof(void*)*3 + 8, v___x_4638_);
lean_ctor_set_uint8(v_data_4639_, sizeof(void*)*3 + 16, v_collapsed_4598_);
if (v___x_4631_ == 0)
{
lean_dec_ref_known(v___x_4637_, 1);
lean_dec(v_snd_4629_);
lean_dec(v_fst_4628_);
lean_dec_ref(v_tag_4599_);
lean_dec(v_cls_4597_);
v___y_4615_ = v___y_4633_;
v___y_4616_ = v_a_4634_;
v_data_4617_ = v_data_4639_;
goto v___jp_4614_;
}
else
{
lean_object* v_data_4640_; double v___x_4641_; double v___x_4642_; 
lean_dec_ref_known(v_data_4639_, 3);
v_data_4640_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4640_, 0, v_cls_4597_);
lean_ctor_set(v_data_4640_, 1, v___x_4637_);
lean_ctor_set(v_data_4640_, 2, v_tag_4599_);
v___x_4641_ = lean_unbox_float(v_fst_4628_);
lean_dec(v_fst_4628_);
lean_ctor_set_float(v_data_4640_, sizeof(void*)*3, v___x_4641_);
v___x_4642_ = lean_unbox_float(v_snd_4629_);
lean_dec(v_snd_4629_);
lean_ctor_set_float(v_data_4640_, sizeof(void*)*3 + 8, v___x_4642_);
lean_ctor_set_uint8(v_data_4640_, sizeof(void*)*3 + 16, v_collapsed_4598_);
v___y_4615_ = v___y_4633_;
v___y_4616_ = v_a_4634_;
v_data_4617_ = v_data_4640_;
goto v___jp_4614_;
}
}
v___jp_4643_:
{
lean_object* v_ref_4644_; lean_object* v___x_4645_; 
v_ref_4644_ = lean_ctor_get(v___y_4609_, 5);
lean_inc(v___y_4610_);
lean_inc_ref(v___y_4609_);
lean_inc(v___y_4608_);
lean_inc_ref(v___y_4607_);
lean_inc(v___y_4606_);
lean_inc_ref(v___y_4605_);
lean_inc(v_fst_4612_);
v___x_4645_ = lean_apply_8(v_msg_4603_, v_fst_4612_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_, lean_box(0));
if (lean_obj_tag(v___x_4645_) == 0)
{
lean_object* v_a_4646_; 
v_a_4646_ = lean_ctor_get(v___x_4645_, 0);
lean_inc(v_a_4646_);
lean_dec_ref_known(v___x_4645_, 1);
v___y_4633_ = v_ref_4644_;
v_a_4634_ = v_a_4646_;
goto v___jp_4632_;
}
else
{
lean_object* v___x_4647_; 
lean_dec_ref_known(v___x_4645_, 1);
v___x_4647_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
v___y_4633_ = v_ref_4644_;
v_a_4634_ = v___x_4647_;
goto v___jp_4632_;
}
}
v___jp_4648_:
{
if (v_clsEnabled_4601_ == 0)
{
if (v___y_4649_ == 0)
{
lean_object* v___x_4650_; lean_object* v_traceState_4651_; lean_object* v_env_4652_; lean_object* v_nextMacroScope_4653_; lean_object* v_ngen_4654_; lean_object* v_auxDeclNGen_4655_; lean_object* v_cache_4656_; lean_object* v_messages_4657_; lean_object* v_infoState_4658_; lean_object* v_snapshotTasks_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4678_; 
lean_dec(v_snd_4629_);
lean_dec(v_fst_4628_);
lean_dec_ref(v_msg_4603_);
lean_dec_ref(v_tag_4599_);
lean_dec(v_cls_4597_);
v___x_4650_ = lean_st_ref_take(v___y_4610_);
v_traceState_4651_ = lean_ctor_get(v___x_4650_, 4);
v_env_4652_ = lean_ctor_get(v___x_4650_, 0);
v_nextMacroScope_4653_ = lean_ctor_get(v___x_4650_, 1);
v_ngen_4654_ = lean_ctor_get(v___x_4650_, 2);
v_auxDeclNGen_4655_ = lean_ctor_get(v___x_4650_, 3);
v_cache_4656_ = lean_ctor_get(v___x_4650_, 5);
v_messages_4657_ = lean_ctor_get(v___x_4650_, 6);
v_infoState_4658_ = lean_ctor_get(v___x_4650_, 7);
v_snapshotTasks_4659_ = lean_ctor_get(v___x_4650_, 8);
v_isSharedCheck_4678_ = !lean_is_exclusive(v___x_4650_);
if (v_isSharedCheck_4678_ == 0)
{
v___x_4661_ = v___x_4650_;
v_isShared_4662_ = v_isSharedCheck_4678_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_snapshotTasks_4659_);
lean_inc(v_infoState_4658_);
lean_inc(v_messages_4657_);
lean_inc(v_cache_4656_);
lean_inc(v_traceState_4651_);
lean_inc(v_auxDeclNGen_4655_);
lean_inc(v_ngen_4654_);
lean_inc(v_nextMacroScope_4653_);
lean_inc(v_env_4652_);
lean_dec(v___x_4650_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4678_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
uint64_t v_tid_4663_; lean_object* v_traces_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4677_; 
v_tid_4663_ = lean_ctor_get_uint64(v_traceState_4651_, sizeof(void*)*1);
v_traces_4664_ = lean_ctor_get(v_traceState_4651_, 0);
v_isSharedCheck_4677_ = !lean_is_exclusive(v_traceState_4651_);
if (v_isSharedCheck_4677_ == 0)
{
v___x_4666_ = v_traceState_4651_;
v_isShared_4667_ = v_isSharedCheck_4677_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_traces_4664_);
lean_dec(v_traceState_4651_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4677_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v___x_4668_; lean_object* v___x_4670_; 
v___x_4668_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4602_, v_traces_4664_);
lean_dec_ref(v_traces_4664_);
if (v_isShared_4667_ == 0)
{
lean_ctor_set(v___x_4666_, 0, v___x_4668_);
v___x_4670_ = v___x_4666_;
goto v_reusejp_4669_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v___x_4668_);
lean_ctor_set_uint64(v_reuseFailAlloc_4676_, sizeof(void*)*1, v_tid_4663_);
v___x_4670_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4669_;
}
v_reusejp_4669_:
{
lean_object* v___x_4672_; 
if (v_isShared_4662_ == 0)
{
lean_ctor_set(v___x_4661_, 4, v___x_4670_);
v___x_4672_ = v___x_4661_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v_env_4652_);
lean_ctor_set(v_reuseFailAlloc_4675_, 1, v_nextMacroScope_4653_);
lean_ctor_set(v_reuseFailAlloc_4675_, 2, v_ngen_4654_);
lean_ctor_set(v_reuseFailAlloc_4675_, 3, v_auxDeclNGen_4655_);
lean_ctor_set(v_reuseFailAlloc_4675_, 4, v___x_4670_);
lean_ctor_set(v_reuseFailAlloc_4675_, 5, v_cache_4656_);
lean_ctor_set(v_reuseFailAlloc_4675_, 6, v_messages_4657_);
lean_ctor_set(v_reuseFailAlloc_4675_, 7, v_infoState_4658_);
lean_ctor_set(v_reuseFailAlloc_4675_, 8, v_snapshotTasks_4659_);
v___x_4672_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___x_4673_ = lean_st_ref_set(v___y_4610_, v___x_4672_);
v___x_4674_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(v_fst_4612_);
return v___x_4674_;
}
}
}
}
}
else
{
goto v___jp_4643_;
}
}
else
{
goto v___jp_4643_;
}
}
v___jp_4679_:
{
double v___x_4681_; double v___x_4682_; double v___x_4683_; uint8_t v___x_4684_; 
v___x_4681_ = lean_unbox_float(v_snd_4629_);
v___x_4682_ = lean_unbox_float(v_fst_4628_);
v___x_4683_ = lean_float_sub(v___x_4681_, v___x_4682_);
v___x_4684_ = lean_float_decLt(v___y_4680_, v___x_4683_);
v___y_4649_ = v___x_4684_;
goto v___jp_4648_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2___boxed(lean_object* v_cls_4695_, lean_object* v_collapsed_4696_, lean_object* v_tag_4697_, lean_object* v_opts_4698_, lean_object* v_clsEnabled_4699_, lean_object* v_oldTraces_4700_, lean_object* v_msg_4701_, lean_object* v_resStartStop_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_){
_start:
{
uint8_t v_collapsed_boxed_4710_; uint8_t v_clsEnabled_boxed_4711_; lean_object* v_res_4712_; 
v_collapsed_boxed_4710_ = lean_unbox(v_collapsed_4696_);
v_clsEnabled_boxed_4711_ = lean_unbox(v_clsEnabled_4699_);
v_res_4712_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v_cls_4695_, v_collapsed_boxed_4710_, v_tag_4697_, v_opts_4698_, v_clsEnabled_boxed_4711_, v_oldTraces_4700_, v_msg_4701_, v_resStartStop_4702_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_);
lean_dec(v___y_4708_);
lean_dec_ref(v___y_4707_);
lean_dec(v___y_4706_);
lean_dec_ref(v___y_4705_);
lean_dec(v___y_4704_);
lean_dec_ref(v___y_4703_);
lean_dec_ref(v_opts_4698_);
return v_res_4712_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4714_; lean_object* v___x_4715_; 
v___x_4714_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__0));
v___x_4715_ = l_Lean_stringToMessageData(v___x_4714_);
return v___x_4715_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4717_; lean_object* v___x_4718_; 
v___x_4717_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__2));
v___x_4718_ = l_Lean_stringToMessageData(v___x_4717_);
return v___x_4718_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4720_; lean_object* v___x_4721_; 
v___x_4720_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__4));
v___x_4721_ = l_Lean_stringToMessageData(v___x_4720_);
return v___x_4721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0(lean_object* v_a_4722_, lean_object* v___x_4723_, lean_object* v_x_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_, lean_object* v___y_4730_){
_start:
{
if (lean_obj_tag(v_x_4724_) == 0)
{
lean_object* v_a_4732_; lean_object* v___x_4734_; uint8_t v_isShared_4735_; uint8_t v_isSharedCheck_4747_; 
lean_dec_ref(v___x_4723_);
v_a_4732_ = lean_ctor_get(v_x_4724_, 0);
v_isSharedCheck_4747_ = !lean_is_exclusive(v_x_4724_);
if (v_isSharedCheck_4747_ == 0)
{
v___x_4734_ = v_x_4724_;
v_isShared_4735_ = v_isSharedCheck_4747_;
goto v_resetjp_4733_;
}
else
{
lean_inc(v_a_4732_);
lean_dec(v_x_4724_);
v___x_4734_ = lean_box(0);
v_isShared_4735_ = v_isSharedCheck_4747_;
goto v_resetjp_4733_;
}
v_resetjp_4733_:
{
lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4745_; 
v___x_4736_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1);
v___x_4737_ = l_Lean_LocalDecl_userName(v_a_4722_);
v___x_4738_ = l_Lean_MessageData_ofName(v___x_4737_);
v___x_4739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4739_, 0, v___x_4736_);
lean_ctor_set(v___x_4739_, 1, v___x_4738_);
v___x_4740_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3);
v___x_4741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4741_, 0, v___x_4739_);
lean_ctor_set(v___x_4741_, 1, v___x_4740_);
v___x_4742_ = l_Lean_Exception_toMessageData(v_a_4732_);
v___x_4743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4743_, 0, v___x_4741_);
lean_ctor_set(v___x_4743_, 1, v___x_4742_);
if (v_isShared_4735_ == 0)
{
lean_ctor_set(v___x_4734_, 0, v___x_4743_);
v___x_4745_ = v___x_4734_;
goto v_reusejp_4744_;
}
else
{
lean_object* v_reuseFailAlloc_4746_; 
v_reuseFailAlloc_4746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4746_, 0, v___x_4743_);
v___x_4745_ = v_reuseFailAlloc_4746_;
goto v_reusejp_4744_;
}
v_reusejp_4744_:
{
return v___x_4745_;
}
}
}
else
{
lean_object* v_a_4748_; lean_object* v___x_4750_; uint8_t v_isShared_4751_; uint8_t v_isSharedCheck_4777_; 
v_a_4748_ = lean_ctor_get(v_x_4724_, 0);
v_isSharedCheck_4777_ = !lean_is_exclusive(v_x_4724_);
if (v_isSharedCheck_4777_ == 0)
{
v___x_4750_ = v_x_4724_;
v_isShared_4751_ = v_isSharedCheck_4777_;
goto v_resetjp_4749_;
}
else
{
lean_inc(v_a_4748_);
lean_dec(v_x_4724_);
v___x_4750_ = lean_box(0);
v_isShared_4751_ = v_isSharedCheck_4777_;
goto v_resetjp_4749_;
}
v_resetjp_4749_:
{
if (lean_obj_tag(v_a_4748_) == 0)
{
lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4759_; 
lean_dec_ref_known(v_a_4748_, 0);
lean_dec_ref(v___x_4723_);
v___x_4752_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1);
v___x_4753_ = l_Lean_LocalDecl_userName(v_a_4722_);
v___x_4754_ = l_Lean_MessageData_ofName(v___x_4753_);
v___x_4755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4755_, 0, v___x_4752_);
lean_ctor_set(v___x_4755_, 1, v___x_4754_);
v___x_4756_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5);
v___x_4757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4757_, 0, v___x_4755_);
lean_ctor_set(v___x_4757_, 1, v___x_4756_);
if (v_isShared_4751_ == 0)
{
lean_ctor_set_tag(v___x_4750_, 0);
lean_ctor_set(v___x_4750_, 0, v___x_4757_);
v___x_4759_ = v___x_4750_;
goto v_reusejp_4758_;
}
else
{
lean_object* v_reuseFailAlloc_4760_; 
v_reuseFailAlloc_4760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4760_, 0, v___x_4757_);
v___x_4759_ = v_reuseFailAlloc_4760_;
goto v_reusejp_4758_;
}
v_reusejp_4758_:
{
return v___x_4759_;
}
}
else
{
lean_object* v_e_x27_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4775_; 
v_e_x27_4761_ = lean_ctor_get(v_a_4748_, 0);
lean_inc_ref(v_e_x27_4761_);
lean_dec_ref_known(v_a_4748_, 2);
v___x_4762_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1);
v___x_4763_ = l_Lean_LocalDecl_userName(v_a_4722_);
v___x_4764_ = l_Lean_MessageData_ofName(v___x_4763_);
v___x_4765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4765_, 0, v___x_4762_);
lean_ctor_set(v___x_4765_, 1, v___x_4764_);
v___x_4766_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8);
v___x_4767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4767_, 0, v___x_4765_);
lean_ctor_set(v___x_4767_, 1, v___x_4766_);
v___x_4768_ = l_Lean_indentExpr(v___x_4723_);
v___x_4769_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4769_, 0, v___x_4767_);
lean_ctor_set(v___x_4769_, 1, v___x_4768_);
v___x_4770_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_4771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4771_, 0, v___x_4769_);
lean_ctor_set(v___x_4771_, 1, v___x_4770_);
v___x_4772_ = l_Lean_indentExpr(v_e_x27_4761_);
v___x_4773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4773_, 0, v___x_4771_);
lean_ctor_set(v___x_4773_, 1, v___x_4772_);
if (v_isShared_4751_ == 0)
{
lean_ctor_set_tag(v___x_4750_, 0);
lean_ctor_set(v___x_4750_, 0, v___x_4773_);
v___x_4775_ = v___x_4750_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4776_; 
v_reuseFailAlloc_4776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4776_, 0, v___x_4773_);
v___x_4775_ = v_reuseFailAlloc_4776_;
goto v_reusejp_4774_;
}
v_reusejp_4774_:
{
return v___x_4775_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___boxed(lean_object* v_a_4778_, lean_object* v___x_4779_, lean_object* v_x_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_){
_start:
{
lean_object* v_res_4788_; 
v_res_4788_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0(v_a_4778_, v___x_4779_, v_x_4780_, v___y_4781_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_);
lean_dec(v___y_4786_);
lean_dec_ref(v___y_4785_);
lean_dec(v___y_4784_);
lean_dec_ref(v___y_4783_);
lean_dec(v___y_4782_);
lean_dec_ref(v___y_4781_);
lean_dec_ref(v_a_4778_);
return v_res_4788_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(lean_object* v_x_4789_, lean_object* v_x_4790_, lean_object* v_x_4791_, lean_object* v_x_4792_){
_start:
{
lean_object* v_ks_4793_; lean_object* v_vs_4794_; lean_object* v___x_4796_; uint8_t v_isShared_4797_; uint8_t v_isSharedCheck_4818_; 
v_ks_4793_ = lean_ctor_get(v_x_4789_, 0);
v_vs_4794_ = lean_ctor_get(v_x_4789_, 1);
v_isSharedCheck_4818_ = !lean_is_exclusive(v_x_4789_);
if (v_isSharedCheck_4818_ == 0)
{
v___x_4796_ = v_x_4789_;
v_isShared_4797_ = v_isSharedCheck_4818_;
goto v_resetjp_4795_;
}
else
{
lean_inc(v_vs_4794_);
lean_inc(v_ks_4793_);
lean_dec(v_x_4789_);
v___x_4796_ = lean_box(0);
v_isShared_4797_ = v_isSharedCheck_4818_;
goto v_resetjp_4795_;
}
v_resetjp_4795_:
{
lean_object* v___x_4798_; uint8_t v___x_4799_; 
v___x_4798_ = lean_array_get_size(v_ks_4793_);
v___x_4799_ = lean_nat_dec_lt(v_x_4790_, v___x_4798_);
if (v___x_4799_ == 0)
{
lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v___x_4803_; 
lean_dec(v_x_4790_);
v___x_4800_ = lean_array_push(v_ks_4793_, v_x_4791_);
v___x_4801_ = lean_array_push(v_vs_4794_, v_x_4792_);
if (v_isShared_4797_ == 0)
{
lean_ctor_set(v___x_4796_, 1, v___x_4801_);
lean_ctor_set(v___x_4796_, 0, v___x_4800_);
v___x_4803_ = v___x_4796_;
goto v_reusejp_4802_;
}
else
{
lean_object* v_reuseFailAlloc_4804_; 
v_reuseFailAlloc_4804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4804_, 0, v___x_4800_);
lean_ctor_set(v_reuseFailAlloc_4804_, 1, v___x_4801_);
v___x_4803_ = v_reuseFailAlloc_4804_;
goto v_reusejp_4802_;
}
v_reusejp_4802_:
{
return v___x_4803_;
}
}
else
{
lean_object* v_k_x27_4805_; uint8_t v___x_4806_; 
v_k_x27_4805_ = lean_array_fget_borrowed(v_ks_4793_, v_x_4790_);
v___x_4806_ = l_Lean_instBEqMVarId_beq(v_x_4791_, v_k_x27_4805_);
if (v___x_4806_ == 0)
{
lean_object* v___x_4808_; 
if (v_isShared_4797_ == 0)
{
v___x_4808_ = v___x_4796_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v_ks_4793_);
lean_ctor_set(v_reuseFailAlloc_4812_, 1, v_vs_4794_);
v___x_4808_ = v_reuseFailAlloc_4812_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
lean_object* v___x_4809_; lean_object* v___x_4810_; 
v___x_4809_ = lean_unsigned_to_nat(1u);
v___x_4810_ = lean_nat_add(v_x_4790_, v___x_4809_);
lean_dec(v_x_4790_);
v_x_4789_ = v___x_4808_;
v_x_4790_ = v___x_4810_;
goto _start;
}
}
else
{
lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v___x_4816_; 
v___x_4813_ = lean_array_fset(v_ks_4793_, v_x_4790_, v_x_4791_);
v___x_4814_ = lean_array_fset(v_vs_4794_, v_x_4790_, v_x_4792_);
lean_dec(v_x_4790_);
if (v_isShared_4797_ == 0)
{
lean_ctor_set(v___x_4796_, 1, v___x_4814_);
lean_ctor_set(v___x_4796_, 0, v___x_4813_);
v___x_4816_ = v___x_4796_;
goto v_reusejp_4815_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v___x_4813_);
lean_ctor_set(v_reuseFailAlloc_4817_, 1, v___x_4814_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_n_4819_, lean_object* v_k_4820_, lean_object* v_v_4821_){
_start:
{
lean_object* v___x_4822_; lean_object* v___x_4823_; 
v___x_4822_ = lean_unsigned_to_nat(0u);
v___x_4823_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_n_4819_, v___x_4822_, v_k_4820_, v_v_4821_);
return v___x_4823_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_4824_; 
v___x_4824_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4824_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(lean_object* v_x_4825_, size_t v_x_4826_, size_t v_x_4827_, lean_object* v_x_4828_, lean_object* v_x_4829_){
_start:
{
if (lean_obj_tag(v_x_4825_) == 0)
{
lean_object* v_es_4830_; size_t v___x_4831_; size_t v___x_4832_; lean_object* v_j_4833_; lean_object* v___x_4834_; uint8_t v___x_4835_; 
v_es_4830_ = lean_ctor_get(v_x_4825_, 0);
v___x_4831_ = ((size_t)31ULL);
v___x_4832_ = lean_usize_land(v_x_4826_, v___x_4831_);
v_j_4833_ = lean_usize_to_nat(v___x_4832_);
v___x_4834_ = lean_array_get_size(v_es_4830_);
v___x_4835_ = lean_nat_dec_lt(v_j_4833_, v___x_4834_);
if (v___x_4835_ == 0)
{
lean_dec(v_j_4833_);
lean_dec(v_x_4829_);
lean_dec(v_x_4828_);
return v_x_4825_;
}
else
{
lean_object* v___x_4837_; uint8_t v_isShared_4838_; uint8_t v_isSharedCheck_4874_; 
lean_inc_ref(v_es_4830_);
v_isSharedCheck_4874_ = !lean_is_exclusive(v_x_4825_);
if (v_isSharedCheck_4874_ == 0)
{
lean_object* v_unused_4875_; 
v_unused_4875_ = lean_ctor_get(v_x_4825_, 0);
lean_dec(v_unused_4875_);
v___x_4837_ = v_x_4825_;
v_isShared_4838_ = v_isSharedCheck_4874_;
goto v_resetjp_4836_;
}
else
{
lean_dec(v_x_4825_);
v___x_4837_ = lean_box(0);
v_isShared_4838_ = v_isSharedCheck_4874_;
goto v_resetjp_4836_;
}
v_resetjp_4836_:
{
lean_object* v_v_4839_; lean_object* v___x_4840_; lean_object* v_xs_x27_4841_; lean_object* v___y_4843_; 
v_v_4839_ = lean_array_fget(v_es_4830_, v_j_4833_);
v___x_4840_ = lean_box(0);
v_xs_x27_4841_ = lean_array_fset(v_es_4830_, v_j_4833_, v___x_4840_);
switch(lean_obj_tag(v_v_4839_))
{
case 0:
{
lean_object* v_key_4848_; lean_object* v_val_4849_; lean_object* v___x_4851_; uint8_t v_isShared_4852_; uint8_t v_isSharedCheck_4859_; 
v_key_4848_ = lean_ctor_get(v_v_4839_, 0);
v_val_4849_ = lean_ctor_get(v_v_4839_, 1);
v_isSharedCheck_4859_ = !lean_is_exclusive(v_v_4839_);
if (v_isSharedCheck_4859_ == 0)
{
v___x_4851_ = v_v_4839_;
v_isShared_4852_ = v_isSharedCheck_4859_;
goto v_resetjp_4850_;
}
else
{
lean_inc(v_val_4849_);
lean_inc(v_key_4848_);
lean_dec(v_v_4839_);
v___x_4851_ = lean_box(0);
v_isShared_4852_ = v_isSharedCheck_4859_;
goto v_resetjp_4850_;
}
v_resetjp_4850_:
{
uint8_t v___x_4853_; 
v___x_4853_ = l_Lean_instBEqMVarId_beq(v_x_4828_, v_key_4848_);
if (v___x_4853_ == 0)
{
lean_object* v___x_4854_; lean_object* v___x_4855_; 
lean_del_object(v___x_4851_);
v___x_4854_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4848_, v_val_4849_, v_x_4828_, v_x_4829_);
v___x_4855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4855_, 0, v___x_4854_);
v___y_4843_ = v___x_4855_;
goto v___jp_4842_;
}
else
{
lean_object* v___x_4857_; 
lean_dec(v_val_4849_);
lean_dec(v_key_4848_);
if (v_isShared_4852_ == 0)
{
lean_ctor_set(v___x_4851_, 1, v_x_4829_);
lean_ctor_set(v___x_4851_, 0, v_x_4828_);
v___x_4857_ = v___x_4851_;
goto v_reusejp_4856_;
}
else
{
lean_object* v_reuseFailAlloc_4858_; 
v_reuseFailAlloc_4858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_x_4828_);
lean_ctor_set(v_reuseFailAlloc_4858_, 1, v_x_4829_);
v___x_4857_ = v_reuseFailAlloc_4858_;
goto v_reusejp_4856_;
}
v_reusejp_4856_:
{
v___y_4843_ = v___x_4857_;
goto v___jp_4842_;
}
}
}
}
case 1:
{
lean_object* v_node_4860_; lean_object* v___x_4862_; uint8_t v_isShared_4863_; uint8_t v_isSharedCheck_4872_; 
v_node_4860_ = lean_ctor_get(v_v_4839_, 0);
v_isSharedCheck_4872_ = !lean_is_exclusive(v_v_4839_);
if (v_isSharedCheck_4872_ == 0)
{
v___x_4862_ = v_v_4839_;
v_isShared_4863_ = v_isSharedCheck_4872_;
goto v_resetjp_4861_;
}
else
{
lean_inc(v_node_4860_);
lean_dec(v_v_4839_);
v___x_4862_ = lean_box(0);
v_isShared_4863_ = v_isSharedCheck_4872_;
goto v_resetjp_4861_;
}
v_resetjp_4861_:
{
size_t v___x_4864_; size_t v___x_4865_; size_t v___x_4866_; size_t v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4870_; 
v___x_4864_ = ((size_t)5ULL);
v___x_4865_ = lean_usize_shift_right(v_x_4826_, v___x_4864_);
v___x_4866_ = ((size_t)1ULL);
v___x_4867_ = lean_usize_add(v_x_4827_, v___x_4866_);
v___x_4868_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_node_4860_, v___x_4865_, v___x_4867_, v_x_4828_, v_x_4829_);
if (v_isShared_4863_ == 0)
{
lean_ctor_set(v___x_4862_, 0, v___x_4868_);
v___x_4870_ = v___x_4862_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4871_; 
v_reuseFailAlloc_4871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4871_, 0, v___x_4868_);
v___x_4870_ = v_reuseFailAlloc_4871_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
v___y_4843_ = v___x_4870_;
goto v___jp_4842_;
}
}
}
default: 
{
lean_object* v___x_4873_; 
v___x_4873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4873_, 0, v_x_4828_);
lean_ctor_set(v___x_4873_, 1, v_x_4829_);
v___y_4843_ = v___x_4873_;
goto v___jp_4842_;
}
}
v___jp_4842_:
{
lean_object* v___x_4844_; lean_object* v___x_4846_; 
v___x_4844_ = lean_array_fset(v_xs_x27_4841_, v_j_4833_, v___y_4843_);
lean_dec(v_j_4833_);
if (v_isShared_4838_ == 0)
{
lean_ctor_set(v___x_4837_, 0, v___x_4844_);
v___x_4846_ = v___x_4837_;
goto v_reusejp_4845_;
}
else
{
lean_object* v_reuseFailAlloc_4847_; 
v_reuseFailAlloc_4847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4847_, 0, v___x_4844_);
v___x_4846_ = v_reuseFailAlloc_4847_;
goto v_reusejp_4845_;
}
v_reusejp_4845_:
{
return v___x_4846_;
}
}
}
}
}
else
{
lean_object* v_ks_4876_; lean_object* v_vs_4877_; lean_object* v___x_4879_; uint8_t v_isShared_4880_; uint8_t v_isSharedCheck_4897_; 
v_ks_4876_ = lean_ctor_get(v_x_4825_, 0);
v_vs_4877_ = lean_ctor_get(v_x_4825_, 1);
v_isSharedCheck_4897_ = !lean_is_exclusive(v_x_4825_);
if (v_isSharedCheck_4897_ == 0)
{
v___x_4879_ = v_x_4825_;
v_isShared_4880_ = v_isSharedCheck_4897_;
goto v_resetjp_4878_;
}
else
{
lean_inc(v_vs_4877_);
lean_inc(v_ks_4876_);
lean_dec(v_x_4825_);
v___x_4879_ = lean_box(0);
v_isShared_4880_ = v_isSharedCheck_4897_;
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
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v_ks_4876_);
lean_ctor_set(v_reuseFailAlloc_4896_, 1, v_vs_4877_);
v___x_4882_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
lean_object* v_newNode_4883_; uint8_t v___y_4885_; size_t v___x_4891_; uint8_t v___x_4892_; 
v_newNode_4883_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7___redArg(v___x_4882_, v_x_4828_, v_x_4829_);
v___x_4891_ = ((size_t)7ULL);
v___x_4892_ = lean_usize_dec_le(v___x_4891_, v_x_4827_);
if (v___x_4892_ == 0)
{
lean_object* v___x_4893_; lean_object* v___x_4894_; uint8_t v___x_4895_; 
v___x_4893_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4883_);
v___x_4894_ = lean_unsigned_to_nat(4u);
v___x_4895_ = lean_nat_dec_lt(v___x_4893_, v___x_4894_);
lean_dec(v___x_4893_);
v___y_4885_ = v___x_4895_;
goto v___jp_4884_;
}
else
{
v___y_4885_ = v___x_4892_;
goto v___jp_4884_;
}
v___jp_4884_:
{
if (v___y_4885_ == 0)
{
lean_object* v_ks_4886_; lean_object* v_vs_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; 
v_ks_4886_ = lean_ctor_get(v_newNode_4883_, 0);
lean_inc_ref(v_ks_4886_);
v_vs_4887_ = lean_ctor_get(v_newNode_4883_, 1);
lean_inc_ref(v_vs_4887_);
lean_dec_ref(v_newNode_4883_);
v___x_4888_ = lean_unsigned_to_nat(0u);
v___x_4889_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_4890_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg(v_x_4827_, v_ks_4886_, v_vs_4887_, v___x_4888_, v___x_4889_);
lean_dec_ref(v_vs_4887_);
lean_dec_ref(v_ks_4886_);
return v___x_4890_;
}
else
{
return v_newNode_4883_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg(size_t v_depth_4898_, lean_object* v_keys_4899_, lean_object* v_vals_4900_, lean_object* v_i_4901_, lean_object* v_entries_4902_){
_start:
{
lean_object* v___x_4903_; uint8_t v___x_4904_; 
v___x_4903_ = lean_array_get_size(v_keys_4899_);
v___x_4904_ = lean_nat_dec_lt(v_i_4901_, v___x_4903_);
if (v___x_4904_ == 0)
{
lean_dec(v_i_4901_);
return v_entries_4902_;
}
else
{
lean_object* v_k_4905_; lean_object* v_v_4906_; uint64_t v___x_4907_; size_t v_h_4908_; size_t v___x_4909_; lean_object* v___x_4910_; size_t v___x_4911_; size_t v___x_4912_; size_t v___x_4913_; size_t v_h_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; 
v_k_4905_ = lean_array_fget_borrowed(v_keys_4899_, v_i_4901_);
v_v_4906_ = lean_array_fget_borrowed(v_vals_4900_, v_i_4901_);
v___x_4907_ = l_Lean_instHashableMVarId_hash(v_k_4905_);
v_h_4908_ = lean_uint64_to_usize(v___x_4907_);
v___x_4909_ = ((size_t)5ULL);
v___x_4910_ = lean_unsigned_to_nat(1u);
v___x_4911_ = ((size_t)1ULL);
v___x_4912_ = lean_usize_sub(v_depth_4898_, v___x_4911_);
v___x_4913_ = lean_usize_mul(v___x_4909_, v___x_4912_);
v_h_4914_ = lean_usize_shift_right(v_h_4908_, v___x_4913_);
v___x_4915_ = lean_nat_add(v_i_4901_, v___x_4910_);
lean_dec(v_i_4901_);
lean_inc(v_v_4906_);
lean_inc(v_k_4905_);
v___x_4916_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_entries_4902_, v_h_4914_, v_depth_4898_, v_k_4905_, v_v_4906_);
v_i_4901_ = v___x_4915_;
v_entries_4902_ = v___x_4916_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object* v_depth_4918_, lean_object* v_keys_4919_, lean_object* v_vals_4920_, lean_object* v_i_4921_, lean_object* v_entries_4922_){
_start:
{
size_t v_depth_boxed_4923_; lean_object* v_res_4924_; 
v_depth_boxed_4923_ = lean_unbox_usize(v_depth_4918_);
lean_dec(v_depth_4918_);
v_res_4924_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg(v_depth_boxed_4923_, v_keys_4919_, v_vals_4920_, v_i_4921_, v_entries_4922_);
lean_dec_ref(v_vals_4920_);
lean_dec_ref(v_keys_4919_);
return v_res_4924_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_x_4925_, lean_object* v_x_4926_, lean_object* v_x_4927_, lean_object* v_x_4928_, lean_object* v_x_4929_){
_start:
{
size_t v_x_52796__boxed_4930_; size_t v_x_52797__boxed_4931_; lean_object* v_res_4932_; 
v_x_52796__boxed_4930_ = lean_unbox_usize(v_x_4926_);
lean_dec(v_x_4926_);
v_x_52797__boxed_4931_ = lean_unbox_usize(v_x_4927_);
lean_dec(v_x_4927_);
v_res_4932_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_x_4925_, v_x_52796__boxed_4930_, v_x_52797__boxed_4931_, v_x_4928_, v_x_4929_);
return v_res_4932_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0___redArg(lean_object* v_x_4933_, lean_object* v_x_4934_, lean_object* v_x_4935_){
_start:
{
uint64_t v___x_4936_; size_t v___x_4937_; size_t v___x_4938_; lean_object* v___x_4939_; 
v___x_4936_ = l_Lean_instHashableMVarId_hash(v_x_4934_);
v___x_4937_ = lean_uint64_to_usize(v___x_4936_);
v___x_4938_ = ((size_t)1ULL);
v___x_4939_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_x_4933_, v___x_4937_, v___x_4938_, v_x_4934_, v_x_4935_);
return v___x_4939_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(lean_object* v_mvarId_4940_, lean_object* v_val_4941_, lean_object* v___y_4942_){
_start:
{
lean_object* v___x_4944_; lean_object* v_mctx_4945_; lean_object* v_cache_4946_; lean_object* v_zetaDeltaFVarIds_4947_; lean_object* v_postponed_4948_; lean_object* v_diag_4949_; lean_object* v___x_4951_; uint8_t v_isShared_4952_; uint8_t v_isSharedCheck_4977_; 
v___x_4944_ = lean_st_ref_take(v___y_4942_);
v_mctx_4945_ = lean_ctor_get(v___x_4944_, 0);
v_cache_4946_ = lean_ctor_get(v___x_4944_, 1);
v_zetaDeltaFVarIds_4947_ = lean_ctor_get(v___x_4944_, 2);
v_postponed_4948_ = lean_ctor_get(v___x_4944_, 3);
v_diag_4949_ = lean_ctor_get(v___x_4944_, 4);
v_isSharedCheck_4977_ = !lean_is_exclusive(v___x_4944_);
if (v_isSharedCheck_4977_ == 0)
{
v___x_4951_ = v___x_4944_;
v_isShared_4952_ = v_isSharedCheck_4977_;
goto v_resetjp_4950_;
}
else
{
lean_inc(v_diag_4949_);
lean_inc(v_postponed_4948_);
lean_inc(v_zetaDeltaFVarIds_4947_);
lean_inc(v_cache_4946_);
lean_inc(v_mctx_4945_);
lean_dec(v___x_4944_);
v___x_4951_ = lean_box(0);
v_isShared_4952_ = v_isSharedCheck_4977_;
goto v_resetjp_4950_;
}
v_resetjp_4950_:
{
lean_object* v_depth_4953_; lean_object* v_levelAssignDepth_4954_; lean_object* v_lmvarCounter_4955_; lean_object* v_mvarCounter_4956_; lean_object* v_lDecls_4957_; lean_object* v_decls_4958_; lean_object* v_userNames_4959_; lean_object* v_lAssignment_4960_; lean_object* v_eAssignment_4961_; lean_object* v_dAssignment_4962_; lean_object* v___x_4964_; uint8_t v_isShared_4965_; uint8_t v_isSharedCheck_4976_; 
v_depth_4953_ = lean_ctor_get(v_mctx_4945_, 0);
v_levelAssignDepth_4954_ = lean_ctor_get(v_mctx_4945_, 1);
v_lmvarCounter_4955_ = lean_ctor_get(v_mctx_4945_, 2);
v_mvarCounter_4956_ = lean_ctor_get(v_mctx_4945_, 3);
v_lDecls_4957_ = lean_ctor_get(v_mctx_4945_, 4);
v_decls_4958_ = lean_ctor_get(v_mctx_4945_, 5);
v_userNames_4959_ = lean_ctor_get(v_mctx_4945_, 6);
v_lAssignment_4960_ = lean_ctor_get(v_mctx_4945_, 7);
v_eAssignment_4961_ = lean_ctor_get(v_mctx_4945_, 8);
v_dAssignment_4962_ = lean_ctor_get(v_mctx_4945_, 9);
v_isSharedCheck_4976_ = !lean_is_exclusive(v_mctx_4945_);
if (v_isSharedCheck_4976_ == 0)
{
v___x_4964_ = v_mctx_4945_;
v_isShared_4965_ = v_isSharedCheck_4976_;
goto v_resetjp_4963_;
}
else
{
lean_inc(v_dAssignment_4962_);
lean_inc(v_eAssignment_4961_);
lean_inc(v_lAssignment_4960_);
lean_inc(v_userNames_4959_);
lean_inc(v_decls_4958_);
lean_inc(v_lDecls_4957_);
lean_inc(v_mvarCounter_4956_);
lean_inc(v_lmvarCounter_4955_);
lean_inc(v_levelAssignDepth_4954_);
lean_inc(v_depth_4953_);
lean_dec(v_mctx_4945_);
v___x_4964_ = lean_box(0);
v_isShared_4965_ = v_isSharedCheck_4976_;
goto v_resetjp_4963_;
}
v_resetjp_4963_:
{
lean_object* v___x_4966_; lean_object* v___x_4968_; 
v___x_4966_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0___redArg(v_eAssignment_4961_, v_mvarId_4940_, v_val_4941_);
if (v_isShared_4965_ == 0)
{
lean_ctor_set(v___x_4964_, 8, v___x_4966_);
v___x_4968_ = v___x_4964_;
goto v_reusejp_4967_;
}
else
{
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_depth_4953_);
lean_ctor_set(v_reuseFailAlloc_4975_, 1, v_levelAssignDepth_4954_);
lean_ctor_set(v_reuseFailAlloc_4975_, 2, v_lmvarCounter_4955_);
lean_ctor_set(v_reuseFailAlloc_4975_, 3, v_mvarCounter_4956_);
lean_ctor_set(v_reuseFailAlloc_4975_, 4, v_lDecls_4957_);
lean_ctor_set(v_reuseFailAlloc_4975_, 5, v_decls_4958_);
lean_ctor_set(v_reuseFailAlloc_4975_, 6, v_userNames_4959_);
lean_ctor_set(v_reuseFailAlloc_4975_, 7, v_lAssignment_4960_);
lean_ctor_set(v_reuseFailAlloc_4975_, 8, v___x_4966_);
lean_ctor_set(v_reuseFailAlloc_4975_, 9, v_dAssignment_4962_);
v___x_4968_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4967_;
}
v_reusejp_4967_:
{
lean_object* v___x_4970_; 
if (v_isShared_4952_ == 0)
{
lean_ctor_set(v___x_4951_, 0, v___x_4968_);
v___x_4970_ = v___x_4951_;
goto v_reusejp_4969_;
}
else
{
lean_object* v_reuseFailAlloc_4974_; 
v_reuseFailAlloc_4974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4974_, 0, v___x_4968_);
lean_ctor_set(v_reuseFailAlloc_4974_, 1, v_cache_4946_);
lean_ctor_set(v_reuseFailAlloc_4974_, 2, v_zetaDeltaFVarIds_4947_);
lean_ctor_set(v_reuseFailAlloc_4974_, 3, v_postponed_4948_);
lean_ctor_set(v_reuseFailAlloc_4974_, 4, v_diag_4949_);
v___x_4970_ = v_reuseFailAlloc_4974_;
goto v_reusejp_4969_;
}
v_reusejp_4969_:
{
lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v___x_4973_; 
v___x_4971_ = lean_st_ref_set(v___y_4942_, v___x_4970_);
v___x_4972_ = lean_box(0);
v___x_4973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4973_, 0, v___x_4972_);
return v___x_4973_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg___boxed(lean_object* v_mvarId_4978_, lean_object* v_val_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_){
_start:
{
lean_object* v_res_4982_; 
v_res_4982_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(v_mvarId_4978_, v_val_4979_, v___y_4980_);
lean_dec(v___y_4980_);
return v_res_4982_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3(lean_object* v_mvarId_4990_, lean_object* v___x_4991_, lean_object* v_as_4992_, size_t v_sz_4993_, size_t v_i_4994_, lean_object* v_b_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_){
_start:
{
lean_object* v_a_5004_; uint8_t v___x_5008_; 
v___x_5008_ = lean_usize_dec_lt(v_i_4994_, v_sz_4993_);
if (v___x_5008_ == 0)
{
lean_object* v___x_5009_; 
lean_dec_ref(v___x_4991_);
lean_dec(v_mvarId_4990_);
v___x_5009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5009_, 0, v_b_4995_);
return v___x_5009_;
}
else
{
lean_object* v_a_5010_; lean_object* v___x_5011_; 
v_a_5010_ = lean_array_uget_borrowed(v_as_4992_, v_i_4994_);
lean_inc(v_a_5010_);
v___x_5011_ = l_Lean_FVarId_getDecl___redArg(v_a_5010_, v___y_4998_, v___y_5000_, v___y_5001_);
if (lean_obj_tag(v___x_5011_) == 0)
{
lean_object* v_options_5012_; lean_object* v_a_5013_; lean_object* v_snd_5014_; lean_object* v___x_5016_; uint8_t v_isShared_5017_; uint8_t v_isSharedCheck_5205_; 
v_options_5012_ = lean_ctor_get(v___y_5000_, 2);
v_a_5013_ = lean_ctor_get(v___x_5011_, 0);
lean_inc(v_a_5013_);
lean_dec_ref_known(v___x_5011_, 1);
v_snd_5014_ = lean_ctor_get(v_b_4995_, 1);
v_isSharedCheck_5205_ = !lean_is_exclusive(v_b_4995_);
if (v_isSharedCheck_5205_ == 0)
{
lean_object* v_unused_5206_; 
v_unused_5206_ = lean_ctor_get(v_b_4995_, 0);
lean_dec(v_unused_5206_);
v___x_5016_ = v_b_4995_;
v_isShared_5017_ = v_isSharedCheck_5205_;
goto v_resetjp_5015_;
}
else
{
lean_inc(v_snd_5014_);
lean_dec(v_b_4995_);
v___x_5016_ = lean_box(0);
v_isShared_5017_ = v_isSharedCheck_5205_;
goto v_resetjp_5015_;
}
v_resetjp_5015_:
{
lean_object* v_inheritedTraceOptions_5018_; uint8_t v_hasTrace_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___y_5023_; 
v_inheritedTraceOptions_5018_ = lean_ctor_get(v___y_5000_, 13);
v_hasTrace_5019_ = lean_ctor_get_uint8(v_options_5012_, sizeof(void*)*1);
v___x_5020_ = lean_box(0);
v___x_5021_ = l_Lean_LocalDecl_type(v_a_5013_);
if (v_hasTrace_5019_ == 0)
{
lean_object* v___x_5120_; 
lean_inc_ref(v___x_4991_);
lean_inc_ref(v___x_5021_);
v___x_5120_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5021_, v___x_4991_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
v___y_5023_ = v___x_5120_;
goto v___jp_5022_;
}
else
{
lean_object* v___f_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; uint8_t v___x_5125_; lean_object* v___y_5127_; lean_object* v___y_5128_; lean_object* v_a_5129_; lean_object* v___y_5142_; lean_object* v___y_5143_; lean_object* v_a_5144_; 
lean_inc_ref(v___x_5021_);
lean_inc(v_a_5013_);
v___f_5121_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___boxed), 10, 2);
lean_closure_set(v___f_5121_, 0, v_a_5013_);
lean_closure_set(v___f_5121_, 1, v___x_5021_);
v___x_5122_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_5123_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_5124_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_5125_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5018_, v_options_5012_, v___x_5124_);
if (v___x_5125_ == 0)
{
lean_object* v___x_5202_; uint8_t v___x_5203_; 
v___x_5202_ = l_Lean_trace_profiler;
v___x_5203_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5012_, v___x_5202_);
if (v___x_5203_ == 0)
{
lean_object* v___x_5204_; 
lean_dec_ref(v___f_5121_);
lean_inc_ref(v___x_4991_);
lean_inc_ref(v___x_5021_);
v___x_5204_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5021_, v___x_4991_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
v___y_5023_ = v___x_5204_;
goto v___jp_5022_;
}
else
{
goto v___jp_5153_;
}
}
else
{
goto v___jp_5153_;
}
v___jp_5126_:
{
lean_object* v___x_5130_; double v___x_5131_; double v___x_5132_; double v___x_5133_; double v___x_5134_; double v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; 
v___x_5130_ = lean_io_mono_nanos_now();
v___x_5131_ = lean_float_of_nat(v___y_5128_);
v___x_5132_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_5133_ = lean_float_div(v___x_5131_, v___x_5132_);
v___x_5134_ = lean_float_of_nat(v___x_5130_);
v___x_5135_ = lean_float_div(v___x_5134_, v___x_5132_);
v___x_5136_ = lean_box_float(v___x_5133_);
v___x_5137_ = lean_box_float(v___x_5135_);
v___x_5138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5138_, 0, v___x_5136_);
lean_ctor_set(v___x_5138_, 1, v___x_5137_);
v___x_5139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5139_, 0, v_a_5129_);
lean_ctor_set(v___x_5139_, 1, v___x_5138_);
v___x_5140_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v___x_5122_, v_hasTrace_5019_, v___x_5123_, v_options_5012_, v___x_5125_, v___y_5127_, v___f_5121_, v___x_5139_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
v___y_5023_ = v___x_5140_;
goto v___jp_5022_;
}
v___jp_5141_:
{
lean_object* v___x_5145_; double v___x_5146_; double v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; 
v___x_5145_ = lean_io_get_num_heartbeats();
v___x_5146_ = lean_float_of_nat(v___y_5142_);
v___x_5147_ = lean_float_of_nat(v___x_5145_);
v___x_5148_ = lean_box_float(v___x_5146_);
v___x_5149_ = lean_box_float(v___x_5147_);
v___x_5150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5150_, 0, v___x_5148_);
lean_ctor_set(v___x_5150_, 1, v___x_5149_);
v___x_5151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5151_, 0, v_a_5144_);
lean_ctor_set(v___x_5151_, 1, v___x_5150_);
v___x_5152_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v___x_5122_, v_hasTrace_5019_, v___x_5123_, v_options_5012_, v___x_5125_, v___y_5143_, v___f_5121_, v___x_5151_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
v___y_5023_ = v___x_5152_;
goto v___jp_5022_;
}
v___jp_5153_:
{
lean_object* v___x_5154_; 
v___x_5154_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(v___y_5001_);
if (lean_obj_tag(v___x_5154_) == 0)
{
lean_object* v_a_5155_; lean_object* v___x_5156_; uint8_t v___x_5157_; 
v_a_5155_ = lean_ctor_get(v___x_5154_, 0);
lean_inc(v_a_5155_);
lean_dec_ref_known(v___x_5154_, 1);
v___x_5156_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5157_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5012_, v___x_5156_);
if (v___x_5157_ == 0)
{
lean_object* v___x_5158_; lean_object* v___x_5159_; 
v___x_5158_ = lean_io_mono_nanos_now();
lean_inc_ref(v___x_4991_);
lean_inc_ref(v___x_5021_);
v___x_5159_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5021_, v___x_4991_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
if (lean_obj_tag(v___x_5159_) == 0)
{
lean_object* v_a_5160_; lean_object* v___x_5162_; uint8_t v_isShared_5163_; uint8_t v_isSharedCheck_5167_; 
v_a_5160_ = lean_ctor_get(v___x_5159_, 0);
v_isSharedCheck_5167_ = !lean_is_exclusive(v___x_5159_);
if (v_isSharedCheck_5167_ == 0)
{
v___x_5162_ = v___x_5159_;
v_isShared_5163_ = v_isSharedCheck_5167_;
goto v_resetjp_5161_;
}
else
{
lean_inc(v_a_5160_);
lean_dec(v___x_5159_);
v___x_5162_ = lean_box(0);
v_isShared_5163_ = v_isSharedCheck_5167_;
goto v_resetjp_5161_;
}
v_resetjp_5161_:
{
lean_object* v___x_5165_; 
if (v_isShared_5163_ == 0)
{
lean_ctor_set_tag(v___x_5162_, 1);
v___x_5165_ = v___x_5162_;
goto v_reusejp_5164_;
}
else
{
lean_object* v_reuseFailAlloc_5166_; 
v_reuseFailAlloc_5166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5166_, 0, v_a_5160_);
v___x_5165_ = v_reuseFailAlloc_5166_;
goto v_reusejp_5164_;
}
v_reusejp_5164_:
{
v___y_5127_ = v_a_5155_;
v___y_5128_ = v___x_5158_;
v_a_5129_ = v___x_5165_;
goto v___jp_5126_;
}
}
}
else
{
lean_object* v_a_5168_; lean_object* v___x_5170_; uint8_t v_isShared_5171_; uint8_t v_isSharedCheck_5175_; 
v_a_5168_ = lean_ctor_get(v___x_5159_, 0);
v_isSharedCheck_5175_ = !lean_is_exclusive(v___x_5159_);
if (v_isSharedCheck_5175_ == 0)
{
v___x_5170_ = v___x_5159_;
v_isShared_5171_ = v_isSharedCheck_5175_;
goto v_resetjp_5169_;
}
else
{
lean_inc(v_a_5168_);
lean_dec(v___x_5159_);
v___x_5170_ = lean_box(0);
v_isShared_5171_ = v_isSharedCheck_5175_;
goto v_resetjp_5169_;
}
v_resetjp_5169_:
{
lean_object* v___x_5173_; 
if (v_isShared_5171_ == 0)
{
lean_ctor_set_tag(v___x_5170_, 0);
v___x_5173_ = v___x_5170_;
goto v_reusejp_5172_;
}
else
{
lean_object* v_reuseFailAlloc_5174_; 
v_reuseFailAlloc_5174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5174_, 0, v_a_5168_);
v___x_5173_ = v_reuseFailAlloc_5174_;
goto v_reusejp_5172_;
}
v_reusejp_5172_:
{
v___y_5127_ = v_a_5155_;
v___y_5128_ = v___x_5158_;
v_a_5129_ = v___x_5173_;
goto v___jp_5126_;
}
}
}
}
else
{
lean_object* v___x_5176_; lean_object* v___x_5177_; 
v___x_5176_ = lean_io_get_num_heartbeats();
lean_inc_ref(v___x_4991_);
lean_inc_ref(v___x_5021_);
v___x_5177_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5021_, v___x_4991_, v___y_4996_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
if (lean_obj_tag(v___x_5177_) == 0)
{
lean_object* v_a_5178_; lean_object* v___x_5180_; uint8_t v_isShared_5181_; uint8_t v_isSharedCheck_5185_; 
v_a_5178_ = lean_ctor_get(v___x_5177_, 0);
v_isSharedCheck_5185_ = !lean_is_exclusive(v___x_5177_);
if (v_isSharedCheck_5185_ == 0)
{
v___x_5180_ = v___x_5177_;
v_isShared_5181_ = v_isSharedCheck_5185_;
goto v_resetjp_5179_;
}
else
{
lean_inc(v_a_5178_);
lean_dec(v___x_5177_);
v___x_5180_ = lean_box(0);
v_isShared_5181_ = v_isSharedCheck_5185_;
goto v_resetjp_5179_;
}
v_resetjp_5179_:
{
lean_object* v___x_5183_; 
if (v_isShared_5181_ == 0)
{
lean_ctor_set_tag(v___x_5180_, 1);
v___x_5183_ = v___x_5180_;
goto v_reusejp_5182_;
}
else
{
lean_object* v_reuseFailAlloc_5184_; 
v_reuseFailAlloc_5184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5184_, 0, v_a_5178_);
v___x_5183_ = v_reuseFailAlloc_5184_;
goto v_reusejp_5182_;
}
v_reusejp_5182_:
{
v___y_5142_ = v___x_5176_;
v___y_5143_ = v_a_5155_;
v_a_5144_ = v___x_5183_;
goto v___jp_5141_;
}
}
}
else
{
lean_object* v_a_5186_; lean_object* v___x_5188_; uint8_t v_isShared_5189_; uint8_t v_isSharedCheck_5193_; 
v_a_5186_ = lean_ctor_get(v___x_5177_, 0);
v_isSharedCheck_5193_ = !lean_is_exclusive(v___x_5177_);
if (v_isSharedCheck_5193_ == 0)
{
v___x_5188_ = v___x_5177_;
v_isShared_5189_ = v_isSharedCheck_5193_;
goto v_resetjp_5187_;
}
else
{
lean_inc(v_a_5186_);
lean_dec(v___x_5177_);
v___x_5188_ = lean_box(0);
v_isShared_5189_ = v_isSharedCheck_5193_;
goto v_resetjp_5187_;
}
v_resetjp_5187_:
{
lean_object* v___x_5191_; 
if (v_isShared_5189_ == 0)
{
lean_ctor_set_tag(v___x_5188_, 0);
v___x_5191_ = v___x_5188_;
goto v_reusejp_5190_;
}
else
{
lean_object* v_reuseFailAlloc_5192_; 
v_reuseFailAlloc_5192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5192_, 0, v_a_5186_);
v___x_5191_ = v_reuseFailAlloc_5192_;
goto v_reusejp_5190_;
}
v_reusejp_5190_:
{
v___y_5142_ = v___x_5176_;
v___y_5143_ = v_a_5155_;
v_a_5144_ = v___x_5191_;
goto v___jp_5141_;
}
}
}
}
}
else
{
lean_object* v_a_5194_; lean_object* v___x_5196_; uint8_t v_isShared_5197_; uint8_t v_isSharedCheck_5201_; 
lean_dec_ref(v___f_5121_);
lean_dec_ref(v___x_5021_);
lean_del_object(v___x_5016_);
lean_dec(v_snd_5014_);
lean_dec(v_a_5013_);
lean_dec_ref(v___x_4991_);
lean_dec(v_mvarId_4990_);
v_a_5194_ = lean_ctor_get(v___x_5154_, 0);
v_isSharedCheck_5201_ = !lean_is_exclusive(v___x_5154_);
if (v_isSharedCheck_5201_ == 0)
{
v___x_5196_ = v___x_5154_;
v_isShared_5197_ = v_isSharedCheck_5201_;
goto v_resetjp_5195_;
}
else
{
lean_inc(v_a_5194_);
lean_dec(v___x_5154_);
v___x_5196_ = lean_box(0);
v_isShared_5197_ = v_isSharedCheck_5201_;
goto v_resetjp_5195_;
}
v_resetjp_5195_:
{
lean_object* v___x_5199_; 
if (v_isShared_5197_ == 0)
{
v___x_5199_ = v___x_5196_;
goto v_reusejp_5198_;
}
else
{
lean_object* v_reuseFailAlloc_5200_; 
v_reuseFailAlloc_5200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5200_, 0, v_a_5194_);
v___x_5199_ = v_reuseFailAlloc_5200_;
goto v_reusejp_5198_;
}
v_reusejp_5198_:
{
return v___x_5199_;
}
}
}
}
}
v___jp_5022_:
{
if (lean_obj_tag(v___y_5023_) == 0)
{
lean_object* v_a_5024_; 
v_a_5024_ = lean_ctor_get(v___y_5023_, 0);
lean_inc(v_a_5024_);
lean_dec_ref_known(v___y_5023_, 1);
if (lean_obj_tag(v_a_5024_) == 0)
{
lean_object* v___x_5026_; 
lean_dec_ref_known(v_a_5024_, 0);
lean_dec_ref(v___x_5021_);
lean_dec(v_a_5013_);
if (v_isShared_5017_ == 0)
{
lean_ctor_set(v___x_5016_, 0, v___x_5020_);
v___x_5026_ = v___x_5016_;
goto v_reusejp_5025_;
}
else
{
lean_object* v_reuseFailAlloc_5027_; 
v_reuseFailAlloc_5027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5027_, 0, v___x_5020_);
lean_ctor_set(v_reuseFailAlloc_5027_, 1, v_snd_5014_);
v___x_5026_ = v_reuseFailAlloc_5027_;
goto v_reusejp_5025_;
}
v_reusejp_5025_:
{
v_a_5004_ = v___x_5026_;
goto v___jp_5003_;
}
}
else
{
lean_object* v_e_x27_5028_; lean_object* v_proof_5029_; uint8_t v___x_5030_; 
v_e_x27_5028_ = lean_ctor_get(v_a_5024_, 0);
lean_inc_ref_n(v_e_x27_5028_, 2);
v_proof_5029_ = lean_ctor_get(v_a_5024_, 1);
lean_inc_ref(v_proof_5029_);
lean_dec_ref_known(v_a_5024_, 2);
v___x_5030_ = l_Lean_Expr_isFalse(v_e_x27_5028_);
if (v___x_5030_ == 0)
{
lean_object* v___x_5031_; 
lean_inc_ref(v___x_5021_);
v___x_5031_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_5021_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
if (lean_obj_tag(v___x_5031_) == 0)
{
lean_object* v_a_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; uint8_t v___x_5040_; uint8_t v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5045_; 
v_a_5032_ = lean_ctor_get(v___x_5031_, 0);
lean_inc(v_a_5032_);
lean_dec_ref_known(v___x_5031_, 1);
v___x_5033_ = l_Lean_LocalDecl_userName(v_a_5013_);
lean_dec(v_a_5013_);
v___x_5034_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__2));
v___x_5035_ = lean_box(0);
v___x_5036_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5036_, 0, v_a_5032_);
lean_ctor_set(v___x_5036_, 1, v___x_5035_);
v___x_5037_ = l_Lean_mkConst(v___x_5034_, v___x_5036_);
lean_inc(v_a_5010_);
v___x_5038_ = l_Lean_mkFVar(v_a_5010_);
lean_inc_ref(v_e_x27_5028_);
v___x_5039_ = l_Lean_mkApp4(v___x_5037_, v___x_5021_, v_e_x27_5028_, v_proof_5029_, v___x_5038_);
v___x_5040_ = 0;
v___x_5041_ = 0;
v___x_5042_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5042_, 0, v___x_5033_);
lean_ctor_set(v___x_5042_, 1, v_e_x27_5028_);
lean_ctor_set(v___x_5042_, 2, v___x_5039_);
lean_ctor_set_uint8(v___x_5042_, sizeof(void*)*3, v___x_5040_);
lean_ctor_set_uint8(v___x_5042_, sizeof(void*)*3 + 1, v___x_5041_);
v___x_5043_ = lean_array_push(v_snd_5014_, v___x_5042_);
if (v_isShared_5017_ == 0)
{
lean_ctor_set(v___x_5016_, 1, v___x_5043_);
lean_ctor_set(v___x_5016_, 0, v___x_5020_);
v___x_5045_ = v___x_5016_;
goto v_reusejp_5044_;
}
else
{
lean_object* v_reuseFailAlloc_5046_; 
v_reuseFailAlloc_5046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5046_, 0, v___x_5020_);
lean_ctor_set(v_reuseFailAlloc_5046_, 1, v___x_5043_);
v___x_5045_ = v_reuseFailAlloc_5046_;
goto v_reusejp_5044_;
}
v_reusejp_5044_:
{
v_a_5004_ = v___x_5045_;
goto v___jp_5003_;
}
}
else
{
lean_object* v_a_5047_; lean_object* v___x_5049_; uint8_t v_isShared_5050_; uint8_t v_isSharedCheck_5054_; 
lean_dec_ref(v_proof_5029_);
lean_dec_ref(v_e_x27_5028_);
lean_dec_ref(v___x_5021_);
lean_del_object(v___x_5016_);
lean_dec(v_snd_5014_);
lean_dec(v_a_5013_);
lean_dec_ref(v___x_4991_);
lean_dec(v_mvarId_4990_);
v_a_5047_ = lean_ctor_get(v___x_5031_, 0);
v_isSharedCheck_5054_ = !lean_is_exclusive(v___x_5031_);
if (v_isSharedCheck_5054_ == 0)
{
v___x_5049_ = v___x_5031_;
v_isShared_5050_ = v_isSharedCheck_5054_;
goto v_resetjp_5048_;
}
else
{
lean_inc(v_a_5047_);
lean_dec(v___x_5031_);
v___x_5049_ = lean_box(0);
v_isShared_5050_ = v_isSharedCheck_5054_;
goto v_resetjp_5048_;
}
v_resetjp_5048_:
{
lean_object* v___x_5052_; 
if (v_isShared_5050_ == 0)
{
v___x_5052_ = v___x_5049_;
goto v_reusejp_5051_;
}
else
{
lean_object* v_reuseFailAlloc_5053_; 
v_reuseFailAlloc_5053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5053_, 0, v_a_5047_);
v___x_5052_ = v_reuseFailAlloc_5053_;
goto v_reusejp_5051_;
}
v_reusejp_5051_:
{
return v___x_5052_;
}
}
}
}
else
{
lean_object* v___x_5055_; 
lean_dec(v_a_5013_);
lean_dec_ref(v___x_4991_);
lean_inc_ref(v___x_5021_);
v___x_5055_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_5021_, v___y_4997_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
if (lean_obj_tag(v___x_5055_) == 0)
{
lean_object* v_a_5056_; lean_object* v___x_5057_; 
v_a_5056_ = lean_ctor_get(v___x_5055_, 0);
lean_inc(v_a_5056_);
lean_dec_ref_known(v___x_5055_, 1);
lean_inc(v_mvarId_4990_);
v___x_5057_ = l_Lean_MVarId_getType(v_mvarId_4990_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
if (lean_obj_tag(v___x_5057_) == 0)
{
lean_object* v_a_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; 
v_a_5058_ = lean_ctor_get(v___x_5057_, 0);
lean_inc(v_a_5058_);
lean_dec_ref_known(v___x_5057_, 1);
v___x_5059_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__2));
v___x_5060_ = lean_box(0);
v___x_5061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5061_, 0, v_a_5056_);
lean_ctor_set(v___x_5061_, 1, v___x_5060_);
v___x_5062_ = l_Lean_mkConst(v___x_5059_, v___x_5061_);
lean_inc(v_a_5010_);
v___x_5063_ = l_Lean_mkFVar(v_a_5010_);
v___x_5064_ = l_Lean_mkApp4(v___x_5062_, v___x_5021_, v_e_x27_5028_, v_proof_5029_, v___x_5063_);
v___x_5065_ = l_Lean_Meta_mkFalseElim(v_a_5058_, v___x_5064_, v___y_4998_, v___y_4999_, v___y_5000_, v___y_5001_);
if (lean_obj_tag(v___x_5065_) == 0)
{
lean_object* v_a_5066_; lean_object* v___x_5067_; 
v_a_5066_ = lean_ctor_get(v___x_5065_, 0);
lean_inc(v_a_5066_);
lean_dec_ref_known(v___x_5065_, 1);
v___x_5067_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(v_mvarId_4990_, v_a_5066_, v___y_4999_);
if (lean_obj_tag(v___x_5067_) == 0)
{
lean_object* v___x_5069_; uint8_t v_isShared_5070_; uint8_t v_isSharedCheck_5078_; 
v_isSharedCheck_5078_ = !lean_is_exclusive(v___x_5067_);
if (v_isSharedCheck_5078_ == 0)
{
lean_object* v_unused_5079_; 
v_unused_5079_ = lean_ctor_get(v___x_5067_, 0);
lean_dec(v_unused_5079_);
v___x_5069_ = v___x_5067_;
v_isShared_5070_ = v_isSharedCheck_5078_;
goto v_resetjp_5068_;
}
else
{
lean_dec(v___x_5067_);
v___x_5069_ = lean_box(0);
v_isShared_5070_ = v_isSharedCheck_5078_;
goto v_resetjp_5068_;
}
v_resetjp_5068_:
{
lean_object* v___x_5071_; lean_object* v___x_5073_; 
v___x_5071_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__3));
if (v_isShared_5017_ == 0)
{
lean_ctor_set(v___x_5016_, 0, v___x_5071_);
v___x_5073_ = v___x_5016_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v___x_5071_);
lean_ctor_set(v_reuseFailAlloc_5077_, 1, v_snd_5014_);
v___x_5073_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
lean_object* v___x_5075_; 
if (v_isShared_5070_ == 0)
{
lean_ctor_set(v___x_5069_, 0, v___x_5073_);
v___x_5075_ = v___x_5069_;
goto v_reusejp_5074_;
}
else
{
lean_object* v_reuseFailAlloc_5076_; 
v_reuseFailAlloc_5076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5076_, 0, v___x_5073_);
v___x_5075_ = v_reuseFailAlloc_5076_;
goto v_reusejp_5074_;
}
v_reusejp_5074_:
{
return v___x_5075_;
}
}
}
}
else
{
lean_object* v_a_5080_; lean_object* v___x_5082_; uint8_t v_isShared_5083_; uint8_t v_isSharedCheck_5087_; 
lean_del_object(v___x_5016_);
lean_dec(v_snd_5014_);
v_a_5080_ = lean_ctor_get(v___x_5067_, 0);
v_isSharedCheck_5087_ = !lean_is_exclusive(v___x_5067_);
if (v_isSharedCheck_5087_ == 0)
{
v___x_5082_ = v___x_5067_;
v_isShared_5083_ = v_isSharedCheck_5087_;
goto v_resetjp_5081_;
}
else
{
lean_inc(v_a_5080_);
lean_dec(v___x_5067_);
v___x_5082_ = lean_box(0);
v_isShared_5083_ = v_isSharedCheck_5087_;
goto v_resetjp_5081_;
}
v_resetjp_5081_:
{
lean_object* v___x_5085_; 
if (v_isShared_5083_ == 0)
{
v___x_5085_ = v___x_5082_;
goto v_reusejp_5084_;
}
else
{
lean_object* v_reuseFailAlloc_5086_; 
v_reuseFailAlloc_5086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5086_, 0, v_a_5080_);
v___x_5085_ = v_reuseFailAlloc_5086_;
goto v_reusejp_5084_;
}
v_reusejp_5084_:
{
return v___x_5085_;
}
}
}
}
else
{
lean_object* v_a_5088_; lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5095_; 
lean_del_object(v___x_5016_);
lean_dec(v_snd_5014_);
lean_dec(v_mvarId_4990_);
v_a_5088_ = lean_ctor_get(v___x_5065_, 0);
v_isSharedCheck_5095_ = !lean_is_exclusive(v___x_5065_);
if (v_isSharedCheck_5095_ == 0)
{
v___x_5090_ = v___x_5065_;
v_isShared_5091_ = v_isSharedCheck_5095_;
goto v_resetjp_5089_;
}
else
{
lean_inc(v_a_5088_);
lean_dec(v___x_5065_);
v___x_5090_ = lean_box(0);
v_isShared_5091_ = v_isSharedCheck_5095_;
goto v_resetjp_5089_;
}
v_resetjp_5089_:
{
lean_object* v___x_5093_; 
if (v_isShared_5091_ == 0)
{
v___x_5093_ = v___x_5090_;
goto v_reusejp_5092_;
}
else
{
lean_object* v_reuseFailAlloc_5094_; 
v_reuseFailAlloc_5094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5094_, 0, v_a_5088_);
v___x_5093_ = v_reuseFailAlloc_5094_;
goto v_reusejp_5092_;
}
v_reusejp_5092_:
{
return v___x_5093_;
}
}
}
}
else
{
lean_object* v_a_5096_; lean_object* v___x_5098_; uint8_t v_isShared_5099_; uint8_t v_isSharedCheck_5103_; 
lean_dec(v_a_5056_);
lean_dec_ref(v_proof_5029_);
lean_dec_ref(v_e_x27_5028_);
lean_dec_ref(v___x_5021_);
lean_del_object(v___x_5016_);
lean_dec(v_snd_5014_);
lean_dec(v_mvarId_4990_);
v_a_5096_ = lean_ctor_get(v___x_5057_, 0);
v_isSharedCheck_5103_ = !lean_is_exclusive(v___x_5057_);
if (v_isSharedCheck_5103_ == 0)
{
v___x_5098_ = v___x_5057_;
v_isShared_5099_ = v_isSharedCheck_5103_;
goto v_resetjp_5097_;
}
else
{
lean_inc(v_a_5096_);
lean_dec(v___x_5057_);
v___x_5098_ = lean_box(0);
v_isShared_5099_ = v_isSharedCheck_5103_;
goto v_resetjp_5097_;
}
v_resetjp_5097_:
{
lean_object* v___x_5101_; 
if (v_isShared_5099_ == 0)
{
v___x_5101_ = v___x_5098_;
goto v_reusejp_5100_;
}
else
{
lean_object* v_reuseFailAlloc_5102_; 
v_reuseFailAlloc_5102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5102_, 0, v_a_5096_);
v___x_5101_ = v_reuseFailAlloc_5102_;
goto v_reusejp_5100_;
}
v_reusejp_5100_:
{
return v___x_5101_;
}
}
}
}
else
{
lean_object* v_a_5104_; lean_object* v___x_5106_; uint8_t v_isShared_5107_; uint8_t v_isSharedCheck_5111_; 
lean_dec_ref(v_proof_5029_);
lean_dec_ref(v_e_x27_5028_);
lean_dec_ref(v___x_5021_);
lean_del_object(v___x_5016_);
lean_dec(v_snd_5014_);
lean_dec(v_mvarId_4990_);
v_a_5104_ = lean_ctor_get(v___x_5055_, 0);
v_isSharedCheck_5111_ = !lean_is_exclusive(v___x_5055_);
if (v_isSharedCheck_5111_ == 0)
{
v___x_5106_ = v___x_5055_;
v_isShared_5107_ = v_isSharedCheck_5111_;
goto v_resetjp_5105_;
}
else
{
lean_inc(v_a_5104_);
lean_dec(v___x_5055_);
v___x_5106_ = lean_box(0);
v_isShared_5107_ = v_isSharedCheck_5111_;
goto v_resetjp_5105_;
}
v_resetjp_5105_:
{
lean_object* v___x_5109_; 
if (v_isShared_5107_ == 0)
{
v___x_5109_ = v___x_5106_;
goto v_reusejp_5108_;
}
else
{
lean_object* v_reuseFailAlloc_5110_; 
v_reuseFailAlloc_5110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5110_, 0, v_a_5104_);
v___x_5109_ = v_reuseFailAlloc_5110_;
goto v_reusejp_5108_;
}
v_reusejp_5108_:
{
return v___x_5109_;
}
}
}
}
}
}
else
{
lean_object* v_a_5112_; lean_object* v___x_5114_; uint8_t v_isShared_5115_; uint8_t v_isSharedCheck_5119_; 
lean_dec_ref(v___x_5021_);
lean_del_object(v___x_5016_);
lean_dec(v_snd_5014_);
lean_dec(v_a_5013_);
lean_dec_ref(v___x_4991_);
lean_dec(v_mvarId_4990_);
v_a_5112_ = lean_ctor_get(v___y_5023_, 0);
v_isSharedCheck_5119_ = !lean_is_exclusive(v___y_5023_);
if (v_isSharedCheck_5119_ == 0)
{
v___x_5114_ = v___y_5023_;
v_isShared_5115_ = v_isSharedCheck_5119_;
goto v_resetjp_5113_;
}
else
{
lean_inc(v_a_5112_);
lean_dec(v___y_5023_);
v___x_5114_ = lean_box(0);
v_isShared_5115_ = v_isSharedCheck_5119_;
goto v_resetjp_5113_;
}
v_resetjp_5113_:
{
lean_object* v___x_5117_; 
if (v_isShared_5115_ == 0)
{
v___x_5117_ = v___x_5114_;
goto v_reusejp_5116_;
}
else
{
lean_object* v_reuseFailAlloc_5118_; 
v_reuseFailAlloc_5118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5118_, 0, v_a_5112_);
v___x_5117_ = v_reuseFailAlloc_5118_;
goto v_reusejp_5116_;
}
v_reusejp_5116_:
{
return v___x_5117_;
}
}
}
}
}
}
else
{
lean_object* v_a_5207_; lean_object* v___x_5209_; uint8_t v_isShared_5210_; uint8_t v_isSharedCheck_5214_; 
lean_dec_ref(v_b_4995_);
lean_dec_ref(v___x_4991_);
lean_dec(v_mvarId_4990_);
v_a_5207_ = lean_ctor_get(v___x_5011_, 0);
v_isSharedCheck_5214_ = !lean_is_exclusive(v___x_5011_);
if (v_isSharedCheck_5214_ == 0)
{
v___x_5209_ = v___x_5011_;
v_isShared_5210_ = v_isSharedCheck_5214_;
goto v_resetjp_5208_;
}
else
{
lean_inc(v_a_5207_);
lean_dec(v___x_5011_);
v___x_5209_ = lean_box(0);
v_isShared_5210_ = v_isSharedCheck_5214_;
goto v_resetjp_5208_;
}
v_resetjp_5208_:
{
lean_object* v___x_5212_; 
if (v_isShared_5210_ == 0)
{
v___x_5212_ = v___x_5209_;
goto v_reusejp_5211_;
}
else
{
lean_object* v_reuseFailAlloc_5213_; 
v_reuseFailAlloc_5213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5213_, 0, v_a_5207_);
v___x_5212_ = v_reuseFailAlloc_5213_;
goto v_reusejp_5211_;
}
v_reusejp_5211_:
{
return v___x_5212_;
}
}
}
}
v___jp_5003_:
{
size_t v___x_5005_; size_t v___x_5006_; 
v___x_5005_ = ((size_t)1ULL);
v___x_5006_ = lean_usize_add(v_i_4994_, v___x_5005_);
v_i_4994_ = v___x_5006_;
v_b_4995_ = v_a_5004_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___boxed(lean_object* v_mvarId_5215_, lean_object* v___x_5216_, lean_object* v_as_5217_, lean_object* v_sz_5218_, lean_object* v_i_5219_, lean_object* v_b_5220_, lean_object* v___y_5221_, lean_object* v___y_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_){
_start:
{
size_t v_sz_boxed_5228_; size_t v_i_boxed_5229_; lean_object* v_res_5230_; 
v_sz_boxed_5228_ = lean_unbox_usize(v_sz_5218_);
lean_dec(v_sz_5218_);
v_i_boxed_5229_ = lean_unbox_usize(v_i_5219_);
lean_dec(v_i_5219_);
v_res_5230_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3(v_mvarId_5215_, v___x_5216_, v_as_5217_, v_sz_boxed_5228_, v_i_boxed_5229_, v_b_5220_, v___y_5221_, v___y_5222_, v___y_5223_, v___y_5224_, v___y_5225_, v___y_5226_);
lean_dec(v___y_5226_);
lean_dec_ref(v___y_5225_);
lean_dec(v___y_5224_);
lean_dec_ref(v___y_5223_);
lean_dec(v___y_5222_);
lean_dec_ref(v___y_5221_);
lean_dec_ref(v_as_5217_);
return v_res_5230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1(lean_object* v_mvarId_5231_, lean_object* v___x_5232_, lean_object* v_fvarIdsToSimp_5233_, size_t v_sz_5234_, size_t v___x_5235_, lean_object* v___x_5236_, uint8_t v_simplifyTarget_5237_, lean_object* v___y_5238_, lean_object* v___y_5239_, lean_object* v___y_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_){
_start:
{
lean_object* v___y_5246_; lean_object* v___y_5247_; lean_object* v___y_5248_; lean_object* v___y_5249_; lean_object* v___y_5250_; uint8_t v___y_5251_; lean_object* v___x_5271_; 
lean_inc_ref(v___x_5232_);
lean_inc(v_mvarId_5231_);
v___x_5271_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3(v_mvarId_5231_, v___x_5232_, v_fvarIdsToSimp_5233_, v_sz_5234_, v___x_5235_, v___x_5236_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_);
if (lean_obj_tag(v___x_5271_) == 0)
{
lean_object* v_a_5272_; lean_object* v___x_5274_; uint8_t v_isShared_5275_; uint8_t v_isSharedCheck_5474_; 
v_a_5272_ = lean_ctor_get(v___x_5271_, 0);
v_isSharedCheck_5474_ = !lean_is_exclusive(v___x_5271_);
if (v_isSharedCheck_5474_ == 0)
{
v___x_5274_ = v___x_5271_;
v_isShared_5275_ = v_isSharedCheck_5474_;
goto v_resetjp_5273_;
}
else
{
lean_inc(v_a_5272_);
lean_dec(v___x_5271_);
v___x_5274_ = lean_box(0);
v_isShared_5275_ = v_isSharedCheck_5474_;
goto v_resetjp_5273_;
}
v_resetjp_5273_:
{
lean_object* v_fst_5276_; lean_object* v_snd_5277_; lean_object* v___x_5279_; uint8_t v_isShared_5280_; uint8_t v_isSharedCheck_5473_; 
v_fst_5276_ = lean_ctor_get(v_a_5272_, 0);
v_snd_5277_ = lean_ctor_get(v_a_5272_, 1);
v_isSharedCheck_5473_ = !lean_is_exclusive(v_a_5272_);
if (v_isSharedCheck_5473_ == 0)
{
v___x_5279_ = v_a_5272_;
v_isShared_5280_ = v_isSharedCheck_5473_;
goto v_resetjp_5278_;
}
else
{
lean_inc(v_snd_5277_);
lean_inc(v_fst_5276_);
lean_dec(v_a_5272_);
v___x_5279_ = lean_box(0);
v_isShared_5280_ = v_isSharedCheck_5473_;
goto v_resetjp_5278_;
}
v_resetjp_5278_:
{
lean_object* v_mvarIdNew_5282_; lean_object* v___y_5283_; lean_object* v___y_5284_; lean_object* v___y_5285_; lean_object* v___y_5286_; lean_object* v___y_5333_; 
if (lean_obj_tag(v_fst_5276_) == 0)
{
lean_del_object(v___x_5274_);
if (v_simplifyTarget_5237_ == 0)
{
lean_del_object(v___x_5279_);
lean_dec_ref(v___x_5232_);
v_mvarIdNew_5282_ = v_mvarId_5231_;
v___y_5283_ = v___y_5240_;
v___y_5284_ = v___y_5241_;
v___y_5285_ = v___y_5242_;
v___y_5286_ = v___y_5243_;
goto v___jp_5281_;
}
else
{
lean_object* v___x_5376_; 
lean_inc(v_mvarId_5231_);
v___x_5376_ = l_Lean_MVarId_getType(v_mvarId_5231_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_);
if (lean_obj_tag(v___x_5376_) == 0)
{
lean_object* v_options_5377_; uint8_t v_hasTrace_5378_; 
v_options_5377_ = lean_ctor_get(v___y_5242_, 2);
v_hasTrace_5378_ = lean_ctor_get_uint8(v_options_5377_, sizeof(void*)*1);
if (v_hasTrace_5378_ == 0)
{
lean_object* v_a_5379_; lean_object* v___x_5380_; 
lean_del_object(v___x_5279_);
v_a_5379_ = lean_ctor_get(v___x_5376_, 0);
lean_inc(v_a_5379_);
lean_dec_ref_known(v___x_5376_, 1);
v___x_5380_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5379_, v___x_5232_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_);
v___y_5333_ = v___x_5380_;
goto v___jp_5332_;
}
else
{
lean_object* v_a_5381_; lean_object* v_inheritedTraceOptions_5382_; lean_object* v___f_5383_; lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v___x_5386_; uint8_t v___x_5387_; lean_object* v___y_5389_; lean_object* v___y_5390_; lean_object* v_a_5391_; lean_object* v___y_5406_; lean_object* v___y_5407_; lean_object* v_a_5408_; 
v_a_5381_ = lean_ctor_get(v___x_5376_, 0);
lean_inc_n(v_a_5381_, 2);
lean_dec_ref_known(v___x_5376_, 1);
v_inheritedTraceOptions_5382_ = lean_ctor_get(v___y_5242_, 13);
v___f_5383_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___boxed), 9, 1);
lean_closure_set(v___f_5383_, 0, v_a_5381_);
v___x_5384_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_5385_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_5386_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_5387_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5382_, v_options_5377_, v___x_5386_);
if (v___x_5387_ == 0)
{
lean_object* v___x_5458_; uint8_t v___x_5459_; 
v___x_5458_ = l_Lean_trace_profiler;
v___x_5459_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5377_, v___x_5458_);
if (v___x_5459_ == 0)
{
lean_object* v___x_5460_; 
lean_dec_ref(v___f_5383_);
lean_del_object(v___x_5279_);
v___x_5460_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5381_, v___x_5232_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_);
v___y_5333_ = v___x_5460_;
goto v___jp_5332_;
}
else
{
goto v___jp_5417_;
}
}
else
{
goto v___jp_5417_;
}
v___jp_5388_:
{
lean_object* v___x_5392_; double v___x_5393_; double v___x_5394_; double v___x_5395_; double v___x_5396_; double v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; lean_object* v___x_5401_; 
v___x_5392_ = lean_io_mono_nanos_now();
v___x_5393_ = lean_float_of_nat(v___y_5389_);
v___x_5394_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_5395_ = lean_float_div(v___x_5393_, v___x_5394_);
v___x_5396_ = lean_float_of_nat(v___x_5392_);
v___x_5397_ = lean_float_div(v___x_5396_, v___x_5394_);
v___x_5398_ = lean_box_float(v___x_5395_);
v___x_5399_ = lean_box_float(v___x_5397_);
if (v_isShared_5280_ == 0)
{
lean_ctor_set(v___x_5279_, 1, v___x_5399_);
lean_ctor_set(v___x_5279_, 0, v___x_5398_);
v___x_5401_ = v___x_5279_;
goto v_reusejp_5400_;
}
else
{
lean_object* v_reuseFailAlloc_5404_; 
v_reuseFailAlloc_5404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5404_, 0, v___x_5398_);
lean_ctor_set(v_reuseFailAlloc_5404_, 1, v___x_5399_);
v___x_5401_ = v_reuseFailAlloc_5404_;
goto v_reusejp_5400_;
}
v_reusejp_5400_:
{
lean_object* v___x_5402_; lean_object* v___x_5403_; 
v___x_5402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5402_, 0, v_a_5391_);
lean_ctor_set(v___x_5402_, 1, v___x_5401_);
v___x_5403_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v___x_5384_, v_hasTrace_5378_, v___x_5385_, v_options_5377_, v___x_5387_, v___y_5390_, v___f_5383_, v___x_5402_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_);
v___y_5333_ = v___x_5403_;
goto v___jp_5332_;
}
}
v___jp_5405_:
{
lean_object* v___x_5409_; double v___x_5410_; double v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; 
v___x_5409_ = lean_io_get_num_heartbeats();
v___x_5410_ = lean_float_of_nat(v___y_5406_);
v___x_5411_ = lean_float_of_nat(v___x_5409_);
v___x_5412_ = lean_box_float(v___x_5410_);
v___x_5413_ = lean_box_float(v___x_5411_);
v___x_5414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5414_, 0, v___x_5412_);
lean_ctor_set(v___x_5414_, 1, v___x_5413_);
v___x_5415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5415_, 0, v_a_5408_);
lean_ctor_set(v___x_5415_, 1, v___x_5414_);
v___x_5416_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v___x_5384_, v_hasTrace_5378_, v___x_5385_, v_options_5377_, v___x_5387_, v___y_5407_, v___f_5383_, v___x_5415_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_);
v___y_5333_ = v___x_5416_;
goto v___jp_5332_;
}
v___jp_5417_:
{
lean_object* v___x_5418_; lean_object* v_a_5419_; lean_object* v___x_5420_; uint8_t v___x_5421_; 
v___x_5418_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(v___y_5243_);
v_a_5419_ = lean_ctor_get(v___x_5418_, 0);
lean_inc(v_a_5419_);
lean_dec_ref(v___x_5418_);
v___x_5420_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5421_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5377_, v___x_5420_);
if (v___x_5421_ == 0)
{
lean_object* v___x_5422_; lean_object* v___x_5423_; 
v___x_5422_ = lean_io_mono_nanos_now();
v___x_5423_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5381_, v___x_5232_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_);
if (lean_obj_tag(v___x_5423_) == 0)
{
lean_object* v_a_5424_; lean_object* v___x_5426_; uint8_t v_isShared_5427_; uint8_t v_isSharedCheck_5431_; 
v_a_5424_ = lean_ctor_get(v___x_5423_, 0);
v_isSharedCheck_5431_ = !lean_is_exclusive(v___x_5423_);
if (v_isSharedCheck_5431_ == 0)
{
v___x_5426_ = v___x_5423_;
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
else
{
lean_inc(v_a_5424_);
lean_dec(v___x_5423_);
v___x_5426_ = lean_box(0);
v_isShared_5427_ = v_isSharedCheck_5431_;
goto v_resetjp_5425_;
}
v_resetjp_5425_:
{
lean_object* v___x_5429_; 
if (v_isShared_5427_ == 0)
{
lean_ctor_set_tag(v___x_5426_, 1);
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
v___y_5389_ = v___x_5422_;
v___y_5390_ = v_a_5419_;
v_a_5391_ = v___x_5429_;
goto v___jp_5388_;
}
}
}
else
{
lean_object* v_a_5432_; lean_object* v___x_5434_; uint8_t v_isShared_5435_; uint8_t v_isSharedCheck_5439_; 
v_a_5432_ = lean_ctor_get(v___x_5423_, 0);
v_isSharedCheck_5439_ = !lean_is_exclusive(v___x_5423_);
if (v_isSharedCheck_5439_ == 0)
{
v___x_5434_ = v___x_5423_;
v_isShared_5435_ = v_isSharedCheck_5439_;
goto v_resetjp_5433_;
}
else
{
lean_inc(v_a_5432_);
lean_dec(v___x_5423_);
v___x_5434_ = lean_box(0);
v_isShared_5435_ = v_isSharedCheck_5439_;
goto v_resetjp_5433_;
}
v_resetjp_5433_:
{
lean_object* v___x_5437_; 
if (v_isShared_5435_ == 0)
{
lean_ctor_set_tag(v___x_5434_, 0);
v___x_5437_ = v___x_5434_;
goto v_reusejp_5436_;
}
else
{
lean_object* v_reuseFailAlloc_5438_; 
v_reuseFailAlloc_5438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5438_, 0, v_a_5432_);
v___x_5437_ = v_reuseFailAlloc_5438_;
goto v_reusejp_5436_;
}
v_reusejp_5436_:
{
v___y_5389_ = v___x_5422_;
v___y_5390_ = v_a_5419_;
v_a_5391_ = v___x_5437_;
goto v___jp_5388_;
}
}
}
}
else
{
lean_object* v___x_5440_; lean_object* v___x_5441_; 
lean_del_object(v___x_5279_);
v___x_5440_ = lean_io_get_num_heartbeats();
v___x_5441_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5381_, v___x_5232_, v___y_5238_, v___y_5239_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_);
if (lean_obj_tag(v___x_5441_) == 0)
{
lean_object* v_a_5442_; lean_object* v___x_5444_; uint8_t v_isShared_5445_; uint8_t v_isSharedCheck_5449_; 
v_a_5442_ = lean_ctor_get(v___x_5441_, 0);
v_isSharedCheck_5449_ = !lean_is_exclusive(v___x_5441_);
if (v_isSharedCheck_5449_ == 0)
{
v___x_5444_ = v___x_5441_;
v_isShared_5445_ = v_isSharedCheck_5449_;
goto v_resetjp_5443_;
}
else
{
lean_inc(v_a_5442_);
lean_dec(v___x_5441_);
v___x_5444_ = lean_box(0);
v_isShared_5445_ = v_isSharedCheck_5449_;
goto v_resetjp_5443_;
}
v_resetjp_5443_:
{
lean_object* v___x_5447_; 
if (v_isShared_5445_ == 0)
{
lean_ctor_set_tag(v___x_5444_, 1);
v___x_5447_ = v___x_5444_;
goto v_reusejp_5446_;
}
else
{
lean_object* v_reuseFailAlloc_5448_; 
v_reuseFailAlloc_5448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5448_, 0, v_a_5442_);
v___x_5447_ = v_reuseFailAlloc_5448_;
goto v_reusejp_5446_;
}
v_reusejp_5446_:
{
v___y_5406_ = v___x_5440_;
v___y_5407_ = v_a_5419_;
v_a_5408_ = v___x_5447_;
goto v___jp_5405_;
}
}
}
else
{
lean_object* v_a_5450_; lean_object* v___x_5452_; uint8_t v_isShared_5453_; uint8_t v_isSharedCheck_5457_; 
v_a_5450_ = lean_ctor_get(v___x_5441_, 0);
v_isSharedCheck_5457_ = !lean_is_exclusive(v___x_5441_);
if (v_isSharedCheck_5457_ == 0)
{
v___x_5452_ = v___x_5441_;
v_isShared_5453_ = v_isSharedCheck_5457_;
goto v_resetjp_5451_;
}
else
{
lean_inc(v_a_5450_);
lean_dec(v___x_5441_);
v___x_5452_ = lean_box(0);
v_isShared_5453_ = v_isSharedCheck_5457_;
goto v_resetjp_5451_;
}
v_resetjp_5451_:
{
lean_object* v___x_5455_; 
if (v_isShared_5453_ == 0)
{
lean_ctor_set_tag(v___x_5452_, 0);
v___x_5455_ = v___x_5452_;
goto v_reusejp_5454_;
}
else
{
lean_object* v_reuseFailAlloc_5456_; 
v_reuseFailAlloc_5456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5456_, 0, v_a_5450_);
v___x_5455_ = v_reuseFailAlloc_5456_;
goto v_reusejp_5454_;
}
v_reusejp_5454_:
{
v___y_5406_ = v___x_5440_;
v___y_5407_ = v_a_5419_;
v_a_5408_ = v___x_5455_;
goto v___jp_5405_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5461_; lean_object* v___x_5463_; uint8_t v_isShared_5464_; uint8_t v_isSharedCheck_5468_; 
lean_del_object(v___x_5279_);
lean_dec(v_snd_5277_);
lean_dec_ref(v___x_5232_);
lean_dec(v_mvarId_5231_);
v_a_5461_ = lean_ctor_get(v___x_5376_, 0);
v_isSharedCheck_5468_ = !lean_is_exclusive(v___x_5376_);
if (v_isSharedCheck_5468_ == 0)
{
v___x_5463_ = v___x_5376_;
v_isShared_5464_ = v_isSharedCheck_5468_;
goto v_resetjp_5462_;
}
else
{
lean_inc(v_a_5461_);
lean_dec(v___x_5376_);
v___x_5463_ = lean_box(0);
v_isShared_5464_ = v_isSharedCheck_5468_;
goto v_resetjp_5462_;
}
v_resetjp_5462_:
{
lean_object* v___x_5466_; 
if (v_isShared_5464_ == 0)
{
v___x_5466_ = v___x_5463_;
goto v_reusejp_5465_;
}
else
{
lean_object* v_reuseFailAlloc_5467_; 
v_reuseFailAlloc_5467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5467_, 0, v_a_5461_);
v___x_5466_ = v_reuseFailAlloc_5467_;
goto v_reusejp_5465_;
}
v_reusejp_5465_:
{
return v___x_5466_;
}
}
}
}
}
else
{
lean_object* v_val_5469_; lean_object* v___x_5471_; 
lean_del_object(v___x_5279_);
lean_dec(v_snd_5277_);
lean_dec_ref(v___x_5232_);
lean_dec(v_mvarId_5231_);
v_val_5469_ = lean_ctor_get(v_fst_5276_, 0);
lean_inc(v_val_5469_);
lean_dec_ref_known(v_fst_5276_, 1);
if (v_isShared_5275_ == 0)
{
lean_ctor_set(v___x_5274_, 0, v_val_5469_);
v___x_5471_ = v___x_5274_;
goto v_reusejp_5470_;
}
else
{
lean_object* v_reuseFailAlloc_5472_; 
v_reuseFailAlloc_5472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5472_, 0, v_val_5469_);
v___x_5471_ = v_reuseFailAlloc_5472_;
goto v_reusejp_5470_;
}
v_reusejp_5470_:
{
return v___x_5471_;
}
}
v___jp_5281_:
{
lean_object* v___x_5287_; 
v___x_5287_ = l_Lean_MVarId_assertHypotheses(v_mvarIdNew_5282_, v_snd_5277_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_);
if (lean_obj_tag(v___x_5287_) == 0)
{
lean_object* v_a_5288_; lean_object* v_snd_5289_; lean_object* v___x_5290_; 
v_a_5288_ = lean_ctor_get(v___x_5287_, 0);
lean_inc(v_a_5288_);
lean_dec_ref_known(v___x_5287_, 1);
v_snd_5289_ = lean_ctor_get(v_a_5288_, 1);
lean_inc(v_snd_5289_);
lean_dec(v_a_5288_);
v___x_5290_ = l_Lean_MVarId_tryClearMany(v_snd_5289_, v_fvarIdsToSimp_5233_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_);
if (lean_obj_tag(v___x_5290_) == 0)
{
lean_object* v_a_5291_; lean_object* v___x_5292_; 
v_a_5291_ = lean_ctor_get(v___x_5290_, 0);
lean_inc(v_a_5291_);
lean_dec_ref_known(v___x_5290_, 1);
v___x_5292_ = l_Lean_Meta_saveState___redArg(v___y_5284_, v___y_5286_);
if (lean_obj_tag(v___x_5292_) == 0)
{
lean_object* v_a_5293_; uint8_t v___x_5294_; lean_object* v___x_5295_; 
v_a_5293_ = lean_ctor_get(v___x_5292_, 0);
lean_inc(v_a_5293_);
lean_dec_ref_known(v___x_5292_, 1);
v___x_5294_ = 1;
lean_inc(v_a_5291_);
v___x_5295_ = l_Lean_MVarId_refl(v_a_5291_, v___x_5294_, v___y_5283_, v___y_5284_, v___y_5285_, v___y_5286_);
if (lean_obj_tag(v___x_5295_) == 0)
{
lean_object* v___x_5297_; uint8_t v_isShared_5298_; uint8_t v_isSharedCheck_5303_; 
lean_dec(v_a_5293_);
lean_dec(v_a_5291_);
v_isSharedCheck_5303_ = !lean_is_exclusive(v___x_5295_);
if (v_isSharedCheck_5303_ == 0)
{
lean_object* v_unused_5304_; 
v_unused_5304_ = lean_ctor_get(v___x_5295_, 0);
lean_dec(v_unused_5304_);
v___x_5297_ = v___x_5295_;
v_isShared_5298_ = v_isSharedCheck_5303_;
goto v_resetjp_5296_;
}
else
{
lean_dec(v___x_5295_);
v___x_5297_ = lean_box(0);
v_isShared_5298_ = v_isSharedCheck_5303_;
goto v_resetjp_5296_;
}
v_resetjp_5296_:
{
lean_object* v___x_5299_; lean_object* v___x_5301_; 
v___x_5299_ = lean_box(0);
if (v_isShared_5298_ == 0)
{
lean_ctor_set(v___x_5297_, 0, v___x_5299_);
v___x_5301_ = v___x_5297_;
goto v_reusejp_5300_;
}
else
{
lean_object* v_reuseFailAlloc_5302_; 
v_reuseFailAlloc_5302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5302_, 0, v___x_5299_);
v___x_5301_ = v_reuseFailAlloc_5302_;
goto v_reusejp_5300_;
}
v_reusejp_5300_:
{
return v___x_5301_;
}
}
}
else
{
lean_object* v_a_5305_; uint8_t v___x_5306_; 
v_a_5305_ = lean_ctor_get(v___x_5295_, 0);
lean_inc(v_a_5305_);
lean_dec_ref_known(v___x_5295_, 1);
v___x_5306_ = l_Lean_Exception_isInterrupt(v_a_5305_);
if (v___x_5306_ == 0)
{
uint8_t v___x_5307_; 
lean_inc(v_a_5305_);
v___x_5307_ = l_Lean_Exception_isRuntime(v_a_5305_);
v___y_5246_ = v_a_5291_;
v___y_5247_ = v_a_5305_;
v___y_5248_ = v___y_5286_;
v___y_5249_ = v___y_5284_;
v___y_5250_ = v_a_5293_;
v___y_5251_ = v___x_5307_;
goto v___jp_5245_;
}
else
{
v___y_5246_ = v_a_5291_;
v___y_5247_ = v_a_5305_;
v___y_5248_ = v___y_5286_;
v___y_5249_ = v___y_5284_;
v___y_5250_ = v_a_5293_;
v___y_5251_ = v___x_5306_;
goto v___jp_5245_;
}
}
}
else
{
lean_object* v_a_5308_; lean_object* v___x_5310_; uint8_t v_isShared_5311_; uint8_t v_isSharedCheck_5315_; 
lean_dec(v_a_5291_);
v_a_5308_ = lean_ctor_get(v___x_5292_, 0);
v_isSharedCheck_5315_ = !lean_is_exclusive(v___x_5292_);
if (v_isSharedCheck_5315_ == 0)
{
v___x_5310_ = v___x_5292_;
v_isShared_5311_ = v_isSharedCheck_5315_;
goto v_resetjp_5309_;
}
else
{
lean_inc(v_a_5308_);
lean_dec(v___x_5292_);
v___x_5310_ = lean_box(0);
v_isShared_5311_ = v_isSharedCheck_5315_;
goto v_resetjp_5309_;
}
v_resetjp_5309_:
{
lean_object* v___x_5313_; 
if (v_isShared_5311_ == 0)
{
v___x_5313_ = v___x_5310_;
goto v_reusejp_5312_;
}
else
{
lean_object* v_reuseFailAlloc_5314_; 
v_reuseFailAlloc_5314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5314_, 0, v_a_5308_);
v___x_5313_ = v_reuseFailAlloc_5314_;
goto v_reusejp_5312_;
}
v_reusejp_5312_:
{
return v___x_5313_;
}
}
}
}
else
{
lean_object* v_a_5316_; lean_object* v___x_5318_; uint8_t v_isShared_5319_; uint8_t v_isSharedCheck_5323_; 
v_a_5316_ = lean_ctor_get(v___x_5290_, 0);
v_isSharedCheck_5323_ = !lean_is_exclusive(v___x_5290_);
if (v_isSharedCheck_5323_ == 0)
{
v___x_5318_ = v___x_5290_;
v_isShared_5319_ = v_isSharedCheck_5323_;
goto v_resetjp_5317_;
}
else
{
lean_inc(v_a_5316_);
lean_dec(v___x_5290_);
v___x_5318_ = lean_box(0);
v_isShared_5319_ = v_isSharedCheck_5323_;
goto v_resetjp_5317_;
}
v_resetjp_5317_:
{
lean_object* v___x_5321_; 
if (v_isShared_5319_ == 0)
{
v___x_5321_ = v___x_5318_;
goto v_reusejp_5320_;
}
else
{
lean_object* v_reuseFailAlloc_5322_; 
v_reuseFailAlloc_5322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5322_, 0, v_a_5316_);
v___x_5321_ = v_reuseFailAlloc_5322_;
goto v_reusejp_5320_;
}
v_reusejp_5320_:
{
return v___x_5321_;
}
}
}
}
else
{
lean_object* v_a_5324_; lean_object* v___x_5326_; uint8_t v_isShared_5327_; uint8_t v_isSharedCheck_5331_; 
v_a_5324_ = lean_ctor_get(v___x_5287_, 0);
v_isSharedCheck_5331_ = !lean_is_exclusive(v___x_5287_);
if (v_isSharedCheck_5331_ == 0)
{
v___x_5326_ = v___x_5287_;
v_isShared_5327_ = v_isSharedCheck_5331_;
goto v_resetjp_5325_;
}
else
{
lean_inc(v_a_5324_);
lean_dec(v___x_5287_);
v___x_5326_ = lean_box(0);
v_isShared_5327_ = v_isSharedCheck_5331_;
goto v_resetjp_5325_;
}
v_resetjp_5325_:
{
lean_object* v___x_5329_; 
if (v_isShared_5327_ == 0)
{
v___x_5329_ = v___x_5326_;
goto v_reusejp_5328_;
}
else
{
lean_object* v_reuseFailAlloc_5330_; 
v_reuseFailAlloc_5330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5330_, 0, v_a_5324_);
v___x_5329_ = v_reuseFailAlloc_5330_;
goto v_reusejp_5328_;
}
v_reusejp_5328_:
{
return v___x_5329_;
}
}
}
}
v___jp_5332_:
{
if (lean_obj_tag(v___y_5333_) == 0)
{
lean_object* v_a_5334_; 
v_a_5334_ = lean_ctor_get(v___y_5333_, 0);
lean_inc(v_a_5334_);
lean_dec_ref_known(v___y_5333_, 1);
if (lean_obj_tag(v_a_5334_) == 0)
{
lean_dec_ref_known(v_a_5334_, 0);
v_mvarIdNew_5282_ = v_mvarId_5231_;
v___y_5283_ = v___y_5240_;
v___y_5284_ = v___y_5241_;
v___y_5285_ = v___y_5242_;
v___y_5286_ = v___y_5243_;
goto v___jp_5281_;
}
else
{
lean_object* v_e_x27_5335_; lean_object* v_proof_5336_; uint8_t v___x_5337_; 
v_e_x27_5335_ = lean_ctor_get(v_a_5334_, 0);
lean_inc_ref_n(v_e_x27_5335_, 2);
v_proof_5336_ = lean_ctor_get(v_a_5334_, 1);
lean_inc_ref(v_proof_5336_);
lean_dec_ref_known(v_a_5334_, 2);
v___x_5337_ = l_Lean_Expr_isTrue(v_e_x27_5335_);
if (v___x_5337_ == 0)
{
lean_object* v___x_5338_; 
v___x_5338_ = l_Lean_MVarId_replaceTargetEq(v_mvarId_5231_, v_e_x27_5335_, v_proof_5336_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_);
if (lean_obj_tag(v___x_5338_) == 0)
{
lean_object* v_a_5339_; 
v_a_5339_ = lean_ctor_get(v___x_5338_, 0);
lean_inc(v_a_5339_);
lean_dec_ref_known(v___x_5338_, 1);
v_mvarIdNew_5282_ = v_a_5339_;
v___y_5283_ = v___y_5240_;
v___y_5284_ = v___y_5241_;
v___y_5285_ = v___y_5242_;
v___y_5286_ = v___y_5243_;
goto v___jp_5281_;
}
else
{
lean_object* v_a_5340_; lean_object* v___x_5342_; uint8_t v_isShared_5343_; uint8_t v_isSharedCheck_5347_; 
lean_dec(v_snd_5277_);
v_a_5340_ = lean_ctor_get(v___x_5338_, 0);
v_isSharedCheck_5347_ = !lean_is_exclusive(v___x_5338_);
if (v_isSharedCheck_5347_ == 0)
{
v___x_5342_ = v___x_5338_;
v_isShared_5343_ = v_isSharedCheck_5347_;
goto v_resetjp_5341_;
}
else
{
lean_inc(v_a_5340_);
lean_dec(v___x_5338_);
v___x_5342_ = lean_box(0);
v_isShared_5343_ = v_isSharedCheck_5347_;
goto v_resetjp_5341_;
}
v_resetjp_5341_:
{
lean_object* v___x_5345_; 
if (v_isShared_5343_ == 0)
{
v___x_5345_ = v___x_5342_;
goto v_reusejp_5344_;
}
else
{
lean_object* v_reuseFailAlloc_5346_; 
v_reuseFailAlloc_5346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5346_, 0, v_a_5340_);
v___x_5345_ = v_reuseFailAlloc_5346_;
goto v_reusejp_5344_;
}
v_reusejp_5344_:
{
return v___x_5345_;
}
}
}
}
else
{
lean_object* v___x_5348_; 
lean_dec_ref(v_e_x27_5335_);
lean_dec(v_snd_5277_);
v___x_5348_ = l_Lean_Meta_mkOfEqTrue(v_proof_5336_, v___y_5240_, v___y_5241_, v___y_5242_, v___y_5243_);
if (lean_obj_tag(v___x_5348_) == 0)
{
lean_object* v_a_5349_; lean_object* v___x_5350_; lean_object* v___x_5352_; uint8_t v_isShared_5353_; uint8_t v_isSharedCheck_5358_; 
v_a_5349_ = lean_ctor_get(v___x_5348_, 0);
lean_inc(v_a_5349_);
lean_dec_ref_known(v___x_5348_, 1);
v___x_5350_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(v_mvarId_5231_, v_a_5349_, v___y_5241_);
v_isSharedCheck_5358_ = !lean_is_exclusive(v___x_5350_);
if (v_isSharedCheck_5358_ == 0)
{
lean_object* v_unused_5359_; 
v_unused_5359_ = lean_ctor_get(v___x_5350_, 0);
lean_dec(v_unused_5359_);
v___x_5352_ = v___x_5350_;
v_isShared_5353_ = v_isSharedCheck_5358_;
goto v_resetjp_5351_;
}
else
{
lean_dec(v___x_5350_);
v___x_5352_ = lean_box(0);
v_isShared_5353_ = v_isSharedCheck_5358_;
goto v_resetjp_5351_;
}
v_resetjp_5351_:
{
lean_object* v___x_5354_; lean_object* v___x_5356_; 
v___x_5354_ = lean_box(0);
if (v_isShared_5353_ == 0)
{
lean_ctor_set(v___x_5352_, 0, v___x_5354_);
v___x_5356_ = v___x_5352_;
goto v_reusejp_5355_;
}
else
{
lean_object* v_reuseFailAlloc_5357_; 
v_reuseFailAlloc_5357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5357_, 0, v___x_5354_);
v___x_5356_ = v_reuseFailAlloc_5357_;
goto v_reusejp_5355_;
}
v_reusejp_5355_:
{
return v___x_5356_;
}
}
}
else
{
lean_object* v_a_5360_; lean_object* v___x_5362_; uint8_t v_isShared_5363_; uint8_t v_isSharedCheck_5367_; 
lean_dec(v_mvarId_5231_);
v_a_5360_ = lean_ctor_get(v___x_5348_, 0);
v_isSharedCheck_5367_ = !lean_is_exclusive(v___x_5348_);
if (v_isSharedCheck_5367_ == 0)
{
v___x_5362_ = v___x_5348_;
v_isShared_5363_ = v_isSharedCheck_5367_;
goto v_resetjp_5361_;
}
else
{
lean_inc(v_a_5360_);
lean_dec(v___x_5348_);
v___x_5362_ = lean_box(0);
v_isShared_5363_ = v_isSharedCheck_5367_;
goto v_resetjp_5361_;
}
v_resetjp_5361_:
{
lean_object* v___x_5365_; 
if (v_isShared_5363_ == 0)
{
v___x_5365_ = v___x_5362_;
goto v_reusejp_5364_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_a_5360_);
v___x_5365_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5364_;
}
v_reusejp_5364_:
{
return v___x_5365_;
}
}
}
}
}
}
else
{
lean_object* v_a_5368_; lean_object* v___x_5370_; uint8_t v_isShared_5371_; uint8_t v_isSharedCheck_5375_; 
lean_dec(v_snd_5277_);
lean_dec(v_mvarId_5231_);
v_a_5368_ = lean_ctor_get(v___y_5333_, 0);
v_isSharedCheck_5375_ = !lean_is_exclusive(v___y_5333_);
if (v_isSharedCheck_5375_ == 0)
{
v___x_5370_ = v___y_5333_;
v_isShared_5371_ = v_isSharedCheck_5375_;
goto v_resetjp_5369_;
}
else
{
lean_inc(v_a_5368_);
lean_dec(v___y_5333_);
v___x_5370_ = lean_box(0);
v_isShared_5371_ = v_isSharedCheck_5375_;
goto v_resetjp_5369_;
}
v_resetjp_5369_:
{
lean_object* v___x_5373_; 
if (v_isShared_5371_ == 0)
{
v___x_5373_ = v___x_5370_;
goto v_reusejp_5372_;
}
else
{
lean_object* v_reuseFailAlloc_5374_; 
v_reuseFailAlloc_5374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5374_, 0, v_a_5368_);
v___x_5373_ = v_reuseFailAlloc_5374_;
goto v_reusejp_5372_;
}
v_reusejp_5372_:
{
return v___x_5373_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5475_; lean_object* v___x_5477_; uint8_t v_isShared_5478_; uint8_t v_isSharedCheck_5482_; 
lean_dec_ref(v___x_5232_);
lean_dec(v_mvarId_5231_);
v_a_5475_ = lean_ctor_get(v___x_5271_, 0);
v_isSharedCheck_5482_ = !lean_is_exclusive(v___x_5271_);
if (v_isSharedCheck_5482_ == 0)
{
v___x_5477_ = v___x_5271_;
v_isShared_5478_ = v_isSharedCheck_5482_;
goto v_resetjp_5476_;
}
else
{
lean_inc(v_a_5475_);
lean_dec(v___x_5271_);
v___x_5477_ = lean_box(0);
v_isShared_5478_ = v_isSharedCheck_5482_;
goto v_resetjp_5476_;
}
v_resetjp_5476_:
{
lean_object* v___x_5480_; 
if (v_isShared_5478_ == 0)
{
v___x_5480_ = v___x_5477_;
goto v_reusejp_5479_;
}
else
{
lean_object* v_reuseFailAlloc_5481_; 
v_reuseFailAlloc_5481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5481_, 0, v_a_5475_);
v___x_5480_ = v_reuseFailAlloc_5481_;
goto v_reusejp_5479_;
}
v_reusejp_5479_:
{
return v___x_5480_;
}
}
}
v___jp_5245_:
{
if (v___y_5251_ == 0)
{
lean_object* v___x_5252_; 
lean_dec_ref(v___y_5247_);
v___x_5252_ = l_Lean_Meta_SavedState_restore___redArg(v___y_5250_, v___y_5249_, v___y_5248_);
lean_dec_ref(v___y_5250_);
if (lean_obj_tag(v___x_5252_) == 0)
{
lean_object* v___x_5254_; uint8_t v_isShared_5255_; uint8_t v_isSharedCheck_5260_; 
v_isSharedCheck_5260_ = !lean_is_exclusive(v___x_5252_);
if (v_isSharedCheck_5260_ == 0)
{
lean_object* v_unused_5261_; 
v_unused_5261_ = lean_ctor_get(v___x_5252_, 0);
lean_dec(v_unused_5261_);
v___x_5254_ = v___x_5252_;
v_isShared_5255_ = v_isSharedCheck_5260_;
goto v_resetjp_5253_;
}
else
{
lean_dec(v___x_5252_);
v___x_5254_ = lean_box(0);
v_isShared_5255_ = v_isSharedCheck_5260_;
goto v_resetjp_5253_;
}
v_resetjp_5253_:
{
lean_object* v___x_5256_; lean_object* v___x_5258_; 
v___x_5256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5256_, 0, v___y_5246_);
if (v_isShared_5255_ == 0)
{
lean_ctor_set(v___x_5254_, 0, v___x_5256_);
v___x_5258_ = v___x_5254_;
goto v_reusejp_5257_;
}
else
{
lean_object* v_reuseFailAlloc_5259_; 
v_reuseFailAlloc_5259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5259_, 0, v___x_5256_);
v___x_5258_ = v_reuseFailAlloc_5259_;
goto v_reusejp_5257_;
}
v_reusejp_5257_:
{
return v___x_5258_;
}
}
}
else
{
lean_object* v_a_5262_; lean_object* v___x_5264_; uint8_t v_isShared_5265_; uint8_t v_isSharedCheck_5269_; 
lean_dec(v___y_5246_);
v_a_5262_ = lean_ctor_get(v___x_5252_, 0);
v_isSharedCheck_5269_ = !lean_is_exclusive(v___x_5252_);
if (v_isSharedCheck_5269_ == 0)
{
v___x_5264_ = v___x_5252_;
v_isShared_5265_ = v_isSharedCheck_5269_;
goto v_resetjp_5263_;
}
else
{
lean_inc(v_a_5262_);
lean_dec(v___x_5252_);
v___x_5264_ = lean_box(0);
v_isShared_5265_ = v_isSharedCheck_5269_;
goto v_resetjp_5263_;
}
v_resetjp_5263_:
{
lean_object* v___x_5267_; 
if (v_isShared_5265_ == 0)
{
v___x_5267_ = v___x_5264_;
goto v_reusejp_5266_;
}
else
{
lean_object* v_reuseFailAlloc_5268_; 
v_reuseFailAlloc_5268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5268_, 0, v_a_5262_);
v___x_5267_ = v_reuseFailAlloc_5268_;
goto v_reusejp_5266_;
}
v_reusejp_5266_:
{
return v___x_5267_;
}
}
}
}
else
{
lean_object* v___x_5270_; 
lean_dec_ref(v___y_5250_);
lean_dec(v___y_5246_);
v___x_5270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5270_, 0, v___y_5247_);
return v___x_5270_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1___boxed(lean_object* v_mvarId_5483_, lean_object* v___x_5484_, lean_object* v_fvarIdsToSimp_5485_, lean_object* v_sz_5486_, lean_object* v___x_5487_, lean_object* v___x_5488_, lean_object* v_simplifyTarget_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_, lean_object* v___y_5494_, lean_object* v___y_5495_, lean_object* v___y_5496_){
_start:
{
size_t v_sz_boxed_5497_; size_t v___x_53511__boxed_5498_; uint8_t v_simplifyTarget_boxed_5499_; lean_object* v_res_5500_; 
v_sz_boxed_5497_ = lean_unbox_usize(v_sz_5486_);
lean_dec(v_sz_5486_);
v___x_53511__boxed_5498_ = lean_unbox_usize(v___x_5487_);
lean_dec(v___x_5487_);
v_simplifyTarget_boxed_5499_ = lean_unbox(v_simplifyTarget_5489_);
v_res_5500_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1(v_mvarId_5483_, v___x_5484_, v_fvarIdsToSimp_5485_, v_sz_boxed_5497_, v___x_53511__boxed_5498_, v___x_5488_, v_simplifyTarget_boxed_5499_, v___y_5490_, v___y_5491_, v___y_5492_, v___y_5493_, v___y_5494_, v___y_5495_);
lean_dec(v___y_5495_);
lean_dec_ref(v___y_5494_);
lean_dec(v___y_5493_);
lean_dec_ref(v___y_5492_);
lean_dec(v___y_5491_);
lean_dec_ref(v___y_5490_);
lean_dec_ref(v_fvarIdsToSimp_5485_);
return v_res_5500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore(lean_object* v_mvarId_5508_, uint8_t v_simplifyTarget_5509_, lean_object* v_fvarIdsToSimp_5510_, lean_object* v_a_5511_, lean_object* v_a_5512_, lean_object* v_a_5513_, lean_object* v_a_5514_, lean_object* v_a_5515_, lean_object* v_a_5516_){
_start:
{
lean_object* v_options_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; size_t v_sz_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___f_5528_; lean_object* v___x_5529_; 
v_options_5518_ = lean_ctor_get(v_a_5515_, 2);
v___x_5519_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_5520_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_5518_, v___x_5519_);
v___x_5521_ = lean_unsigned_to_nat(2u);
v___x_5522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5522_, 0, v___x_5520_);
lean_ctor_set(v___x_5522_, 1, v___x_5521_);
v___x_5523_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___closed__1));
v_sz_5524_ = lean_array_size(v_fvarIdsToSimp_5510_);
v___x_5525_ = lean_box_usize(v_sz_5524_);
v___x_5526_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___boxed__const__1));
v___x_5527_ = lean_box(v_simplifyTarget_5509_);
lean_inc(v_mvarId_5508_);
v___f_5528_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1___boxed), 14, 7);
lean_closure_set(v___f_5528_, 0, v_mvarId_5508_);
lean_closure_set(v___f_5528_, 1, v___x_5522_);
lean_closure_set(v___f_5528_, 2, v_fvarIdsToSimp_5510_);
lean_closure_set(v___f_5528_, 3, v___x_5525_);
lean_closure_set(v___f_5528_, 4, v___x_5526_);
lean_closure_set(v___f_5528_, 5, v___x_5523_);
lean_closure_set(v___f_5528_, 6, v___x_5527_);
v___x_5529_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg(v_mvarId_5508_, v___f_5528_, v_a_5511_, v_a_5512_, v_a_5513_, v_a_5514_, v_a_5515_, v_a_5516_);
return v___x_5529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___boxed(lean_object* v_mvarId_5530_, lean_object* v_simplifyTarget_5531_, lean_object* v_fvarIdsToSimp_5532_, lean_object* v_a_5533_, lean_object* v_a_5534_, lean_object* v_a_5535_, lean_object* v_a_5536_, lean_object* v_a_5537_, lean_object* v_a_5538_, lean_object* v_a_5539_){
_start:
{
uint8_t v_simplifyTarget_boxed_5540_; lean_object* v_res_5541_; 
v_simplifyTarget_boxed_5540_ = lean_unbox(v_simplifyTarget_5531_);
v_res_5541_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore(v_mvarId_5530_, v_simplifyTarget_boxed_5540_, v_fvarIdsToSimp_5532_, v_a_5533_, v_a_5534_, v_a_5535_, v_a_5536_, v_a_5537_, v_a_5538_);
lean_dec(v_a_5538_);
lean_dec_ref(v_a_5537_);
lean_dec(v_a_5536_);
lean_dec_ref(v_a_5535_);
lean_dec(v_a_5534_);
lean_dec_ref(v_a_5533_);
return v_res_5541_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0(lean_object* v_mvarId_5542_, lean_object* v_val_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_, lean_object* v___y_5546_, lean_object* v___y_5547_, lean_object* v___y_5548_, lean_object* v___y_5549_){
_start:
{
lean_object* v___x_5551_; 
v___x_5551_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(v_mvarId_5542_, v_val_5543_, v___y_5547_);
return v___x_5551_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___boxed(lean_object* v_mvarId_5552_, lean_object* v_val_5553_, lean_object* v___y_5554_, lean_object* v___y_5555_, lean_object* v___y_5556_, lean_object* v___y_5557_, lean_object* v___y_5558_, lean_object* v___y_5559_, lean_object* v___y_5560_){
_start:
{
lean_object* v_res_5561_; 
v_res_5561_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0(v_mvarId_5552_, v_val_5553_, v___y_5554_, v___y_5555_, v___y_5556_, v___y_5557_, v___y_5558_, v___y_5559_);
lean_dec(v___y_5559_);
lean_dec_ref(v___y_5558_);
lean_dec(v___y_5557_);
lean_dec_ref(v___y_5556_);
lean_dec(v___y_5555_);
lean_dec_ref(v___y_5554_);
return v_res_5561_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4(lean_object* v_00_u03b1_5562_, lean_object* v_x_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_, lean_object* v___y_5568_, lean_object* v___y_5569_){
_start:
{
lean_object* v___x_5571_; 
v___x_5571_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(v_x_5563_);
return v___x_5571_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___boxed(lean_object* v_00_u03b1_5572_, lean_object* v_x_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_, lean_object* v___y_5576_, lean_object* v___y_5577_, lean_object* v___y_5578_, lean_object* v___y_5579_, lean_object* v___y_5580_){
_start:
{
lean_object* v_res_5581_; 
v_res_5581_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4(v_00_u03b1_5572_, v_x_5573_, v___y_5574_, v___y_5575_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_);
lean_dec(v___y_5579_);
lean_dec_ref(v___y_5578_);
lean_dec(v___y_5577_);
lean_dec_ref(v___y_5576_);
lean_dec(v___y_5575_);
lean_dec_ref(v___y_5574_);
return v_res_5581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0(lean_object* v_00_u03b2_5582_, lean_object* v_x_5583_, lean_object* v_x_5584_, lean_object* v_x_5585_){
_start:
{
lean_object* v___x_5586_; 
v___x_5586_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0___redArg(v_x_5583_, v_x_5584_, v_x_5585_);
return v___x_5586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3(lean_object* v_oldTraces_5587_, lean_object* v_data_5588_, lean_object* v_ref_5589_, lean_object* v_msg_5590_, lean_object* v___y_5591_, lean_object* v___y_5592_, lean_object* v___y_5593_, lean_object* v___y_5594_, lean_object* v___y_5595_, lean_object* v___y_5596_){
_start:
{
lean_object* v___x_5598_; 
v___x_5598_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg(v_oldTraces_5587_, v_data_5588_, v_ref_5589_, v_msg_5590_, v___y_5593_, v___y_5594_, v___y_5595_, v___y_5596_);
return v___x_5598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___boxed(lean_object* v_oldTraces_5599_, lean_object* v_data_5600_, lean_object* v_ref_5601_, lean_object* v_msg_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_, lean_object* v___y_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_){
_start:
{
lean_object* v_res_5610_; 
v_res_5610_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3(v_oldTraces_5599_, v_data_5600_, v_ref_5601_, v_msg_5602_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_, v___y_5607_, v___y_5608_);
lean_dec(v___y_5608_);
lean_dec_ref(v___y_5607_);
lean_dec(v___y_5606_);
lean_dec_ref(v___y_5605_);
lean_dec(v___y_5604_);
lean_dec_ref(v___y_5603_);
return v_res_5610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_5611_, lean_object* v_x_5612_, size_t v_x_5613_, size_t v_x_5614_, lean_object* v_x_5615_, lean_object* v_x_5616_){
_start:
{
lean_object* v___x_5617_; 
v___x_5617_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_x_5612_, v_x_5613_, v_x_5614_, v_x_5615_, v_x_5616_);
return v___x_5617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_5618_, lean_object* v_x_5619_, lean_object* v_x_5620_, lean_object* v_x_5621_, lean_object* v_x_5622_, lean_object* v_x_5623_){
_start:
{
size_t v_x_54144__boxed_5624_; size_t v_x_54145__boxed_5625_; lean_object* v_res_5626_; 
v_x_54144__boxed_5624_ = lean_unbox_usize(v_x_5620_);
lean_dec(v_x_5620_);
v_x_54145__boxed_5625_ = lean_unbox_usize(v_x_5621_);
lean_dec(v_x_5621_);
v_res_5626_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3(v_00_u03b2_5618_, v_x_5619_, v_x_54144__boxed_5624_, v_x_54145__boxed_5625_, v_x_5622_, v_x_5623_);
return v_res_5626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7(lean_object* v_00_u03b2_5627_, lean_object* v_n_5628_, lean_object* v_k_5629_, lean_object* v_v_5630_){
_start:
{
lean_object* v___x_5631_; 
v___x_5631_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7___redArg(v_n_5628_, v_k_5629_, v_v_5630_);
return v___x_5631_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8(lean_object* v_00_u03b2_5632_, size_t v_depth_5633_, lean_object* v_keys_5634_, lean_object* v_vals_5635_, lean_object* v_heq_5636_, lean_object* v_i_5637_, lean_object* v_entries_5638_){
_start:
{
lean_object* v___x_5639_; 
v___x_5639_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg(v_depth_5633_, v_keys_5634_, v_vals_5635_, v_i_5637_, v_entries_5638_);
return v___x_5639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___boxed(lean_object* v_00_u03b2_5640_, lean_object* v_depth_5641_, lean_object* v_keys_5642_, lean_object* v_vals_5643_, lean_object* v_heq_5644_, lean_object* v_i_5645_, lean_object* v_entries_5646_){
_start:
{
size_t v_depth_boxed_5647_; lean_object* v_res_5648_; 
v_depth_boxed_5647_ = lean_unbox_usize(v_depth_5641_);
lean_dec(v_depth_5641_);
v_res_5648_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8(v_00_u03b2_5640_, v_depth_boxed_5647_, v_keys_5642_, v_vals_5643_, v_heq_5644_, v_i_5645_, v_entries_5646_);
lean_dec_ref(v_vals_5643_);
lean_dec_ref(v_keys_5642_);
return v_res_5648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9(lean_object* v_00_u03b2_5649_, lean_object* v_x_5650_, lean_object* v_x_5651_, lean_object* v_x_5652_, lean_object* v_x_5653_){
_start:
{
lean_object* v___x_5654_; 
v___x_5654_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_x_5650_, v_x_5651_, v_x_5652_, v_x_5653_);
return v___x_5654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0(lean_object* v_mvarId_5655_, uint8_t v_simplifyTarget_5656_, lean_object* v_fvarIdsToSimp_5657_, lean_object* v___y_5658_, lean_object* v___y_5659_, lean_object* v___y_5660_, lean_object* v___y_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_){
_start:
{
lean_object* v___x_5665_; 
v___x_5665_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_5655_, v___y_5658_, v___y_5659_, v___y_5660_, v___y_5661_, v___y_5662_, v___y_5663_);
if (lean_obj_tag(v___x_5665_) == 0)
{
lean_object* v_a_5666_; lean_object* v___x_5667_; 
v_a_5666_ = lean_ctor_get(v___x_5665_, 0);
lean_inc(v_a_5666_);
lean_dec_ref_known(v___x_5665_, 1);
v___x_5667_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore(v_a_5666_, v_simplifyTarget_5656_, v_fvarIdsToSimp_5657_, v___y_5658_, v___y_5659_, v___y_5660_, v___y_5661_, v___y_5662_, v___y_5663_);
return v___x_5667_;
}
else
{
lean_object* v_a_5668_; lean_object* v___x_5670_; uint8_t v_isShared_5671_; uint8_t v_isSharedCheck_5675_; 
lean_dec_ref(v_fvarIdsToSimp_5657_);
v_a_5668_ = lean_ctor_get(v___x_5665_, 0);
v_isSharedCheck_5675_ = !lean_is_exclusive(v___x_5665_);
if (v_isSharedCheck_5675_ == 0)
{
v___x_5670_ = v___x_5665_;
v_isShared_5671_ = v_isSharedCheck_5675_;
goto v_resetjp_5669_;
}
else
{
lean_inc(v_a_5668_);
lean_dec(v___x_5665_);
v___x_5670_ = lean_box(0);
v_isShared_5671_ = v_isSharedCheck_5675_;
goto v_resetjp_5669_;
}
v_resetjp_5669_:
{
lean_object* v___x_5673_; 
if (v_isShared_5671_ == 0)
{
v___x_5673_ = v___x_5670_;
goto v_reusejp_5672_;
}
else
{
lean_object* v_reuseFailAlloc_5674_; 
v_reuseFailAlloc_5674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5674_, 0, v_a_5668_);
v___x_5673_ = v_reuseFailAlloc_5674_;
goto v_reusejp_5672_;
}
v_reusejp_5672_:
{
return v___x_5673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___boxed(lean_object* v_mvarId_5676_, lean_object* v_simplifyTarget_5677_, lean_object* v_fvarIdsToSimp_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_){
_start:
{
uint8_t v_simplifyTarget_boxed_5686_; lean_object* v_res_5687_; 
v_simplifyTarget_boxed_5686_ = lean_unbox(v_simplifyTarget_5677_);
v_res_5687_ = l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0(v_mvarId_5676_, v_simplifyTarget_boxed_5686_, v_fvarIdsToSimp_5678_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_);
lean_dec(v___y_5684_);
lean_dec_ref(v___y_5683_);
lean_dec(v___y_5682_);
lean_dec_ref(v___y_5681_);
lean_dec(v___y_5680_);
lean_dec_ref(v___y_5679_);
return v_res_5687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal(lean_object* v_mvarId_5688_, uint8_t v_simplifyTarget_5689_, lean_object* v_fvarIdsToSimp_5690_, lean_object* v_a_5691_, lean_object* v_a_5692_, lean_object* v_a_5693_, lean_object* v_a_5694_){
_start:
{
lean_object* v___x_5696_; lean_object* v___f_5697_; lean_object* v___x_5698_; 
v___x_5696_ = lean_box(v_simplifyTarget_5689_);
v___f_5697_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5697_, 0, v_mvarId_5688_);
lean_closure_set(v___f_5697_, 1, v___x_5696_);
lean_closure_set(v___f_5697_, 2, v_fvarIdsToSimp_5690_);
v___x_5698_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_5697_, v_a_5691_, v_a_5692_, v_a_5693_, v_a_5694_);
return v___x_5698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___boxed(lean_object* v_mvarId_5699_, lean_object* v_simplifyTarget_5700_, lean_object* v_fvarIdsToSimp_5701_, lean_object* v_a_5702_, lean_object* v_a_5703_, lean_object* v_a_5704_, lean_object* v_a_5705_, lean_object* v_a_5706_){
_start:
{
uint8_t v_simplifyTarget_boxed_5707_; lean_object* v_res_5708_; 
v_simplifyTarget_boxed_5707_ = lean_unbox(v_simplifyTarget_5700_);
v_res_5708_ = l_Lean_Meta_Tactic_Cbv_cbvGoal(v_mvarId_5699_, v_simplifyTarget_boxed_5707_, v_fvarIdsToSimp_5701_, v_a_5702_, v_a_5703_, v_a_5704_, v_a_5705_);
lean_dec(v_a_5705_);
lean_dec_ref(v_a_5704_);
lean_dec(v_a_5703_);
lean_dec_ref(v_a_5702_);
return v_res_5708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0(lean_object* v_a_5709_, uint8_t v___x_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_, lean_object* v___y_5715_, lean_object* v___y_5716_){
_start:
{
lean_object* v___x_5718_; 
v___x_5718_ = l_Lean_MVarId_refl(v_a_5709_, v___x_5710_, v___y_5713_, v___y_5714_, v___y_5715_, v___y_5716_);
return v___x_5718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed(lean_object* v_a_5719_, lean_object* v___x_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_, lean_object* v___y_5727_){
_start:
{
uint8_t v___x_25154__boxed_5728_; lean_object* v_res_5729_; 
v___x_25154__boxed_5728_ = lean_unbox(v___x_5720_);
v_res_5729_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0(v_a_5719_, v___x_25154__boxed_5728_, v___y_5721_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_, v___y_5726_);
lean_dec(v___y_5726_);
lean_dec_ref(v___y_5725_);
lean_dec(v___y_5724_);
lean_dec_ref(v___y_5723_);
lean_dec(v___y_5722_);
lean_dec_ref(v___y_5721_);
return v_res_5729_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(lean_object* v_cls_5730_, lean_object* v_msg_5731_, lean_object* v___y_5732_, lean_object* v___y_5733_, lean_object* v___y_5734_, lean_object* v___y_5735_){
_start:
{
lean_object* v_ref_5737_; lean_object* v___x_5738_; lean_object* v_a_5739_; lean_object* v___x_5741_; uint8_t v_isShared_5742_; uint8_t v_isSharedCheck_5783_; 
v_ref_5737_ = lean_ctor_get(v___y_5734_, 5);
v___x_5738_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_5731_, v___y_5732_, v___y_5733_, v___y_5734_, v___y_5735_);
v_a_5739_ = lean_ctor_get(v___x_5738_, 0);
v_isSharedCheck_5783_ = !lean_is_exclusive(v___x_5738_);
if (v_isSharedCheck_5783_ == 0)
{
v___x_5741_ = v___x_5738_;
v_isShared_5742_ = v_isSharedCheck_5783_;
goto v_resetjp_5740_;
}
else
{
lean_inc(v_a_5739_);
lean_dec(v___x_5738_);
v___x_5741_ = lean_box(0);
v_isShared_5742_ = v_isSharedCheck_5783_;
goto v_resetjp_5740_;
}
v_resetjp_5740_:
{
lean_object* v___x_5743_; lean_object* v_traceState_5744_; lean_object* v_env_5745_; lean_object* v_nextMacroScope_5746_; lean_object* v_ngen_5747_; lean_object* v_auxDeclNGen_5748_; lean_object* v_cache_5749_; lean_object* v_messages_5750_; lean_object* v_infoState_5751_; lean_object* v_snapshotTasks_5752_; lean_object* v___x_5754_; uint8_t v_isShared_5755_; uint8_t v_isSharedCheck_5782_; 
v___x_5743_ = lean_st_ref_take(v___y_5735_);
v_traceState_5744_ = lean_ctor_get(v___x_5743_, 4);
v_env_5745_ = lean_ctor_get(v___x_5743_, 0);
v_nextMacroScope_5746_ = lean_ctor_get(v___x_5743_, 1);
v_ngen_5747_ = lean_ctor_get(v___x_5743_, 2);
v_auxDeclNGen_5748_ = lean_ctor_get(v___x_5743_, 3);
v_cache_5749_ = lean_ctor_get(v___x_5743_, 5);
v_messages_5750_ = lean_ctor_get(v___x_5743_, 6);
v_infoState_5751_ = lean_ctor_get(v___x_5743_, 7);
v_snapshotTasks_5752_ = lean_ctor_get(v___x_5743_, 8);
v_isSharedCheck_5782_ = !lean_is_exclusive(v___x_5743_);
if (v_isSharedCheck_5782_ == 0)
{
v___x_5754_ = v___x_5743_;
v_isShared_5755_ = v_isSharedCheck_5782_;
goto v_resetjp_5753_;
}
else
{
lean_inc(v_snapshotTasks_5752_);
lean_inc(v_infoState_5751_);
lean_inc(v_messages_5750_);
lean_inc(v_cache_5749_);
lean_inc(v_traceState_5744_);
lean_inc(v_auxDeclNGen_5748_);
lean_inc(v_ngen_5747_);
lean_inc(v_nextMacroScope_5746_);
lean_inc(v_env_5745_);
lean_dec(v___x_5743_);
v___x_5754_ = lean_box(0);
v_isShared_5755_ = v_isSharedCheck_5782_;
goto v_resetjp_5753_;
}
v_resetjp_5753_:
{
uint64_t v_tid_5756_; lean_object* v_traces_5757_; lean_object* v___x_5759_; uint8_t v_isShared_5760_; uint8_t v_isSharedCheck_5781_; 
v_tid_5756_ = lean_ctor_get_uint64(v_traceState_5744_, sizeof(void*)*1);
v_traces_5757_ = lean_ctor_get(v_traceState_5744_, 0);
v_isSharedCheck_5781_ = !lean_is_exclusive(v_traceState_5744_);
if (v_isSharedCheck_5781_ == 0)
{
v___x_5759_ = v_traceState_5744_;
v_isShared_5760_ = v_isSharedCheck_5781_;
goto v_resetjp_5758_;
}
else
{
lean_inc(v_traces_5757_);
lean_dec(v_traceState_5744_);
v___x_5759_ = lean_box(0);
v_isShared_5760_ = v_isSharedCheck_5781_;
goto v_resetjp_5758_;
}
v_resetjp_5758_:
{
lean_object* v___x_5761_; double v___x_5762_; uint8_t v___x_5763_; lean_object* v___x_5764_; lean_object* v___x_5765_; lean_object* v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5771_; 
v___x_5761_ = lean_box(0);
v___x_5762_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
v___x_5763_ = 0;
v___x_5764_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_5765_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5765_, 0, v_cls_5730_);
lean_ctor_set(v___x_5765_, 1, v___x_5761_);
lean_ctor_set(v___x_5765_, 2, v___x_5764_);
lean_ctor_set_float(v___x_5765_, sizeof(void*)*3, v___x_5762_);
lean_ctor_set_float(v___x_5765_, sizeof(void*)*3 + 8, v___x_5762_);
lean_ctor_set_uint8(v___x_5765_, sizeof(void*)*3 + 16, v___x_5763_);
v___x_5766_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__2));
v___x_5767_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5767_, 0, v___x_5765_);
lean_ctor_set(v___x_5767_, 1, v_a_5739_);
lean_ctor_set(v___x_5767_, 2, v___x_5766_);
lean_inc(v_ref_5737_);
v___x_5768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5768_, 0, v_ref_5737_);
lean_ctor_set(v___x_5768_, 1, v___x_5767_);
v___x_5769_ = l_Lean_PersistentArray_push___redArg(v_traces_5757_, v___x_5768_);
if (v_isShared_5760_ == 0)
{
lean_ctor_set(v___x_5759_, 0, v___x_5769_);
v___x_5771_ = v___x_5759_;
goto v_reusejp_5770_;
}
else
{
lean_object* v_reuseFailAlloc_5780_; 
v_reuseFailAlloc_5780_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5780_, 0, v___x_5769_);
lean_ctor_set_uint64(v_reuseFailAlloc_5780_, sizeof(void*)*1, v_tid_5756_);
v___x_5771_ = v_reuseFailAlloc_5780_;
goto v_reusejp_5770_;
}
v_reusejp_5770_:
{
lean_object* v___x_5773_; 
if (v_isShared_5755_ == 0)
{
lean_ctor_set(v___x_5754_, 4, v___x_5771_);
v___x_5773_ = v___x_5754_;
goto v_reusejp_5772_;
}
else
{
lean_object* v_reuseFailAlloc_5779_; 
v_reuseFailAlloc_5779_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5779_, 0, v_env_5745_);
lean_ctor_set(v_reuseFailAlloc_5779_, 1, v_nextMacroScope_5746_);
lean_ctor_set(v_reuseFailAlloc_5779_, 2, v_ngen_5747_);
lean_ctor_set(v_reuseFailAlloc_5779_, 3, v_auxDeclNGen_5748_);
lean_ctor_set(v_reuseFailAlloc_5779_, 4, v___x_5771_);
lean_ctor_set(v_reuseFailAlloc_5779_, 5, v_cache_5749_);
lean_ctor_set(v_reuseFailAlloc_5779_, 6, v_messages_5750_);
lean_ctor_set(v_reuseFailAlloc_5779_, 7, v_infoState_5751_);
lean_ctor_set(v_reuseFailAlloc_5779_, 8, v_snapshotTasks_5752_);
v___x_5773_ = v_reuseFailAlloc_5779_;
goto v_reusejp_5772_;
}
v_reusejp_5772_:
{
lean_object* v___x_5774_; lean_object* v___x_5775_; lean_object* v___x_5777_; 
v___x_5774_ = lean_st_ref_set(v___y_5735_, v___x_5773_);
v___x_5775_ = lean_box(0);
if (v_isShared_5742_ == 0)
{
lean_ctor_set(v___x_5741_, 0, v___x_5775_);
v___x_5777_ = v___x_5741_;
goto v_reusejp_5776_;
}
else
{
lean_object* v_reuseFailAlloc_5778_; 
v_reuseFailAlloc_5778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5778_, 0, v___x_5775_);
v___x_5777_ = v_reuseFailAlloc_5778_;
goto v_reusejp_5776_;
}
v_reusejp_5776_:
{
return v___x_5777_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg___boxed(lean_object* v_cls_5784_, lean_object* v_msg_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_, lean_object* v___y_5789_, lean_object* v___y_5790_){
_start:
{
lean_object* v_res_5791_; 
v_res_5791_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_5784_, v_msg_5785_, v___y_5786_, v___y_5787_, v___y_5788_, v___y_5789_);
lean_dec(v___y_5789_);
lean_dec_ref(v___y_5788_);
lean_dec(v___y_5787_);
lean_dec_ref(v___y_5786_);
return v_res_5791_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(lean_object* v_msg_5792_, lean_object* v___y_5793_, lean_object* v___y_5794_, lean_object* v___y_5795_, lean_object* v___y_5796_){
_start:
{
lean_object* v_ref_5798_; lean_object* v___x_5799_; lean_object* v_a_5800_; lean_object* v___x_5802_; uint8_t v_isShared_5803_; uint8_t v_isSharedCheck_5808_; 
v_ref_5798_ = lean_ctor_get(v___y_5795_, 5);
v___x_5799_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_5792_, v___y_5793_, v___y_5794_, v___y_5795_, v___y_5796_);
v_a_5800_ = lean_ctor_get(v___x_5799_, 0);
v_isSharedCheck_5808_ = !lean_is_exclusive(v___x_5799_);
if (v_isSharedCheck_5808_ == 0)
{
v___x_5802_ = v___x_5799_;
v_isShared_5803_ = v_isSharedCheck_5808_;
goto v_resetjp_5801_;
}
else
{
lean_inc(v_a_5800_);
lean_dec(v___x_5799_);
v___x_5802_ = lean_box(0);
v_isShared_5803_ = v_isSharedCheck_5808_;
goto v_resetjp_5801_;
}
v_resetjp_5801_:
{
lean_object* v___x_5804_; lean_object* v___x_5806_; 
lean_inc(v_ref_5798_);
v___x_5804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5804_, 0, v_ref_5798_);
lean_ctor_set(v___x_5804_, 1, v_a_5800_);
if (v_isShared_5803_ == 0)
{
lean_ctor_set_tag(v___x_5802_, 1);
lean_ctor_set(v___x_5802_, 0, v___x_5804_);
v___x_5806_ = v___x_5802_;
goto v_reusejp_5805_;
}
else
{
lean_object* v_reuseFailAlloc_5807_; 
v_reuseFailAlloc_5807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5807_, 0, v___x_5804_);
v___x_5806_ = v_reuseFailAlloc_5807_;
goto v_reusejp_5805_;
}
v_reusejp_5805_:
{
return v___x_5806_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg___boxed(lean_object* v_msg_5809_, lean_object* v___y_5810_, lean_object* v___y_5811_, lean_object* v___y_5812_, lean_object* v___y_5813_, lean_object* v___y_5814_){
_start:
{
lean_object* v_res_5815_; 
v_res_5815_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v_msg_5809_, v___y_5810_, v___y_5811_, v___y_5812_, v___y_5813_);
lean_dec(v___y_5813_);
lean_dec_ref(v___y_5812_);
lean_dec(v___y_5811_);
lean_dec_ref(v___y_5810_);
return v_res_5815_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5817_; lean_object* v___x_5818_; 
v___x_5817_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__0));
v___x_5818_ = l_Lean_stringToMessageData(v___x_5817_);
return v___x_5818_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3(void){
_start:
{
lean_object* v___x_5820_; lean_object* v___x_5821_; 
v___x_5820_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__2));
v___x_5821_ = l_Lean_stringToMessageData(v___x_5820_);
return v___x_5821_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6(void){
_start:
{
lean_object* v___x_5825_; lean_object* v___x_5826_; 
v___x_5825_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__5));
v___x_5826_ = l_Lean_stringToMessageData(v___x_5825_);
return v___x_5826_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8(void){
_start:
{
lean_object* v___x_5828_; lean_object* v___x_5829_; 
v___x_5828_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__7));
v___x_5829_ = l_Lean_stringToMessageData(v___x_5828_);
return v___x_5829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1(lean_object* v_m_5830_, lean_object* v___x_5831_, lean_object* v_cls_5832_, lean_object* v___y_5833_, lean_object* v___y_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_){
_start:
{
lean_object* v_e_5841_; lean_object* v_onTrue_5842_; lean_object* v___y_5843_; lean_object* v___y_5844_; lean_object* v___y_5845_; lean_object* v___y_5846_; lean_object* v___y_5847_; lean_object* v___y_5848_; lean_object* v___x_5878_; 
v___x_5878_ = l_Lean_Meta_Sym_preprocessMVar(v_m_5830_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_);
if (lean_obj_tag(v___x_5878_) == 0)
{
lean_object* v_a_5879_; lean_object* v___x_5880_; 
v_a_5879_ = lean_ctor_get(v___x_5878_, 0);
lean_inc_n(v_a_5879_, 2);
lean_dec_ref_known(v___x_5878_, 1);
v___x_5880_ = l_Lean_MVarId_getType(v_a_5879_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_);
if (lean_obj_tag(v___x_5880_) == 0)
{
lean_object* v_a_5881_; lean_object* v___x_5882_; lean_object* v___x_5883_; uint8_t v___x_5884_; 
v_a_5881_ = lean_ctor_get(v___x_5880_, 0);
lean_inc(v_a_5881_);
lean_dec_ref_known(v___x_5880_, 1);
v___x_5882_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4));
v___x_5883_ = lean_unsigned_to_nat(3u);
v___x_5884_ = l_Lean_Expr_isAppOfArity(v_a_5881_, v___x_5882_, v___x_5883_);
if (v___x_5884_ == 0)
{
lean_object* v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; 
lean_dec(v_a_5879_);
lean_dec(v_cls_5832_);
lean_dec_ref(v___x_5831_);
v___x_5885_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6);
v___x_5886_ = l_Lean_indentExpr(v_a_5881_);
v___x_5887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5887_, 0, v___x_5885_);
lean_ctor_set(v___x_5887_, 1, v___x_5886_);
v___x_5888_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5887_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_);
return v___x_5888_;
}
else
{
lean_object* v___x_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; 
v___x_5889_ = l_Lean_Expr_appFn_x21(v_a_5881_);
lean_dec(v_a_5881_);
v___x_5890_ = l_Lean_Expr_appArg_x21(v___x_5889_);
lean_dec_ref(v___x_5889_);
lean_inc_ref(v___x_5890_);
v___x_5891_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5890_, v___x_5831_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_);
if (lean_obj_tag(v___x_5891_) == 0)
{
lean_object* v_options_5892_; lean_object* v_a_5893_; lean_object* v_inheritedTraceOptions_5894_; uint8_t v_hasTrace_5895_; lean_object* v___x_5896_; lean_object* v___f_5897_; lean_object* v___y_5899_; lean_object* v___y_5900_; lean_object* v___y_5901_; lean_object* v___y_5902_; lean_object* v___y_5903_; lean_object* v___y_5904_; 
v_options_5892_ = lean_ctor_get(v___y_5837_, 2);
v_a_5893_ = lean_ctor_get(v___x_5891_, 0);
lean_inc(v_a_5893_);
lean_dec_ref_known(v___x_5891_, 1);
v_inheritedTraceOptions_5894_ = lean_ctor_get(v___y_5837_, 13);
v_hasTrace_5895_ = lean_ctor_get_uint8(v_options_5892_, sizeof(void*)*1);
v___x_5896_ = lean_box(v___x_5884_);
lean_inc(v_a_5879_);
v___f_5897_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5897_, 0, v_a_5879_);
lean_closure_set(v___f_5897_, 1, v___x_5896_);
if (v_hasTrace_5895_ == 0)
{
lean_dec(v_cls_5832_);
v___y_5899_ = v___y_5833_;
v___y_5900_ = v___y_5834_;
v___y_5901_ = v___y_5835_;
v___y_5902_ = v___y_5836_;
v___y_5903_ = v___y_5837_;
v___y_5904_ = v___y_5838_;
goto v___jp_5898_;
}
else
{
lean_object* v___x_5908_; lean_object* v___x_5909_; uint8_t v___x_5910_; 
v___x_5908_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
lean_inc(v_cls_5832_);
v___x_5909_ = l_Lean_Name_append(v___x_5908_, v_cls_5832_);
v___x_5910_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5894_, v_options_5892_, v___x_5909_);
lean_dec(v___x_5909_);
if (v___x_5910_ == 0)
{
lean_dec(v_cls_5832_);
v___y_5899_ = v___y_5833_;
v___y_5900_ = v___y_5834_;
v___y_5901_ = v___y_5835_;
v___y_5902_ = v___y_5836_;
v___y_5903_ = v___y_5837_;
v___y_5904_ = v___y_5838_;
goto v___jp_5898_;
}
else
{
lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; 
v___x_5911_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8);
lean_inc_ref(v___x_5890_);
v___x_5912_ = l_Lean_indentExpr(v___x_5890_);
v___x_5913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5913_, 0, v___x_5911_);
lean_ctor_set(v___x_5913_, 1, v___x_5912_);
v___x_5914_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_5915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5915_, 0, v___x_5913_);
lean_ctor_set(v___x_5915_, 1, v___x_5914_);
v___x_5916_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_5890_, v_a_5893_);
v___x_5917_ = l_Lean_indentExpr(v___x_5916_);
v___x_5918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5918_, 0, v___x_5915_);
lean_ctor_set(v___x_5918_, 1, v___x_5917_);
v___x_5919_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_5832_, v___x_5918_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_);
if (lean_obj_tag(v___x_5919_) == 0)
{
lean_dec_ref_known(v___x_5919_, 1);
v___y_5899_ = v___y_5833_;
v___y_5900_ = v___y_5834_;
v___y_5901_ = v___y_5835_;
v___y_5902_ = v___y_5836_;
v___y_5903_ = v___y_5837_;
v___y_5904_ = v___y_5838_;
goto v___jp_5898_;
}
else
{
lean_dec_ref(v___f_5897_);
lean_dec(v_a_5893_);
lean_dec_ref(v___x_5890_);
lean_dec(v_a_5879_);
return v___x_5919_;
}
}
}
v___jp_5898_:
{
if (lean_obj_tag(v_a_5893_) == 0)
{
lean_dec_ref_known(v_a_5893_, 0);
lean_dec(v_a_5879_);
v_e_5841_ = v___x_5890_;
v_onTrue_5842_ = v___f_5897_;
v___y_5843_ = v___y_5899_;
v___y_5844_ = v___y_5900_;
v___y_5845_ = v___y_5901_;
v___y_5846_ = v___y_5902_;
v___y_5847_ = v___y_5903_;
v___y_5848_ = v___y_5904_;
goto v___jp_5840_;
}
else
{
lean_object* v_e_x27_5905_; lean_object* v_proof_5906_; lean_object* v___x_5907_; 
lean_dec_ref(v___f_5897_);
lean_dec_ref(v___x_5890_);
v_e_x27_5905_ = lean_ctor_get(v_a_5893_, 0);
lean_inc_ref(v_e_x27_5905_);
v_proof_5906_ = lean_ctor_get(v_a_5893_, 1);
lean_inc_ref(v_proof_5906_);
lean_dec_ref_known(v_a_5893_, 2);
v___x_5907_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_5907_, 0, v_a_5879_);
lean_closure_set(v___x_5907_, 1, v_proof_5906_);
v_e_5841_ = v_e_x27_5905_;
v_onTrue_5842_ = v___x_5907_;
v___y_5843_ = v___y_5899_;
v___y_5844_ = v___y_5900_;
v___y_5845_ = v___y_5901_;
v___y_5846_ = v___y_5902_;
v___y_5847_ = v___y_5903_;
v___y_5848_ = v___y_5904_;
goto v___jp_5840_;
}
}
}
else
{
lean_object* v_a_5920_; lean_object* v___x_5922_; uint8_t v_isShared_5923_; uint8_t v_isSharedCheck_5927_; 
lean_dec_ref(v___x_5890_);
lean_dec(v_a_5879_);
lean_dec(v_cls_5832_);
v_a_5920_ = lean_ctor_get(v___x_5891_, 0);
v_isSharedCheck_5927_ = !lean_is_exclusive(v___x_5891_);
if (v_isSharedCheck_5927_ == 0)
{
v___x_5922_ = v___x_5891_;
v_isShared_5923_ = v_isSharedCheck_5927_;
goto v_resetjp_5921_;
}
else
{
lean_inc(v_a_5920_);
lean_dec(v___x_5891_);
v___x_5922_ = lean_box(0);
v_isShared_5923_ = v_isSharedCheck_5927_;
goto v_resetjp_5921_;
}
v_resetjp_5921_:
{
lean_object* v___x_5925_; 
if (v_isShared_5923_ == 0)
{
v___x_5925_ = v___x_5922_;
goto v_reusejp_5924_;
}
else
{
lean_object* v_reuseFailAlloc_5926_; 
v_reuseFailAlloc_5926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5926_, 0, v_a_5920_);
v___x_5925_ = v_reuseFailAlloc_5926_;
goto v_reusejp_5924_;
}
v_reusejp_5924_:
{
return v___x_5925_;
}
}
}
}
}
else
{
lean_object* v_a_5928_; lean_object* v___x_5930_; uint8_t v_isShared_5931_; uint8_t v_isSharedCheck_5935_; 
lean_dec(v_a_5879_);
lean_dec(v_cls_5832_);
lean_dec_ref(v___x_5831_);
v_a_5928_ = lean_ctor_get(v___x_5880_, 0);
v_isSharedCheck_5935_ = !lean_is_exclusive(v___x_5880_);
if (v_isSharedCheck_5935_ == 0)
{
v___x_5930_ = v___x_5880_;
v_isShared_5931_ = v_isSharedCheck_5935_;
goto v_resetjp_5929_;
}
else
{
lean_inc(v_a_5928_);
lean_dec(v___x_5880_);
v___x_5930_ = lean_box(0);
v_isShared_5931_ = v_isSharedCheck_5935_;
goto v_resetjp_5929_;
}
v_resetjp_5929_:
{
lean_object* v___x_5933_; 
if (v_isShared_5931_ == 0)
{
v___x_5933_ = v___x_5930_;
goto v_reusejp_5932_;
}
else
{
lean_object* v_reuseFailAlloc_5934_; 
v_reuseFailAlloc_5934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5934_, 0, v_a_5928_);
v___x_5933_ = v_reuseFailAlloc_5934_;
goto v_reusejp_5932_;
}
v_reusejp_5932_:
{
return v___x_5933_;
}
}
}
}
else
{
lean_object* v_a_5936_; lean_object* v___x_5938_; uint8_t v_isShared_5939_; uint8_t v_isSharedCheck_5943_; 
lean_dec(v_cls_5832_);
lean_dec_ref(v___x_5831_);
v_a_5936_ = lean_ctor_get(v___x_5878_, 0);
v_isSharedCheck_5943_ = !lean_is_exclusive(v___x_5878_);
if (v_isSharedCheck_5943_ == 0)
{
v___x_5938_ = v___x_5878_;
v_isShared_5939_ = v_isSharedCheck_5943_;
goto v_resetjp_5937_;
}
else
{
lean_inc(v_a_5936_);
lean_dec(v___x_5878_);
v___x_5938_ = lean_box(0);
v_isShared_5939_ = v_isSharedCheck_5943_;
goto v_resetjp_5937_;
}
v_resetjp_5937_:
{
lean_object* v___x_5941_; 
if (v_isShared_5939_ == 0)
{
v___x_5941_ = v___x_5938_;
goto v_reusejp_5940_;
}
else
{
lean_object* v_reuseFailAlloc_5942_; 
v_reuseFailAlloc_5942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5942_, 0, v_a_5936_);
v___x_5941_ = v_reuseFailAlloc_5942_;
goto v_reusejp_5940_;
}
v_reusejp_5940_:
{
return v___x_5941_;
}
}
}
v___jp_5840_:
{
lean_object* v___x_5849_; 
v___x_5849_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_5841_, v___y_5843_);
if (lean_obj_tag(v___x_5849_) == 0)
{
lean_object* v_a_5850_; uint8_t v___x_5851_; 
v_a_5850_ = lean_ctor_get(v___x_5849_, 0);
lean_inc(v_a_5850_);
lean_dec_ref_known(v___x_5849_, 1);
v___x_5851_ = lean_unbox(v_a_5850_);
lean_dec(v_a_5850_);
if (v___x_5851_ == 0)
{
lean_object* v___x_5852_; 
lean_dec_ref(v_onTrue_5842_);
v___x_5852_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_5841_, v___y_5843_);
if (lean_obj_tag(v___x_5852_) == 0)
{
lean_object* v_a_5853_; uint8_t v___x_5854_; 
v_a_5853_ = lean_ctor_get(v___x_5852_, 0);
lean_inc(v_a_5853_);
lean_dec_ref_known(v___x_5852_, 1);
v___x_5854_ = lean_unbox(v_a_5853_);
lean_dec(v_a_5853_);
if (v___x_5854_ == 0)
{
lean_object* v___x_5855_; lean_object* v___x_5856_; lean_object* v___x_5857_; lean_object* v___x_5858_; 
v___x_5855_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1);
v___x_5856_ = l_Lean_indentExpr(v_e_5841_);
v___x_5857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5857_, 0, v___x_5855_);
lean_ctor_set(v___x_5857_, 1, v___x_5856_);
v___x_5858_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5857_, v___y_5845_, v___y_5846_, v___y_5847_, v___y_5848_);
return v___x_5858_;
}
else
{
lean_object* v___x_5859_; lean_object* v___x_5860_; 
lean_dec_ref(v_e_5841_);
v___x_5859_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3);
v___x_5860_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5859_, v___y_5845_, v___y_5846_, v___y_5847_, v___y_5848_);
return v___x_5860_;
}
}
else
{
lean_object* v_a_5861_; lean_object* v___x_5863_; uint8_t v_isShared_5864_; uint8_t v_isSharedCheck_5868_; 
lean_dec_ref(v_e_5841_);
v_a_5861_ = lean_ctor_get(v___x_5852_, 0);
v_isSharedCheck_5868_ = !lean_is_exclusive(v___x_5852_);
if (v_isSharedCheck_5868_ == 0)
{
v___x_5863_ = v___x_5852_;
v_isShared_5864_ = v_isSharedCheck_5868_;
goto v_resetjp_5862_;
}
else
{
lean_inc(v_a_5861_);
lean_dec(v___x_5852_);
v___x_5863_ = lean_box(0);
v_isShared_5864_ = v_isSharedCheck_5868_;
goto v_resetjp_5862_;
}
v_resetjp_5862_:
{
lean_object* v___x_5866_; 
if (v_isShared_5864_ == 0)
{
v___x_5866_ = v___x_5863_;
goto v_reusejp_5865_;
}
else
{
lean_object* v_reuseFailAlloc_5867_; 
v_reuseFailAlloc_5867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5867_, 0, v_a_5861_);
v___x_5866_ = v_reuseFailAlloc_5867_;
goto v_reusejp_5865_;
}
v_reusejp_5865_:
{
return v___x_5866_;
}
}
}
}
else
{
lean_object* v___x_5869_; 
lean_dec_ref(v_e_5841_);
lean_inc(v___y_5848_);
lean_inc_ref(v___y_5847_);
lean_inc(v___y_5846_);
lean_inc_ref(v___y_5845_);
lean_inc(v___y_5844_);
lean_inc_ref(v___y_5843_);
v___x_5869_ = lean_apply_7(v_onTrue_5842_, v___y_5843_, v___y_5844_, v___y_5845_, v___y_5846_, v___y_5847_, v___y_5848_, lean_box(0));
return v___x_5869_;
}
}
else
{
lean_object* v_a_5870_; lean_object* v___x_5872_; uint8_t v_isShared_5873_; uint8_t v_isSharedCheck_5877_; 
lean_dec_ref(v_onTrue_5842_);
lean_dec_ref(v_e_5841_);
v_a_5870_ = lean_ctor_get(v___x_5849_, 0);
v_isSharedCheck_5877_ = !lean_is_exclusive(v___x_5849_);
if (v_isSharedCheck_5877_ == 0)
{
v___x_5872_ = v___x_5849_;
v_isShared_5873_ = v_isSharedCheck_5877_;
goto v_resetjp_5871_;
}
else
{
lean_inc(v_a_5870_);
lean_dec(v___x_5849_);
v___x_5872_ = lean_box(0);
v_isShared_5873_ = v_isSharedCheck_5877_;
goto v_resetjp_5871_;
}
v_resetjp_5871_:
{
lean_object* v___x_5875_; 
if (v_isShared_5873_ == 0)
{
v___x_5875_ = v___x_5872_;
goto v_reusejp_5874_;
}
else
{
lean_object* v_reuseFailAlloc_5876_; 
v_reuseFailAlloc_5876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5876_, 0, v_a_5870_);
v___x_5875_ = v_reuseFailAlloc_5876_;
goto v_reusejp_5874_;
}
v_reusejp_5874_:
{
return v___x_5875_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___boxed(lean_object* v_m_5944_, lean_object* v___x_5945_, lean_object* v_cls_5946_, lean_object* v___y_5947_, lean_object* v___y_5948_, lean_object* v___y_5949_, lean_object* v___y_5950_, lean_object* v___y_5951_, lean_object* v___y_5952_, lean_object* v___y_5953_){
_start:
{
lean_object* v_res_5954_; 
v_res_5954_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1(v_m_5944_, v___x_5945_, v_cls_5946_, v___y_5947_, v___y_5948_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_);
lean_dec(v___y_5952_);
lean_dec_ref(v___y_5951_);
lean_dec(v___y_5950_);
lean_dec_ref(v___y_5949_);
lean_dec(v___y_5948_);
lean_dec_ref(v___y_5947_);
return v_res_5954_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1(void){
_start:
{
lean_object* v___x_5956_; lean_object* v___x_5957_; 
v___x_5956_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__0));
v___x_5957_ = l_Lean_stringToMessageData(v___x_5956_);
return v___x_5957_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3(void){
_start:
{
lean_object* v___x_5959_; lean_object* v___x_5960_; 
v___x_5959_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__2));
v___x_5960_ = l_Lean_stringToMessageData(v___x_5959_);
return v___x_5960_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2(lean_object* v_x_5961_, lean_object* v___y_5962_, lean_object* v___y_5963_, lean_object* v___y_5964_, lean_object* v___y_5965_){
_start:
{
if (lean_obj_tag(v_x_5961_) == 0)
{
lean_object* v_a_5967_; lean_object* v___x_5969_; uint8_t v_isShared_5970_; uint8_t v_isSharedCheck_5977_; 
v_a_5967_ = lean_ctor_get(v_x_5961_, 0);
v_isSharedCheck_5977_ = !lean_is_exclusive(v_x_5961_);
if (v_isSharedCheck_5977_ == 0)
{
v___x_5969_ = v_x_5961_;
v_isShared_5970_ = v_isSharedCheck_5977_;
goto v_resetjp_5968_;
}
else
{
lean_inc(v_a_5967_);
lean_dec(v_x_5961_);
v___x_5969_ = lean_box(0);
v_isShared_5970_ = v_isSharedCheck_5977_;
goto v_resetjp_5968_;
}
v_resetjp_5968_:
{
lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5975_; 
v___x_5971_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1);
v___x_5972_ = l_Lean_Exception_toMessageData(v_a_5967_);
v___x_5973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5973_, 0, v___x_5971_);
lean_ctor_set(v___x_5973_, 1, v___x_5972_);
if (v_isShared_5970_ == 0)
{
lean_ctor_set(v___x_5969_, 0, v___x_5973_);
v___x_5975_ = v___x_5969_;
goto v_reusejp_5974_;
}
else
{
lean_object* v_reuseFailAlloc_5976_; 
v_reuseFailAlloc_5976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5976_, 0, v___x_5973_);
v___x_5975_ = v_reuseFailAlloc_5976_;
goto v_reusejp_5974_;
}
v_reusejp_5974_:
{
return v___x_5975_;
}
}
}
else
{
lean_object* v___x_5979_; uint8_t v_isShared_5980_; uint8_t v_isSharedCheck_5985_; 
v_isSharedCheck_5985_ = !lean_is_exclusive(v_x_5961_);
if (v_isSharedCheck_5985_ == 0)
{
lean_object* v_unused_5986_; 
v_unused_5986_ = lean_ctor_get(v_x_5961_, 0);
lean_dec(v_unused_5986_);
v___x_5979_ = v_x_5961_;
v_isShared_5980_ = v_isSharedCheck_5985_;
goto v_resetjp_5978_;
}
else
{
lean_dec(v_x_5961_);
v___x_5979_ = lean_box(0);
v_isShared_5980_ = v_isSharedCheck_5985_;
goto v_resetjp_5978_;
}
v_resetjp_5978_:
{
lean_object* v___x_5981_; lean_object* v___x_5983_; 
v___x_5981_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3);
if (v_isShared_5980_ == 0)
{
lean_ctor_set_tag(v___x_5979_, 0);
lean_ctor_set(v___x_5979_, 0, v___x_5981_);
v___x_5983_ = v___x_5979_;
goto v_reusejp_5982_;
}
else
{
lean_object* v_reuseFailAlloc_5984_; 
v_reuseFailAlloc_5984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5984_, 0, v___x_5981_);
v___x_5983_ = v_reuseFailAlloc_5984_;
goto v_reusejp_5982_;
}
v_reusejp_5982_:
{
return v___x_5983_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___boxed(lean_object* v_x_5987_, lean_object* v___y_5988_, lean_object* v___y_5989_, lean_object* v___y_5990_, lean_object* v___y_5991_, lean_object* v___y_5992_){
_start:
{
lean_object* v_res_5993_; 
v_res_5993_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2(v_x_5987_, v___y_5988_, v___y_5989_, v___y_5990_, v___y_5991_);
lean_dec(v___y_5991_);
lean_dec_ref(v___y_5990_);
lean_dec(v___y_5989_);
lean_dec_ref(v___y_5988_);
return v_res_5993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3(lean_object* v_a_5994_, uint8_t v_hasTrace_5995_, lean_object* v___y_5996_, lean_object* v___y_5997_, lean_object* v___y_5998_, lean_object* v___y_5999_, lean_object* v___y_6000_, lean_object* v___y_6001_){
_start:
{
lean_object* v___x_6003_; 
v___x_6003_ = l_Lean_MVarId_refl(v_a_5994_, v_hasTrace_5995_, v___y_5998_, v___y_5999_, v___y_6000_, v___y_6001_);
return v___x_6003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3___boxed(lean_object* v_a_6004_, lean_object* v_hasTrace_6005_, lean_object* v___y_6006_, lean_object* v___y_6007_, lean_object* v___y_6008_, lean_object* v___y_6009_, lean_object* v___y_6010_, lean_object* v___y_6011_, lean_object* v___y_6012_){
_start:
{
uint8_t v_hasTrace_boxed_6013_; lean_object* v_res_6014_; 
v_hasTrace_boxed_6013_ = lean_unbox(v_hasTrace_6005_);
v_res_6014_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3(v_a_6004_, v_hasTrace_boxed_6013_, v___y_6006_, v___y_6007_, v___y_6008_, v___y_6009_, v___y_6010_, v___y_6011_);
lean_dec(v___y_6011_);
lean_dec_ref(v___y_6010_);
lean_dec(v___y_6009_);
lean_dec_ref(v___y_6008_);
lean_dec(v___y_6007_);
lean_dec_ref(v___y_6006_);
return v_res_6014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4(lean_object* v_m_6015_, lean_object* v___x_6016_, uint8_t v_hasTrace_6017_, lean_object* v_cls_6018_, lean_object* v___y_6019_, lean_object* v___y_6020_, lean_object* v___y_6021_, lean_object* v___y_6022_, lean_object* v___y_6023_, lean_object* v___y_6024_){
_start:
{
lean_object* v_e_6027_; lean_object* v_onTrue_6028_; lean_object* v___y_6029_; lean_object* v___y_6030_; lean_object* v___y_6031_; lean_object* v___y_6032_; lean_object* v___y_6033_; lean_object* v___y_6034_; lean_object* v___x_6064_; 
v___x_6064_ = l_Lean_Meta_Sym_preprocessMVar(v_m_6015_, v___y_6019_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_, v___y_6024_);
if (lean_obj_tag(v___x_6064_) == 0)
{
lean_object* v_a_6065_; lean_object* v___x_6066_; 
v_a_6065_ = lean_ctor_get(v___x_6064_, 0);
lean_inc_n(v_a_6065_, 2);
lean_dec_ref_known(v___x_6064_, 1);
v___x_6066_ = l_Lean_MVarId_getType(v_a_6065_, v___y_6021_, v___y_6022_, v___y_6023_, v___y_6024_);
if (lean_obj_tag(v___x_6066_) == 0)
{
lean_object* v_a_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; uint8_t v___x_6070_; 
v_a_6067_ = lean_ctor_get(v___x_6066_, 0);
lean_inc(v_a_6067_);
lean_dec_ref_known(v___x_6066_, 1);
v___x_6068_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4));
v___x_6069_ = lean_unsigned_to_nat(3u);
v___x_6070_ = l_Lean_Expr_isAppOfArity(v_a_6067_, v___x_6068_, v___x_6069_);
if (v___x_6070_ == 0)
{
lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; 
lean_dec(v_a_6065_);
lean_dec(v_cls_6018_);
lean_dec_ref(v___x_6016_);
v___x_6071_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6);
v___x_6072_ = l_Lean_indentExpr(v_a_6067_);
v___x_6073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6073_, 0, v___x_6071_);
lean_ctor_set(v___x_6073_, 1, v___x_6072_);
v___x_6074_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6073_, v___y_6021_, v___y_6022_, v___y_6023_, v___y_6024_);
return v___x_6074_;
}
else
{
lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; 
v___x_6075_ = l_Lean_Expr_appFn_x21(v_a_6067_);
lean_dec(v_a_6067_);
v___x_6076_ = l_Lean_Expr_appArg_x21(v___x_6075_);
lean_dec_ref(v___x_6075_);
lean_inc_ref(v___x_6076_);
v___x_6077_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_6076_, v___x_6016_, v___y_6019_, v___y_6020_, v___y_6021_, v___y_6022_, v___y_6023_, v___y_6024_);
if (lean_obj_tag(v___x_6077_) == 0)
{
lean_object* v_options_6078_; lean_object* v_a_6079_; lean_object* v_inheritedTraceOptions_6080_; uint8_t v_hasTrace_6081_; lean_object* v___x_6082_; lean_object* v___f_6083_; lean_object* v___y_6085_; lean_object* v___y_6086_; lean_object* v___y_6087_; lean_object* v___y_6088_; lean_object* v___y_6089_; lean_object* v___y_6090_; 
v_options_6078_ = lean_ctor_get(v___y_6023_, 2);
v_a_6079_ = lean_ctor_get(v___x_6077_, 0);
lean_inc(v_a_6079_);
lean_dec_ref_known(v___x_6077_, 1);
v_inheritedTraceOptions_6080_ = lean_ctor_get(v___y_6023_, 13);
v_hasTrace_6081_ = lean_ctor_get_uint8(v_options_6078_, sizeof(void*)*1);
v___x_6082_ = lean_box(v_hasTrace_6017_);
lean_inc(v_a_6065_);
v___f_6083_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3___boxed), 9, 2);
lean_closure_set(v___f_6083_, 0, v_a_6065_);
lean_closure_set(v___f_6083_, 1, v___x_6082_);
if (v_hasTrace_6081_ == 0)
{
lean_dec(v_cls_6018_);
v___y_6085_ = v___y_6019_;
v___y_6086_ = v___y_6020_;
v___y_6087_ = v___y_6021_;
v___y_6088_ = v___y_6022_;
v___y_6089_ = v___y_6023_;
v___y_6090_ = v___y_6024_;
goto v___jp_6084_;
}
else
{
lean_object* v___x_6094_; lean_object* v___x_6095_; uint8_t v___x_6096_; 
v___x_6094_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
lean_inc(v_cls_6018_);
v___x_6095_ = l_Lean_Name_append(v___x_6094_, v_cls_6018_);
v___x_6096_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6080_, v_options_6078_, v___x_6095_);
lean_dec(v___x_6095_);
if (v___x_6096_ == 0)
{
lean_dec(v_cls_6018_);
v___y_6085_ = v___y_6019_;
v___y_6086_ = v___y_6020_;
v___y_6087_ = v___y_6021_;
v___y_6088_ = v___y_6022_;
v___y_6089_ = v___y_6023_;
v___y_6090_ = v___y_6024_;
goto v___jp_6084_;
}
else
{
lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; 
v___x_6097_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8);
lean_inc_ref(v___x_6076_);
v___x_6098_ = l_Lean_indentExpr(v___x_6076_);
v___x_6099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6099_, 0, v___x_6097_);
lean_ctor_set(v___x_6099_, 1, v___x_6098_);
v___x_6100_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_6101_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6101_, 0, v___x_6099_);
lean_ctor_set(v___x_6101_, 1, v___x_6100_);
v___x_6102_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_6076_, v_a_6079_);
v___x_6103_ = l_Lean_indentExpr(v___x_6102_);
v___x_6104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6104_, 0, v___x_6101_);
lean_ctor_set(v___x_6104_, 1, v___x_6103_);
v___x_6105_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_6018_, v___x_6104_, v___y_6021_, v___y_6022_, v___y_6023_, v___y_6024_);
if (lean_obj_tag(v___x_6105_) == 0)
{
lean_dec_ref_known(v___x_6105_, 1);
v___y_6085_ = v___y_6019_;
v___y_6086_ = v___y_6020_;
v___y_6087_ = v___y_6021_;
v___y_6088_ = v___y_6022_;
v___y_6089_ = v___y_6023_;
v___y_6090_ = v___y_6024_;
goto v___jp_6084_;
}
else
{
lean_dec_ref(v___f_6083_);
lean_dec(v_a_6079_);
lean_dec_ref(v___x_6076_);
lean_dec(v_a_6065_);
return v___x_6105_;
}
}
}
v___jp_6084_:
{
if (lean_obj_tag(v_a_6079_) == 0)
{
lean_dec_ref_known(v_a_6079_, 0);
lean_dec(v_a_6065_);
v_e_6027_ = v___x_6076_;
v_onTrue_6028_ = v___f_6083_;
v___y_6029_ = v___y_6085_;
v___y_6030_ = v___y_6086_;
v___y_6031_ = v___y_6087_;
v___y_6032_ = v___y_6088_;
v___y_6033_ = v___y_6089_;
v___y_6034_ = v___y_6090_;
goto v___jp_6026_;
}
else
{
lean_object* v_e_x27_6091_; lean_object* v_proof_6092_; lean_object* v___x_6093_; 
lean_dec_ref(v___f_6083_);
lean_dec_ref(v___x_6076_);
v_e_x27_6091_ = lean_ctor_get(v_a_6079_, 0);
lean_inc_ref(v_e_x27_6091_);
v_proof_6092_ = lean_ctor_get(v_a_6079_, 1);
lean_inc_ref(v_proof_6092_);
lean_dec_ref_known(v_a_6079_, 2);
v___x_6093_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_6093_, 0, v_a_6065_);
lean_closure_set(v___x_6093_, 1, v_proof_6092_);
v_e_6027_ = v_e_x27_6091_;
v_onTrue_6028_ = v___x_6093_;
v___y_6029_ = v___y_6085_;
v___y_6030_ = v___y_6086_;
v___y_6031_ = v___y_6087_;
v___y_6032_ = v___y_6088_;
v___y_6033_ = v___y_6089_;
v___y_6034_ = v___y_6090_;
goto v___jp_6026_;
}
}
}
else
{
lean_object* v_a_6106_; lean_object* v___x_6108_; uint8_t v_isShared_6109_; uint8_t v_isSharedCheck_6113_; 
lean_dec_ref(v___x_6076_);
lean_dec(v_a_6065_);
lean_dec(v_cls_6018_);
v_a_6106_ = lean_ctor_get(v___x_6077_, 0);
v_isSharedCheck_6113_ = !lean_is_exclusive(v___x_6077_);
if (v_isSharedCheck_6113_ == 0)
{
v___x_6108_ = v___x_6077_;
v_isShared_6109_ = v_isSharedCheck_6113_;
goto v_resetjp_6107_;
}
else
{
lean_inc(v_a_6106_);
lean_dec(v___x_6077_);
v___x_6108_ = lean_box(0);
v_isShared_6109_ = v_isSharedCheck_6113_;
goto v_resetjp_6107_;
}
v_resetjp_6107_:
{
lean_object* v___x_6111_; 
if (v_isShared_6109_ == 0)
{
v___x_6111_ = v___x_6108_;
goto v_reusejp_6110_;
}
else
{
lean_object* v_reuseFailAlloc_6112_; 
v_reuseFailAlloc_6112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6112_, 0, v_a_6106_);
v___x_6111_ = v_reuseFailAlloc_6112_;
goto v_reusejp_6110_;
}
v_reusejp_6110_:
{
return v___x_6111_;
}
}
}
}
}
else
{
lean_object* v_a_6114_; lean_object* v___x_6116_; uint8_t v_isShared_6117_; uint8_t v_isSharedCheck_6121_; 
lean_dec(v_a_6065_);
lean_dec(v_cls_6018_);
lean_dec_ref(v___x_6016_);
v_a_6114_ = lean_ctor_get(v___x_6066_, 0);
v_isSharedCheck_6121_ = !lean_is_exclusive(v___x_6066_);
if (v_isSharedCheck_6121_ == 0)
{
v___x_6116_ = v___x_6066_;
v_isShared_6117_ = v_isSharedCheck_6121_;
goto v_resetjp_6115_;
}
else
{
lean_inc(v_a_6114_);
lean_dec(v___x_6066_);
v___x_6116_ = lean_box(0);
v_isShared_6117_ = v_isSharedCheck_6121_;
goto v_resetjp_6115_;
}
v_resetjp_6115_:
{
lean_object* v___x_6119_; 
if (v_isShared_6117_ == 0)
{
v___x_6119_ = v___x_6116_;
goto v_reusejp_6118_;
}
else
{
lean_object* v_reuseFailAlloc_6120_; 
v_reuseFailAlloc_6120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6120_, 0, v_a_6114_);
v___x_6119_ = v_reuseFailAlloc_6120_;
goto v_reusejp_6118_;
}
v_reusejp_6118_:
{
return v___x_6119_;
}
}
}
}
else
{
lean_object* v_a_6122_; lean_object* v___x_6124_; uint8_t v_isShared_6125_; uint8_t v_isSharedCheck_6129_; 
lean_dec(v_cls_6018_);
lean_dec_ref(v___x_6016_);
v_a_6122_ = lean_ctor_get(v___x_6064_, 0);
v_isSharedCheck_6129_ = !lean_is_exclusive(v___x_6064_);
if (v_isSharedCheck_6129_ == 0)
{
v___x_6124_ = v___x_6064_;
v_isShared_6125_ = v_isSharedCheck_6129_;
goto v_resetjp_6123_;
}
else
{
lean_inc(v_a_6122_);
lean_dec(v___x_6064_);
v___x_6124_ = lean_box(0);
v_isShared_6125_ = v_isSharedCheck_6129_;
goto v_resetjp_6123_;
}
v_resetjp_6123_:
{
lean_object* v___x_6127_; 
if (v_isShared_6125_ == 0)
{
v___x_6127_ = v___x_6124_;
goto v_reusejp_6126_;
}
else
{
lean_object* v_reuseFailAlloc_6128_; 
v_reuseFailAlloc_6128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6128_, 0, v_a_6122_);
v___x_6127_ = v_reuseFailAlloc_6128_;
goto v_reusejp_6126_;
}
v_reusejp_6126_:
{
return v___x_6127_;
}
}
}
v___jp_6026_:
{
lean_object* v___x_6035_; 
v___x_6035_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_6027_, v___y_6029_);
if (lean_obj_tag(v___x_6035_) == 0)
{
lean_object* v_a_6036_; uint8_t v___x_6037_; 
v_a_6036_ = lean_ctor_get(v___x_6035_, 0);
lean_inc(v_a_6036_);
lean_dec_ref_known(v___x_6035_, 1);
v___x_6037_ = lean_unbox(v_a_6036_);
lean_dec(v_a_6036_);
if (v___x_6037_ == 0)
{
lean_object* v___x_6038_; 
lean_dec_ref(v_onTrue_6028_);
v___x_6038_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_6027_, v___y_6029_);
if (lean_obj_tag(v___x_6038_) == 0)
{
lean_object* v_a_6039_; uint8_t v___x_6040_; 
v_a_6039_ = lean_ctor_get(v___x_6038_, 0);
lean_inc(v_a_6039_);
lean_dec_ref_known(v___x_6038_, 1);
v___x_6040_ = lean_unbox(v_a_6039_);
lean_dec(v_a_6039_);
if (v___x_6040_ == 0)
{
lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; 
v___x_6041_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1);
v___x_6042_ = l_Lean_indentExpr(v_e_6027_);
v___x_6043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6043_, 0, v___x_6041_);
lean_ctor_set(v___x_6043_, 1, v___x_6042_);
v___x_6044_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6043_, v___y_6031_, v___y_6032_, v___y_6033_, v___y_6034_);
return v___x_6044_;
}
else
{
lean_object* v___x_6045_; lean_object* v___x_6046_; 
lean_dec_ref(v_e_6027_);
v___x_6045_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3);
v___x_6046_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6045_, v___y_6031_, v___y_6032_, v___y_6033_, v___y_6034_);
return v___x_6046_;
}
}
else
{
lean_object* v_a_6047_; lean_object* v___x_6049_; uint8_t v_isShared_6050_; uint8_t v_isSharedCheck_6054_; 
lean_dec_ref(v_e_6027_);
v_a_6047_ = lean_ctor_get(v___x_6038_, 0);
v_isSharedCheck_6054_ = !lean_is_exclusive(v___x_6038_);
if (v_isSharedCheck_6054_ == 0)
{
v___x_6049_ = v___x_6038_;
v_isShared_6050_ = v_isSharedCheck_6054_;
goto v_resetjp_6048_;
}
else
{
lean_inc(v_a_6047_);
lean_dec(v___x_6038_);
v___x_6049_ = lean_box(0);
v_isShared_6050_ = v_isSharedCheck_6054_;
goto v_resetjp_6048_;
}
v_resetjp_6048_:
{
lean_object* v___x_6052_; 
if (v_isShared_6050_ == 0)
{
v___x_6052_ = v___x_6049_;
goto v_reusejp_6051_;
}
else
{
lean_object* v_reuseFailAlloc_6053_; 
v_reuseFailAlloc_6053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6053_, 0, v_a_6047_);
v___x_6052_ = v_reuseFailAlloc_6053_;
goto v_reusejp_6051_;
}
v_reusejp_6051_:
{
return v___x_6052_;
}
}
}
}
else
{
lean_object* v___x_6055_; 
lean_dec_ref(v_e_6027_);
lean_inc(v___y_6034_);
lean_inc_ref(v___y_6033_);
lean_inc(v___y_6032_);
lean_inc_ref(v___y_6031_);
lean_inc(v___y_6030_);
lean_inc_ref(v___y_6029_);
v___x_6055_ = lean_apply_7(v_onTrue_6028_, v___y_6029_, v___y_6030_, v___y_6031_, v___y_6032_, v___y_6033_, v___y_6034_, lean_box(0));
return v___x_6055_;
}
}
else
{
lean_object* v_a_6056_; lean_object* v___x_6058_; uint8_t v_isShared_6059_; uint8_t v_isSharedCheck_6063_; 
lean_dec_ref(v_onTrue_6028_);
lean_dec_ref(v_e_6027_);
v_a_6056_ = lean_ctor_get(v___x_6035_, 0);
v_isSharedCheck_6063_ = !lean_is_exclusive(v___x_6035_);
if (v_isSharedCheck_6063_ == 0)
{
v___x_6058_ = v___x_6035_;
v_isShared_6059_ = v_isSharedCheck_6063_;
goto v_resetjp_6057_;
}
else
{
lean_inc(v_a_6056_);
lean_dec(v___x_6035_);
v___x_6058_ = lean_box(0);
v_isShared_6059_ = v_isSharedCheck_6063_;
goto v_resetjp_6057_;
}
v_resetjp_6057_:
{
lean_object* v___x_6061_; 
if (v_isShared_6059_ == 0)
{
v___x_6061_ = v___x_6058_;
goto v_reusejp_6060_;
}
else
{
lean_object* v_reuseFailAlloc_6062_; 
v_reuseFailAlloc_6062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6062_, 0, v_a_6056_);
v___x_6061_ = v_reuseFailAlloc_6062_;
goto v_reusejp_6060_;
}
v_reusejp_6060_:
{
return v___x_6061_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed(lean_object* v_m_6130_, lean_object* v___x_6131_, lean_object* v_hasTrace_6132_, lean_object* v_cls_6133_, lean_object* v___y_6134_, lean_object* v___y_6135_, lean_object* v___y_6136_, lean_object* v___y_6137_, lean_object* v___y_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_){
_start:
{
uint8_t v_hasTrace_boxed_6141_; lean_object* v_res_6142_; 
v_hasTrace_boxed_6141_ = lean_unbox(v_hasTrace_6132_);
v_res_6142_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4(v_m_6130_, v___x_6131_, v_hasTrace_boxed_6141_, v_cls_6133_, v___y_6134_, v___y_6135_, v___y_6136_, v___y_6137_, v___y_6138_, v___y_6139_);
lean_dec(v___y_6139_);
lean_dec_ref(v___y_6138_);
lean_dec(v___y_6137_);
lean_dec_ref(v___y_6136_);
lean_dec(v___y_6135_);
lean_dec_ref(v___y_6134_);
return v_res_6142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6(lean_object* v_m_6143_, lean_object* v___x_6144_, uint8_t v___x_6145_, lean_object* v_cls_6146_, lean_object* v___y_6147_, lean_object* v___y_6148_, lean_object* v___y_6149_, lean_object* v___y_6150_, lean_object* v___y_6151_, lean_object* v___y_6152_){
_start:
{
lean_object* v_e_6155_; lean_object* v_onTrue_6156_; lean_object* v___y_6157_; lean_object* v___y_6158_; lean_object* v___y_6159_; lean_object* v___y_6160_; lean_object* v___y_6161_; lean_object* v___y_6162_; lean_object* v___x_6192_; 
v___x_6192_ = l_Lean_Meta_Sym_preprocessMVar(v_m_6143_, v___y_6147_, v___y_6148_, v___y_6149_, v___y_6150_, v___y_6151_, v___y_6152_);
if (lean_obj_tag(v___x_6192_) == 0)
{
lean_object* v_a_6193_; lean_object* v___x_6194_; 
v_a_6193_ = lean_ctor_get(v___x_6192_, 0);
lean_inc_n(v_a_6193_, 2);
lean_dec_ref_known(v___x_6192_, 1);
v___x_6194_ = l_Lean_MVarId_getType(v_a_6193_, v___y_6149_, v___y_6150_, v___y_6151_, v___y_6152_);
if (lean_obj_tag(v___x_6194_) == 0)
{
lean_object* v_a_6195_; lean_object* v___x_6196_; lean_object* v___x_6197_; uint8_t v___x_6198_; 
v_a_6195_ = lean_ctor_get(v___x_6194_, 0);
lean_inc(v_a_6195_);
lean_dec_ref_known(v___x_6194_, 1);
v___x_6196_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4));
v___x_6197_ = lean_unsigned_to_nat(3u);
v___x_6198_ = l_Lean_Expr_isAppOfArity(v_a_6195_, v___x_6196_, v___x_6197_);
if (v___x_6198_ == 0)
{
lean_object* v___x_6199_; lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; 
lean_dec(v_a_6193_);
lean_dec(v_cls_6146_);
lean_dec_ref(v___x_6144_);
v___x_6199_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6);
v___x_6200_ = l_Lean_indentExpr(v_a_6195_);
v___x_6201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6201_, 0, v___x_6199_);
lean_ctor_set(v___x_6201_, 1, v___x_6200_);
v___x_6202_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6201_, v___y_6149_, v___y_6150_, v___y_6151_, v___y_6152_);
return v___x_6202_;
}
else
{
lean_object* v___x_6203_; lean_object* v___x_6204_; lean_object* v___x_6205_; 
v___x_6203_ = l_Lean_Expr_appFn_x21(v_a_6195_);
lean_dec(v_a_6195_);
v___x_6204_ = l_Lean_Expr_appArg_x21(v___x_6203_);
lean_dec_ref(v___x_6203_);
lean_inc_ref(v___x_6204_);
v___x_6205_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_6204_, v___x_6144_, v___y_6147_, v___y_6148_, v___y_6149_, v___y_6150_, v___y_6151_, v___y_6152_);
if (lean_obj_tag(v___x_6205_) == 0)
{
lean_object* v_options_6206_; lean_object* v_a_6207_; lean_object* v_inheritedTraceOptions_6208_; uint8_t v_hasTrace_6209_; lean_object* v___x_6210_; lean_object* v___f_6211_; lean_object* v___y_6213_; lean_object* v___y_6214_; lean_object* v___y_6215_; lean_object* v___y_6216_; lean_object* v___y_6217_; lean_object* v___y_6218_; 
v_options_6206_ = lean_ctor_get(v___y_6151_, 2);
v_a_6207_ = lean_ctor_get(v___x_6205_, 0);
lean_inc(v_a_6207_);
lean_dec_ref_known(v___x_6205_, 1);
v_inheritedTraceOptions_6208_ = lean_ctor_get(v___y_6151_, 13);
v_hasTrace_6209_ = lean_ctor_get_uint8(v_options_6206_, sizeof(void*)*1);
v___x_6210_ = lean_box(v___x_6145_);
lean_inc(v_a_6193_);
v___f_6211_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed), 9, 2);
lean_closure_set(v___f_6211_, 0, v_a_6193_);
lean_closure_set(v___f_6211_, 1, v___x_6210_);
if (v_hasTrace_6209_ == 0)
{
lean_dec(v_cls_6146_);
v___y_6213_ = v___y_6147_;
v___y_6214_ = v___y_6148_;
v___y_6215_ = v___y_6149_;
v___y_6216_ = v___y_6150_;
v___y_6217_ = v___y_6151_;
v___y_6218_ = v___y_6152_;
goto v___jp_6212_;
}
else
{
lean_object* v___x_6222_; lean_object* v___x_6223_; uint8_t v___x_6224_; 
v___x_6222_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
lean_inc(v_cls_6146_);
v___x_6223_ = l_Lean_Name_append(v___x_6222_, v_cls_6146_);
v___x_6224_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6208_, v_options_6206_, v___x_6223_);
lean_dec(v___x_6223_);
if (v___x_6224_ == 0)
{
lean_dec(v_cls_6146_);
v___y_6213_ = v___y_6147_;
v___y_6214_ = v___y_6148_;
v___y_6215_ = v___y_6149_;
v___y_6216_ = v___y_6150_;
v___y_6217_ = v___y_6151_;
v___y_6218_ = v___y_6152_;
goto v___jp_6212_;
}
else
{
lean_object* v___x_6225_; lean_object* v___x_6226_; lean_object* v___x_6227_; lean_object* v___x_6228_; lean_object* v___x_6229_; lean_object* v___x_6230_; lean_object* v___x_6231_; lean_object* v___x_6232_; lean_object* v___x_6233_; 
v___x_6225_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8);
lean_inc_ref(v___x_6204_);
v___x_6226_ = l_Lean_indentExpr(v___x_6204_);
v___x_6227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6227_, 0, v___x_6225_);
lean_ctor_set(v___x_6227_, 1, v___x_6226_);
v___x_6228_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_6229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6229_, 0, v___x_6227_);
lean_ctor_set(v___x_6229_, 1, v___x_6228_);
v___x_6230_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_6204_, v_a_6207_);
v___x_6231_ = l_Lean_indentExpr(v___x_6230_);
v___x_6232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6232_, 0, v___x_6229_);
lean_ctor_set(v___x_6232_, 1, v___x_6231_);
v___x_6233_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_6146_, v___x_6232_, v___y_6149_, v___y_6150_, v___y_6151_, v___y_6152_);
if (lean_obj_tag(v___x_6233_) == 0)
{
lean_dec_ref_known(v___x_6233_, 1);
v___y_6213_ = v___y_6147_;
v___y_6214_ = v___y_6148_;
v___y_6215_ = v___y_6149_;
v___y_6216_ = v___y_6150_;
v___y_6217_ = v___y_6151_;
v___y_6218_ = v___y_6152_;
goto v___jp_6212_;
}
else
{
lean_dec_ref(v___f_6211_);
lean_dec(v_a_6207_);
lean_dec_ref(v___x_6204_);
lean_dec(v_a_6193_);
return v___x_6233_;
}
}
}
v___jp_6212_:
{
if (lean_obj_tag(v_a_6207_) == 0)
{
lean_dec_ref_known(v_a_6207_, 0);
lean_dec(v_a_6193_);
v_e_6155_ = v___x_6204_;
v_onTrue_6156_ = v___f_6211_;
v___y_6157_ = v___y_6213_;
v___y_6158_ = v___y_6214_;
v___y_6159_ = v___y_6215_;
v___y_6160_ = v___y_6216_;
v___y_6161_ = v___y_6217_;
v___y_6162_ = v___y_6218_;
goto v___jp_6154_;
}
else
{
lean_object* v_e_x27_6219_; lean_object* v_proof_6220_; lean_object* v___x_6221_; 
lean_dec_ref(v___f_6211_);
lean_dec_ref(v___x_6204_);
v_e_x27_6219_ = lean_ctor_get(v_a_6207_, 0);
lean_inc_ref(v_e_x27_6219_);
v_proof_6220_ = lean_ctor_get(v_a_6207_, 1);
lean_inc_ref(v_proof_6220_);
lean_dec_ref_known(v_a_6207_, 2);
v___x_6221_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_6221_, 0, v_a_6193_);
lean_closure_set(v___x_6221_, 1, v_proof_6220_);
v_e_6155_ = v_e_x27_6219_;
v_onTrue_6156_ = v___x_6221_;
v___y_6157_ = v___y_6213_;
v___y_6158_ = v___y_6214_;
v___y_6159_ = v___y_6215_;
v___y_6160_ = v___y_6216_;
v___y_6161_ = v___y_6217_;
v___y_6162_ = v___y_6218_;
goto v___jp_6154_;
}
}
}
else
{
lean_object* v_a_6234_; lean_object* v___x_6236_; uint8_t v_isShared_6237_; uint8_t v_isSharedCheck_6241_; 
lean_dec_ref(v___x_6204_);
lean_dec(v_a_6193_);
lean_dec(v_cls_6146_);
v_a_6234_ = lean_ctor_get(v___x_6205_, 0);
v_isSharedCheck_6241_ = !lean_is_exclusive(v___x_6205_);
if (v_isSharedCheck_6241_ == 0)
{
v___x_6236_ = v___x_6205_;
v_isShared_6237_ = v_isSharedCheck_6241_;
goto v_resetjp_6235_;
}
else
{
lean_inc(v_a_6234_);
lean_dec(v___x_6205_);
v___x_6236_ = lean_box(0);
v_isShared_6237_ = v_isSharedCheck_6241_;
goto v_resetjp_6235_;
}
v_resetjp_6235_:
{
lean_object* v___x_6239_; 
if (v_isShared_6237_ == 0)
{
v___x_6239_ = v___x_6236_;
goto v_reusejp_6238_;
}
else
{
lean_object* v_reuseFailAlloc_6240_; 
v_reuseFailAlloc_6240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6240_, 0, v_a_6234_);
v___x_6239_ = v_reuseFailAlloc_6240_;
goto v_reusejp_6238_;
}
v_reusejp_6238_:
{
return v___x_6239_;
}
}
}
}
}
else
{
lean_object* v_a_6242_; lean_object* v___x_6244_; uint8_t v_isShared_6245_; uint8_t v_isSharedCheck_6249_; 
lean_dec(v_a_6193_);
lean_dec(v_cls_6146_);
lean_dec_ref(v___x_6144_);
v_a_6242_ = lean_ctor_get(v___x_6194_, 0);
v_isSharedCheck_6249_ = !lean_is_exclusive(v___x_6194_);
if (v_isSharedCheck_6249_ == 0)
{
v___x_6244_ = v___x_6194_;
v_isShared_6245_ = v_isSharedCheck_6249_;
goto v_resetjp_6243_;
}
else
{
lean_inc(v_a_6242_);
lean_dec(v___x_6194_);
v___x_6244_ = lean_box(0);
v_isShared_6245_ = v_isSharedCheck_6249_;
goto v_resetjp_6243_;
}
v_resetjp_6243_:
{
lean_object* v___x_6247_; 
if (v_isShared_6245_ == 0)
{
v___x_6247_ = v___x_6244_;
goto v_reusejp_6246_;
}
else
{
lean_object* v_reuseFailAlloc_6248_; 
v_reuseFailAlloc_6248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6248_, 0, v_a_6242_);
v___x_6247_ = v_reuseFailAlloc_6248_;
goto v_reusejp_6246_;
}
v_reusejp_6246_:
{
return v___x_6247_;
}
}
}
}
else
{
lean_object* v_a_6250_; lean_object* v___x_6252_; uint8_t v_isShared_6253_; uint8_t v_isSharedCheck_6257_; 
lean_dec(v_cls_6146_);
lean_dec_ref(v___x_6144_);
v_a_6250_ = lean_ctor_get(v___x_6192_, 0);
v_isSharedCheck_6257_ = !lean_is_exclusive(v___x_6192_);
if (v_isSharedCheck_6257_ == 0)
{
v___x_6252_ = v___x_6192_;
v_isShared_6253_ = v_isSharedCheck_6257_;
goto v_resetjp_6251_;
}
else
{
lean_inc(v_a_6250_);
lean_dec(v___x_6192_);
v___x_6252_ = lean_box(0);
v_isShared_6253_ = v_isSharedCheck_6257_;
goto v_resetjp_6251_;
}
v_resetjp_6251_:
{
lean_object* v___x_6255_; 
if (v_isShared_6253_ == 0)
{
v___x_6255_ = v___x_6252_;
goto v_reusejp_6254_;
}
else
{
lean_object* v_reuseFailAlloc_6256_; 
v_reuseFailAlloc_6256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6256_, 0, v_a_6250_);
v___x_6255_ = v_reuseFailAlloc_6256_;
goto v_reusejp_6254_;
}
v_reusejp_6254_:
{
return v___x_6255_;
}
}
}
v___jp_6154_:
{
lean_object* v___x_6163_; 
v___x_6163_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_6155_, v___y_6157_);
if (lean_obj_tag(v___x_6163_) == 0)
{
lean_object* v_a_6164_; uint8_t v___x_6165_; 
v_a_6164_ = lean_ctor_get(v___x_6163_, 0);
lean_inc(v_a_6164_);
lean_dec_ref_known(v___x_6163_, 1);
v___x_6165_ = lean_unbox(v_a_6164_);
lean_dec(v_a_6164_);
if (v___x_6165_ == 0)
{
lean_object* v___x_6166_; 
lean_dec_ref(v_onTrue_6156_);
v___x_6166_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_6155_, v___y_6157_);
if (lean_obj_tag(v___x_6166_) == 0)
{
lean_object* v_a_6167_; uint8_t v___x_6168_; 
v_a_6167_ = lean_ctor_get(v___x_6166_, 0);
lean_inc(v_a_6167_);
lean_dec_ref_known(v___x_6166_, 1);
v___x_6168_ = lean_unbox(v_a_6167_);
lean_dec(v_a_6167_);
if (v___x_6168_ == 0)
{
lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; 
v___x_6169_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1);
v___x_6170_ = l_Lean_indentExpr(v_e_6155_);
v___x_6171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6171_, 0, v___x_6169_);
lean_ctor_set(v___x_6171_, 1, v___x_6170_);
v___x_6172_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6171_, v___y_6159_, v___y_6160_, v___y_6161_, v___y_6162_);
return v___x_6172_;
}
else
{
lean_object* v___x_6173_; lean_object* v___x_6174_; 
lean_dec_ref(v_e_6155_);
v___x_6173_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3);
v___x_6174_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6173_, v___y_6159_, v___y_6160_, v___y_6161_, v___y_6162_);
return v___x_6174_;
}
}
else
{
lean_object* v_a_6175_; lean_object* v___x_6177_; uint8_t v_isShared_6178_; uint8_t v_isSharedCheck_6182_; 
lean_dec_ref(v_e_6155_);
v_a_6175_ = lean_ctor_get(v___x_6166_, 0);
v_isSharedCheck_6182_ = !lean_is_exclusive(v___x_6166_);
if (v_isSharedCheck_6182_ == 0)
{
v___x_6177_ = v___x_6166_;
v_isShared_6178_ = v_isSharedCheck_6182_;
goto v_resetjp_6176_;
}
else
{
lean_inc(v_a_6175_);
lean_dec(v___x_6166_);
v___x_6177_ = lean_box(0);
v_isShared_6178_ = v_isSharedCheck_6182_;
goto v_resetjp_6176_;
}
v_resetjp_6176_:
{
lean_object* v___x_6180_; 
if (v_isShared_6178_ == 0)
{
v___x_6180_ = v___x_6177_;
goto v_reusejp_6179_;
}
else
{
lean_object* v_reuseFailAlloc_6181_; 
v_reuseFailAlloc_6181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6181_, 0, v_a_6175_);
v___x_6180_ = v_reuseFailAlloc_6181_;
goto v_reusejp_6179_;
}
v_reusejp_6179_:
{
return v___x_6180_;
}
}
}
}
else
{
lean_object* v___x_6183_; 
lean_dec_ref(v_e_6155_);
lean_inc(v___y_6162_);
lean_inc_ref(v___y_6161_);
lean_inc(v___y_6160_);
lean_inc_ref(v___y_6159_);
lean_inc(v___y_6158_);
lean_inc_ref(v___y_6157_);
v___x_6183_ = lean_apply_7(v_onTrue_6156_, v___y_6157_, v___y_6158_, v___y_6159_, v___y_6160_, v___y_6161_, v___y_6162_, lean_box(0));
return v___x_6183_;
}
}
else
{
lean_object* v_a_6184_; lean_object* v___x_6186_; uint8_t v_isShared_6187_; uint8_t v_isSharedCheck_6191_; 
lean_dec_ref(v_onTrue_6156_);
lean_dec_ref(v_e_6155_);
v_a_6184_ = lean_ctor_get(v___x_6163_, 0);
v_isSharedCheck_6191_ = !lean_is_exclusive(v___x_6163_);
if (v_isSharedCheck_6191_ == 0)
{
v___x_6186_ = v___x_6163_;
v_isShared_6187_ = v_isSharedCheck_6191_;
goto v_resetjp_6185_;
}
else
{
lean_inc(v_a_6184_);
lean_dec(v___x_6163_);
v___x_6186_ = lean_box(0);
v_isShared_6187_ = v_isSharedCheck_6191_;
goto v_resetjp_6185_;
}
v_resetjp_6185_:
{
lean_object* v___x_6189_; 
if (v_isShared_6187_ == 0)
{
v___x_6189_ = v___x_6186_;
goto v_reusejp_6188_;
}
else
{
lean_object* v_reuseFailAlloc_6190_; 
v_reuseFailAlloc_6190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6190_, 0, v_a_6184_);
v___x_6189_ = v_reuseFailAlloc_6190_;
goto v_reusejp_6188_;
}
v_reusejp_6188_:
{
return v___x_6189_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6___boxed(lean_object* v_m_6258_, lean_object* v___x_6259_, lean_object* v___x_6260_, lean_object* v_cls_6261_, lean_object* v___y_6262_, lean_object* v___y_6263_, lean_object* v___y_6264_, lean_object* v___y_6265_, lean_object* v___y_6266_, lean_object* v___y_6267_, lean_object* v___y_6268_){
_start:
{
uint8_t v___x_25974__boxed_6269_; lean_object* v_res_6270_; 
v___x_25974__boxed_6269_ = lean_unbox(v___x_6260_);
v_res_6270_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6(v_m_6258_, v___x_6259_, v___x_25974__boxed_6269_, v_cls_6261_, v___y_6262_, v___y_6263_, v___y_6264_, v___y_6265_, v___y_6266_, v___y_6267_);
lean_dec(v___y_6267_);
lean_dec_ref(v___y_6266_);
lean_dec(v___y_6265_);
lean_dec_ref(v___y_6264_);
lean_dec(v___y_6263_);
lean_dec_ref(v___y_6262_);
return v_res_6270_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(lean_object* v_e_6271_){
_start:
{
if (lean_obj_tag(v_e_6271_) == 0)
{
uint8_t v___x_6272_; 
v___x_6272_ = 2;
return v___x_6272_;
}
else
{
uint8_t v___x_6273_; 
v___x_6273_ = 0;
return v___x_6273_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2___boxed(lean_object* v_e_6274_){
_start:
{
uint8_t v_res_6275_; lean_object* v_r_6276_; 
v_res_6275_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(v_e_6274_);
lean_dec_ref(v_e_6274_);
v_r_6276_ = lean_box(v_res_6275_);
return v_r_6276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(lean_object* v_cls_6277_, uint8_t v_collapsed_6278_, lean_object* v_tag_6279_, lean_object* v_opts_6280_, uint8_t v_clsEnabled_6281_, lean_object* v_oldTraces_6282_, lean_object* v_msg_6283_, lean_object* v_resStartStop_6284_, lean_object* v___y_6285_, lean_object* v___y_6286_, lean_object* v___y_6287_, lean_object* v___y_6288_){
_start:
{
lean_object* v_fst_6290_; lean_object* v_snd_6291_; lean_object* v___y_6293_; lean_object* v___y_6294_; lean_object* v_data_6295_; lean_object* v_fst_6298_; lean_object* v_snd_6299_; lean_object* v___x_6300_; uint8_t v___x_6301_; lean_object* v___y_6303_; lean_object* v_a_6304_; uint8_t v___y_6319_; double v___y_6350_; 
v_fst_6290_ = lean_ctor_get(v_resStartStop_6284_, 0);
lean_inc(v_fst_6290_);
v_snd_6291_ = lean_ctor_get(v_resStartStop_6284_, 1);
lean_inc(v_snd_6291_);
lean_dec_ref(v_resStartStop_6284_);
v_fst_6298_ = lean_ctor_get(v_snd_6291_, 0);
lean_inc(v_fst_6298_);
v_snd_6299_ = lean_ctor_get(v_snd_6291_, 1);
lean_inc(v_snd_6299_);
lean_dec(v_snd_6291_);
v___x_6300_ = l_Lean_trace_profiler;
v___x_6301_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_6280_, v___x_6300_);
if (v___x_6301_ == 0)
{
v___y_6319_ = v___x_6301_;
goto v___jp_6318_;
}
else
{
lean_object* v___x_6355_; uint8_t v___x_6356_; 
v___x_6355_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6356_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_6280_, v___x_6355_);
if (v___x_6356_ == 0)
{
lean_object* v___x_6357_; lean_object* v___x_6358_; double v___x_6359_; double v___x_6360_; double v___x_6361_; 
v___x_6357_ = l_Lean_trace_profiler_threshold;
v___x_6358_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_6280_, v___x_6357_);
v___x_6359_ = lean_float_of_nat(v___x_6358_);
v___x_6360_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2);
v___x_6361_ = lean_float_div(v___x_6359_, v___x_6360_);
v___y_6350_ = v___x_6361_;
goto v___jp_6349_;
}
else
{
lean_object* v___x_6362_; lean_object* v___x_6363_; double v___x_6364_; 
v___x_6362_ = l_Lean_trace_profiler_threshold;
v___x_6363_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_6280_, v___x_6362_);
v___x_6364_ = lean_float_of_nat(v___x_6363_);
v___y_6350_ = v___x_6364_;
goto v___jp_6349_;
}
}
v___jp_6292_:
{
lean_object* v___x_6296_; 
lean_inc(v___y_6293_);
v___x_6296_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(v_oldTraces_6282_, v_data_6295_, v___y_6293_, v___y_6294_, v___y_6285_, v___y_6286_, v___y_6287_, v___y_6288_);
if (lean_obj_tag(v___x_6296_) == 0)
{
lean_object* v___x_6297_; 
lean_dec_ref_known(v___x_6296_, 1);
v___x_6297_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_6290_);
return v___x_6297_;
}
else
{
lean_dec(v_fst_6290_);
return v___x_6296_;
}
}
v___jp_6302_:
{
uint8_t v_result_6305_; lean_object* v___x_6306_; lean_object* v___x_6307_; double v___x_6308_; lean_object* v_data_6309_; 
v_result_6305_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(v_fst_6290_);
v___x_6306_ = lean_box(v_result_6305_);
v___x_6307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6307_, 0, v___x_6306_);
v___x_6308_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_6279_);
lean_inc_ref(v___x_6307_);
lean_inc(v_cls_6277_);
v_data_6309_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6309_, 0, v_cls_6277_);
lean_ctor_set(v_data_6309_, 1, v___x_6307_);
lean_ctor_set(v_data_6309_, 2, v_tag_6279_);
lean_ctor_set_float(v_data_6309_, sizeof(void*)*3, v___x_6308_);
lean_ctor_set_float(v_data_6309_, sizeof(void*)*3 + 8, v___x_6308_);
lean_ctor_set_uint8(v_data_6309_, sizeof(void*)*3 + 16, v_collapsed_6278_);
if (v___x_6301_ == 0)
{
lean_dec_ref_known(v___x_6307_, 1);
lean_dec(v_snd_6299_);
lean_dec(v_fst_6298_);
lean_dec_ref(v_tag_6279_);
lean_dec(v_cls_6277_);
v___y_6293_ = v___y_6303_;
v___y_6294_ = v_a_6304_;
v_data_6295_ = v_data_6309_;
goto v___jp_6292_;
}
else
{
lean_object* v_data_6310_; double v___x_6311_; double v___x_6312_; 
lean_dec_ref_known(v_data_6309_, 3);
v_data_6310_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6310_, 0, v_cls_6277_);
lean_ctor_set(v_data_6310_, 1, v___x_6307_);
lean_ctor_set(v_data_6310_, 2, v_tag_6279_);
v___x_6311_ = lean_unbox_float(v_fst_6298_);
lean_dec(v_fst_6298_);
lean_ctor_set_float(v_data_6310_, sizeof(void*)*3, v___x_6311_);
v___x_6312_ = lean_unbox_float(v_snd_6299_);
lean_dec(v_snd_6299_);
lean_ctor_set_float(v_data_6310_, sizeof(void*)*3 + 8, v___x_6312_);
lean_ctor_set_uint8(v_data_6310_, sizeof(void*)*3 + 16, v_collapsed_6278_);
v___y_6293_ = v___y_6303_;
v___y_6294_ = v_a_6304_;
v_data_6295_ = v_data_6310_;
goto v___jp_6292_;
}
}
v___jp_6313_:
{
lean_object* v_ref_6314_; lean_object* v___x_6315_; 
v_ref_6314_ = lean_ctor_get(v___y_6287_, 5);
lean_inc(v___y_6288_);
lean_inc_ref(v___y_6287_);
lean_inc(v___y_6286_);
lean_inc_ref(v___y_6285_);
lean_inc(v_fst_6290_);
v___x_6315_ = lean_apply_6(v_msg_6283_, v_fst_6290_, v___y_6285_, v___y_6286_, v___y_6287_, v___y_6288_, lean_box(0));
if (lean_obj_tag(v___x_6315_) == 0)
{
lean_object* v_a_6316_; 
v_a_6316_ = lean_ctor_get(v___x_6315_, 0);
lean_inc(v_a_6316_);
lean_dec_ref_known(v___x_6315_, 1);
v___y_6303_ = v_ref_6314_;
v_a_6304_ = v_a_6316_;
goto v___jp_6302_;
}
else
{
lean_object* v___x_6317_; 
lean_dec_ref_known(v___x_6315_, 1);
v___x_6317_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
v___y_6303_ = v_ref_6314_;
v_a_6304_ = v___x_6317_;
goto v___jp_6302_;
}
}
v___jp_6318_:
{
if (v_clsEnabled_6281_ == 0)
{
if (v___y_6319_ == 0)
{
lean_object* v___x_6320_; lean_object* v_traceState_6321_; lean_object* v_env_6322_; lean_object* v_nextMacroScope_6323_; lean_object* v_ngen_6324_; lean_object* v_auxDeclNGen_6325_; lean_object* v_cache_6326_; lean_object* v_messages_6327_; lean_object* v_infoState_6328_; lean_object* v_snapshotTasks_6329_; lean_object* v___x_6331_; uint8_t v_isShared_6332_; uint8_t v_isSharedCheck_6348_; 
lean_dec(v_snd_6299_);
lean_dec(v_fst_6298_);
lean_dec_ref(v_msg_6283_);
lean_dec_ref(v_tag_6279_);
lean_dec(v_cls_6277_);
v___x_6320_ = lean_st_ref_take(v___y_6288_);
v_traceState_6321_ = lean_ctor_get(v___x_6320_, 4);
v_env_6322_ = lean_ctor_get(v___x_6320_, 0);
v_nextMacroScope_6323_ = lean_ctor_get(v___x_6320_, 1);
v_ngen_6324_ = lean_ctor_get(v___x_6320_, 2);
v_auxDeclNGen_6325_ = lean_ctor_get(v___x_6320_, 3);
v_cache_6326_ = lean_ctor_get(v___x_6320_, 5);
v_messages_6327_ = lean_ctor_get(v___x_6320_, 6);
v_infoState_6328_ = lean_ctor_get(v___x_6320_, 7);
v_snapshotTasks_6329_ = lean_ctor_get(v___x_6320_, 8);
v_isSharedCheck_6348_ = !lean_is_exclusive(v___x_6320_);
if (v_isSharedCheck_6348_ == 0)
{
v___x_6331_ = v___x_6320_;
v_isShared_6332_ = v_isSharedCheck_6348_;
goto v_resetjp_6330_;
}
else
{
lean_inc(v_snapshotTasks_6329_);
lean_inc(v_infoState_6328_);
lean_inc(v_messages_6327_);
lean_inc(v_cache_6326_);
lean_inc(v_traceState_6321_);
lean_inc(v_auxDeclNGen_6325_);
lean_inc(v_ngen_6324_);
lean_inc(v_nextMacroScope_6323_);
lean_inc(v_env_6322_);
lean_dec(v___x_6320_);
v___x_6331_ = lean_box(0);
v_isShared_6332_ = v_isSharedCheck_6348_;
goto v_resetjp_6330_;
}
v_resetjp_6330_:
{
uint64_t v_tid_6333_; lean_object* v_traces_6334_; lean_object* v___x_6336_; uint8_t v_isShared_6337_; uint8_t v_isSharedCheck_6347_; 
v_tid_6333_ = lean_ctor_get_uint64(v_traceState_6321_, sizeof(void*)*1);
v_traces_6334_ = lean_ctor_get(v_traceState_6321_, 0);
v_isSharedCheck_6347_ = !lean_is_exclusive(v_traceState_6321_);
if (v_isSharedCheck_6347_ == 0)
{
v___x_6336_ = v_traceState_6321_;
v_isShared_6337_ = v_isSharedCheck_6347_;
goto v_resetjp_6335_;
}
else
{
lean_inc(v_traces_6334_);
lean_dec(v_traceState_6321_);
v___x_6336_ = lean_box(0);
v_isShared_6337_ = v_isSharedCheck_6347_;
goto v_resetjp_6335_;
}
v_resetjp_6335_:
{
lean_object* v___x_6338_; lean_object* v___x_6340_; 
v___x_6338_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_6282_, v_traces_6334_);
lean_dec_ref(v_traces_6334_);
if (v_isShared_6337_ == 0)
{
lean_ctor_set(v___x_6336_, 0, v___x_6338_);
v___x_6340_ = v___x_6336_;
goto v_reusejp_6339_;
}
else
{
lean_object* v_reuseFailAlloc_6346_; 
v_reuseFailAlloc_6346_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6346_, 0, v___x_6338_);
lean_ctor_set_uint64(v_reuseFailAlloc_6346_, sizeof(void*)*1, v_tid_6333_);
v___x_6340_ = v_reuseFailAlloc_6346_;
goto v_reusejp_6339_;
}
v_reusejp_6339_:
{
lean_object* v___x_6342_; 
if (v_isShared_6332_ == 0)
{
lean_ctor_set(v___x_6331_, 4, v___x_6340_);
v___x_6342_ = v___x_6331_;
goto v_reusejp_6341_;
}
else
{
lean_object* v_reuseFailAlloc_6345_; 
v_reuseFailAlloc_6345_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6345_, 0, v_env_6322_);
lean_ctor_set(v_reuseFailAlloc_6345_, 1, v_nextMacroScope_6323_);
lean_ctor_set(v_reuseFailAlloc_6345_, 2, v_ngen_6324_);
lean_ctor_set(v_reuseFailAlloc_6345_, 3, v_auxDeclNGen_6325_);
lean_ctor_set(v_reuseFailAlloc_6345_, 4, v___x_6340_);
lean_ctor_set(v_reuseFailAlloc_6345_, 5, v_cache_6326_);
lean_ctor_set(v_reuseFailAlloc_6345_, 6, v_messages_6327_);
lean_ctor_set(v_reuseFailAlloc_6345_, 7, v_infoState_6328_);
lean_ctor_set(v_reuseFailAlloc_6345_, 8, v_snapshotTasks_6329_);
v___x_6342_ = v_reuseFailAlloc_6345_;
goto v_reusejp_6341_;
}
v_reusejp_6341_:
{
lean_object* v___x_6343_; lean_object* v___x_6344_; 
v___x_6343_ = lean_st_ref_set(v___y_6288_, v___x_6342_);
v___x_6344_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_6290_);
return v___x_6344_;
}
}
}
}
}
else
{
goto v___jp_6313_;
}
}
else
{
goto v___jp_6313_;
}
}
v___jp_6349_:
{
double v___x_6351_; double v___x_6352_; double v___x_6353_; uint8_t v___x_6354_; 
v___x_6351_ = lean_unbox_float(v_snd_6299_);
v___x_6352_ = lean_unbox_float(v_fst_6298_);
v___x_6353_ = lean_float_sub(v___x_6351_, v___x_6352_);
v___x_6354_ = lean_float_decLt(v___y_6350_, v___x_6353_);
v___y_6319_ = v___x_6354_;
goto v___jp_6318_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2___boxed(lean_object* v_cls_6365_, lean_object* v_collapsed_6366_, lean_object* v_tag_6367_, lean_object* v_opts_6368_, lean_object* v_clsEnabled_6369_, lean_object* v_oldTraces_6370_, lean_object* v_msg_6371_, lean_object* v_resStartStop_6372_, lean_object* v___y_6373_, lean_object* v___y_6374_, lean_object* v___y_6375_, lean_object* v___y_6376_, lean_object* v___y_6377_){
_start:
{
uint8_t v_collapsed_boxed_6378_; uint8_t v_clsEnabled_boxed_6379_; lean_object* v_res_6380_; 
v_collapsed_boxed_6378_ = lean_unbox(v_collapsed_6366_);
v_clsEnabled_boxed_6379_ = lean_unbox(v_clsEnabled_6369_);
v_res_6380_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(v_cls_6365_, v_collapsed_boxed_6378_, v_tag_6367_, v_opts_6368_, v_clsEnabled_boxed_6379_, v_oldTraces_6370_, v_msg_6371_, v_resStartStop_6372_, v___y_6373_, v___y_6374_, v___y_6375_, v___y_6376_);
lean_dec(v___y_6376_);
lean_dec_ref(v___y_6375_);
lean_dec(v___y_6374_);
lean_dec_ref(v___y_6373_);
lean_dec_ref(v_opts_6368_);
return v_res_6380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(lean_object* v_m_6382_, lean_object* v_a_6383_, lean_object* v_a_6384_, lean_object* v_a_6385_, lean_object* v_a_6386_){
_start:
{
lean_object* v_options_6388_; lean_object* v_inheritedTraceOptions_6389_; uint8_t v_hasTrace_6390_; lean_object* v_cls_6391_; 
v_options_6388_ = lean_ctor_get(v_a_6385_, 2);
v_inheritedTraceOptions_6389_ = lean_ctor_get(v_a_6385_, 13);
v_hasTrace_6390_ = lean_ctor_get_uint8(v_options_6388_, sizeof(void*)*1);
v_cls_6391_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
if (v_hasTrace_6390_ == 0)
{
lean_object* v___x_6392_; lean_object* v___x_6393_; lean_object* v___x_6394_; lean_object* v___x_6395_; lean_object* v___f_6396_; lean_object* v___x_6397_; 
v___x_6392_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6393_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6388_, v___x_6392_);
v___x_6394_ = lean_unsigned_to_nat(2u);
v___x_6395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6395_, 0, v___x_6393_);
lean_ctor_set(v___x_6395_, 1, v___x_6394_);
v___f_6396_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___boxed), 10, 3);
lean_closure_set(v___f_6396_, 0, v_m_6382_);
lean_closure_set(v___f_6396_, 1, v___x_6395_);
lean_closure_set(v___f_6396_, 2, v_cls_6391_);
v___x_6397_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6396_, v_a_6383_, v_a_6384_, v_a_6385_, v_a_6386_);
return v___x_6397_;
}
else
{
lean_object* v___f_6398_; lean_object* v___x_6399_; lean_object* v___x_6400_; uint8_t v___x_6401_; lean_object* v___y_6403_; lean_object* v___y_6404_; lean_object* v_a_6405_; lean_object* v___y_6418_; lean_object* v___y_6419_; lean_object* v_a_6420_; 
v___f_6398_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___closed__0));
v___x_6399_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_6400_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_6401_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6389_, v_options_6388_, v___x_6400_);
if (v___x_6401_ == 0)
{
lean_object* v___x_6482_; uint8_t v___x_6483_; 
v___x_6482_ = l_Lean_trace_profiler;
v___x_6483_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_6388_, v___x_6482_);
if (v___x_6483_ == 0)
{
lean_object* v___x_6484_; lean_object* v___x_6485_; lean_object* v___x_6486_; lean_object* v___x_6487_; lean_object* v___x_6488_; lean_object* v___f_6489_; lean_object* v___x_6490_; 
v___x_6484_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6485_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6388_, v___x_6484_);
v___x_6486_ = lean_unsigned_to_nat(2u);
v___x_6487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6487_, 0, v___x_6485_);
lean_ctor_set(v___x_6487_, 1, v___x_6486_);
v___x_6488_ = lean_box(v_hasTrace_6390_);
v___f_6489_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed), 11, 4);
lean_closure_set(v___f_6489_, 0, v_m_6382_);
lean_closure_set(v___f_6489_, 1, v___x_6487_);
lean_closure_set(v___f_6489_, 2, v___x_6488_);
lean_closure_set(v___f_6489_, 3, v_cls_6391_);
v___x_6490_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6489_, v_a_6383_, v_a_6384_, v_a_6385_, v_a_6386_);
return v___x_6490_;
}
else
{
goto v___jp_6429_;
}
}
else
{
goto v___jp_6429_;
}
v___jp_6402_:
{
lean_object* v___x_6406_; double v___x_6407_; double v___x_6408_; double v___x_6409_; double v___x_6410_; double v___x_6411_; lean_object* v___x_6412_; lean_object* v___x_6413_; lean_object* v___x_6414_; lean_object* v___x_6415_; lean_object* v___x_6416_; 
v___x_6406_ = lean_io_mono_nanos_now();
v___x_6407_ = lean_float_of_nat(v___y_6404_);
v___x_6408_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_6409_ = lean_float_div(v___x_6407_, v___x_6408_);
v___x_6410_ = lean_float_of_nat(v___x_6406_);
v___x_6411_ = lean_float_div(v___x_6410_, v___x_6408_);
v___x_6412_ = lean_box_float(v___x_6409_);
v___x_6413_ = lean_box_float(v___x_6411_);
v___x_6414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6414_, 0, v___x_6412_);
lean_ctor_set(v___x_6414_, 1, v___x_6413_);
v___x_6415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6415_, 0, v_a_6405_);
lean_ctor_set(v___x_6415_, 1, v___x_6414_);
v___x_6416_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(v_cls_6391_, v_hasTrace_6390_, v___x_6399_, v_options_6388_, v___x_6401_, v___y_6403_, v___f_6398_, v___x_6415_, v_a_6383_, v_a_6384_, v_a_6385_, v_a_6386_);
return v___x_6416_;
}
v___jp_6417_:
{
lean_object* v___x_6421_; double v___x_6422_; double v___x_6423_; lean_object* v___x_6424_; lean_object* v___x_6425_; lean_object* v___x_6426_; lean_object* v___x_6427_; lean_object* v___x_6428_; 
v___x_6421_ = lean_io_get_num_heartbeats();
v___x_6422_ = lean_float_of_nat(v___y_6419_);
v___x_6423_ = lean_float_of_nat(v___x_6421_);
v___x_6424_ = lean_box_float(v___x_6422_);
v___x_6425_ = lean_box_float(v___x_6423_);
v___x_6426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6426_, 0, v___x_6424_);
lean_ctor_set(v___x_6426_, 1, v___x_6425_);
v___x_6427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6427_, 0, v_a_6420_);
lean_ctor_set(v___x_6427_, 1, v___x_6426_);
v___x_6428_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(v_cls_6391_, v_hasTrace_6390_, v___x_6399_, v_options_6388_, v___x_6401_, v___y_6418_, v___f_6398_, v___x_6427_, v_a_6383_, v_a_6384_, v_a_6385_, v_a_6386_);
return v___x_6428_;
}
v___jp_6429_:
{
lean_object* v___x_6430_; lean_object* v_a_6431_; lean_object* v___x_6432_; uint8_t v___x_6433_; 
v___x_6430_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v_a_6386_);
v_a_6431_ = lean_ctor_get(v___x_6430_, 0);
lean_inc(v_a_6431_);
lean_dec_ref(v___x_6430_);
v___x_6432_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6433_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_6388_, v___x_6432_);
if (v___x_6433_ == 0)
{
lean_object* v___x_6434_; lean_object* v___x_6435_; lean_object* v___x_6436_; lean_object* v___x_6437_; lean_object* v___x_6438_; lean_object* v___x_6439_; lean_object* v___f_6440_; lean_object* v___x_6441_; 
v___x_6434_ = lean_io_mono_nanos_now();
v___x_6435_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6436_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6388_, v___x_6435_);
v___x_6437_ = lean_unsigned_to_nat(2u);
v___x_6438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6438_, 0, v___x_6436_);
lean_ctor_set(v___x_6438_, 1, v___x_6437_);
v___x_6439_ = lean_box(v_hasTrace_6390_);
v___f_6440_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed), 11, 4);
lean_closure_set(v___f_6440_, 0, v_m_6382_);
lean_closure_set(v___f_6440_, 1, v___x_6438_);
lean_closure_set(v___f_6440_, 2, v___x_6439_);
lean_closure_set(v___f_6440_, 3, v_cls_6391_);
v___x_6441_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6440_, v_a_6383_, v_a_6384_, v_a_6385_, v_a_6386_);
if (lean_obj_tag(v___x_6441_) == 0)
{
lean_object* v_a_6442_; lean_object* v___x_6444_; uint8_t v_isShared_6445_; uint8_t v_isSharedCheck_6449_; 
v_a_6442_ = lean_ctor_get(v___x_6441_, 0);
v_isSharedCheck_6449_ = !lean_is_exclusive(v___x_6441_);
if (v_isSharedCheck_6449_ == 0)
{
v___x_6444_ = v___x_6441_;
v_isShared_6445_ = v_isSharedCheck_6449_;
goto v_resetjp_6443_;
}
else
{
lean_inc(v_a_6442_);
lean_dec(v___x_6441_);
v___x_6444_ = lean_box(0);
v_isShared_6445_ = v_isSharedCheck_6449_;
goto v_resetjp_6443_;
}
v_resetjp_6443_:
{
lean_object* v___x_6447_; 
if (v_isShared_6445_ == 0)
{
lean_ctor_set_tag(v___x_6444_, 1);
v___x_6447_ = v___x_6444_;
goto v_reusejp_6446_;
}
else
{
lean_object* v_reuseFailAlloc_6448_; 
v_reuseFailAlloc_6448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6448_, 0, v_a_6442_);
v___x_6447_ = v_reuseFailAlloc_6448_;
goto v_reusejp_6446_;
}
v_reusejp_6446_:
{
v___y_6403_ = v_a_6431_;
v___y_6404_ = v___x_6434_;
v_a_6405_ = v___x_6447_;
goto v___jp_6402_;
}
}
}
else
{
lean_object* v_a_6450_; lean_object* v___x_6452_; uint8_t v_isShared_6453_; uint8_t v_isSharedCheck_6457_; 
v_a_6450_ = lean_ctor_get(v___x_6441_, 0);
v_isSharedCheck_6457_ = !lean_is_exclusive(v___x_6441_);
if (v_isSharedCheck_6457_ == 0)
{
v___x_6452_ = v___x_6441_;
v_isShared_6453_ = v_isSharedCheck_6457_;
goto v_resetjp_6451_;
}
else
{
lean_inc(v_a_6450_);
lean_dec(v___x_6441_);
v___x_6452_ = lean_box(0);
v_isShared_6453_ = v_isSharedCheck_6457_;
goto v_resetjp_6451_;
}
v_resetjp_6451_:
{
lean_object* v___x_6455_; 
if (v_isShared_6453_ == 0)
{
lean_ctor_set_tag(v___x_6452_, 0);
v___x_6455_ = v___x_6452_;
goto v_reusejp_6454_;
}
else
{
lean_object* v_reuseFailAlloc_6456_; 
v_reuseFailAlloc_6456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6456_, 0, v_a_6450_);
v___x_6455_ = v_reuseFailAlloc_6456_;
goto v_reusejp_6454_;
}
v_reusejp_6454_:
{
v___y_6403_ = v_a_6431_;
v___y_6404_ = v___x_6434_;
v_a_6405_ = v___x_6455_;
goto v___jp_6402_;
}
}
}
}
else
{
lean_object* v___x_6458_; lean_object* v___x_6459_; lean_object* v___x_6460_; lean_object* v___x_6461_; lean_object* v___x_6462_; lean_object* v___x_6463_; lean_object* v___f_6464_; lean_object* v___x_6465_; 
v___x_6458_ = lean_io_get_num_heartbeats();
v___x_6459_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6460_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6388_, v___x_6459_);
v___x_6461_ = lean_unsigned_to_nat(2u);
v___x_6462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6462_, 0, v___x_6460_);
lean_ctor_set(v___x_6462_, 1, v___x_6461_);
v___x_6463_ = lean_box(v___x_6433_);
v___f_6464_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6___boxed), 11, 4);
lean_closure_set(v___f_6464_, 0, v_m_6382_);
lean_closure_set(v___f_6464_, 1, v___x_6462_);
lean_closure_set(v___f_6464_, 2, v___x_6463_);
lean_closure_set(v___f_6464_, 3, v_cls_6391_);
v___x_6465_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6464_, v_a_6383_, v_a_6384_, v_a_6385_, v_a_6386_);
if (lean_obj_tag(v___x_6465_) == 0)
{
lean_object* v_a_6466_; lean_object* v___x_6468_; uint8_t v_isShared_6469_; uint8_t v_isSharedCheck_6473_; 
v_a_6466_ = lean_ctor_get(v___x_6465_, 0);
v_isSharedCheck_6473_ = !lean_is_exclusive(v___x_6465_);
if (v_isSharedCheck_6473_ == 0)
{
v___x_6468_ = v___x_6465_;
v_isShared_6469_ = v_isSharedCheck_6473_;
goto v_resetjp_6467_;
}
else
{
lean_inc(v_a_6466_);
lean_dec(v___x_6465_);
v___x_6468_ = lean_box(0);
v_isShared_6469_ = v_isSharedCheck_6473_;
goto v_resetjp_6467_;
}
v_resetjp_6467_:
{
lean_object* v___x_6471_; 
if (v_isShared_6469_ == 0)
{
lean_ctor_set_tag(v___x_6468_, 1);
v___x_6471_ = v___x_6468_;
goto v_reusejp_6470_;
}
else
{
lean_object* v_reuseFailAlloc_6472_; 
v_reuseFailAlloc_6472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6472_, 0, v_a_6466_);
v___x_6471_ = v_reuseFailAlloc_6472_;
goto v_reusejp_6470_;
}
v_reusejp_6470_:
{
v___y_6418_ = v_a_6431_;
v___y_6419_ = v___x_6458_;
v_a_6420_ = v___x_6471_;
goto v___jp_6417_;
}
}
}
else
{
lean_object* v_a_6474_; lean_object* v___x_6476_; uint8_t v_isShared_6477_; uint8_t v_isSharedCheck_6481_; 
v_a_6474_ = lean_ctor_get(v___x_6465_, 0);
v_isSharedCheck_6481_ = !lean_is_exclusive(v___x_6465_);
if (v_isSharedCheck_6481_ == 0)
{
v___x_6476_ = v___x_6465_;
v_isShared_6477_ = v_isSharedCheck_6481_;
goto v_resetjp_6475_;
}
else
{
lean_inc(v_a_6474_);
lean_dec(v___x_6465_);
v___x_6476_ = lean_box(0);
v_isShared_6477_ = v_isSharedCheck_6481_;
goto v_resetjp_6475_;
}
v_resetjp_6475_:
{
lean_object* v___x_6479_; 
if (v_isShared_6477_ == 0)
{
lean_ctor_set_tag(v___x_6476_, 0);
v___x_6479_ = v___x_6476_;
goto v_reusejp_6478_;
}
else
{
lean_object* v_reuseFailAlloc_6480_; 
v_reuseFailAlloc_6480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6480_, 0, v_a_6474_);
v___x_6479_ = v_reuseFailAlloc_6480_;
goto v_reusejp_6478_;
}
v_reusejp_6478_:
{
v___y_6418_ = v_a_6431_;
v___y_6419_ = v___x_6458_;
v_a_6420_ = v___x_6479_;
goto v___jp_6417_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___boxed(lean_object* v_m_6491_, lean_object* v_a_6492_, lean_object* v_a_6493_, lean_object* v_a_6494_, lean_object* v_a_6495_, lean_object* v_a_6496_){
_start:
{
lean_object* v_res_6497_; 
v_res_6497_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(v_m_6491_, v_a_6492_, v_a_6493_, v_a_6494_, v_a_6495_);
lean_dec(v_a_6495_);
lean_dec_ref(v_a_6494_);
lean_dec(v_a_6493_);
lean_dec_ref(v_a_6492_);
return v_res_6497_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0(lean_object* v_00_u03b1_6498_, lean_object* v_msg_6499_, lean_object* v___y_6500_, lean_object* v___y_6501_, lean_object* v___y_6502_, lean_object* v___y_6503_, lean_object* v___y_6504_, lean_object* v___y_6505_){
_start:
{
lean_object* v___x_6507_; 
v___x_6507_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v_msg_6499_, v___y_6502_, v___y_6503_, v___y_6504_, v___y_6505_);
return v___x_6507_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___boxed(lean_object* v_00_u03b1_6508_, lean_object* v_msg_6509_, lean_object* v___y_6510_, lean_object* v___y_6511_, lean_object* v___y_6512_, lean_object* v___y_6513_, lean_object* v___y_6514_, lean_object* v___y_6515_, lean_object* v___y_6516_){
_start:
{
lean_object* v_res_6517_; 
v_res_6517_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0(v_00_u03b1_6508_, v_msg_6509_, v___y_6510_, v___y_6511_, v___y_6512_, v___y_6513_, v___y_6514_, v___y_6515_);
lean_dec(v___y_6515_);
lean_dec_ref(v___y_6514_);
lean_dec(v___y_6513_);
lean_dec_ref(v___y_6512_);
lean_dec(v___y_6511_);
lean_dec_ref(v___y_6510_);
return v_res_6517_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1(lean_object* v_cls_6518_, lean_object* v_msg_6519_, lean_object* v___y_6520_, lean_object* v___y_6521_, lean_object* v___y_6522_, lean_object* v___y_6523_, lean_object* v___y_6524_, lean_object* v___y_6525_){
_start:
{
lean_object* v___x_6527_; 
v___x_6527_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_6518_, v_msg_6519_, v___y_6522_, v___y_6523_, v___y_6524_, v___y_6525_);
return v___x_6527_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___boxed(lean_object* v_cls_6528_, lean_object* v_msg_6529_, lean_object* v___y_6530_, lean_object* v___y_6531_, lean_object* v___y_6532_, lean_object* v___y_6533_, lean_object* v___y_6534_, lean_object* v___y_6535_, lean_object* v___y_6536_){
_start:
{
lean_object* v_res_6537_; 
v_res_6537_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1(v_cls_6528_, v_msg_6529_, v___y_6530_, v___y_6531_, v___y_6532_, v___y_6533_, v___y_6534_, v___y_6535_);
lean_dec(v___y_6535_);
lean_dec_ref(v___y_6534_);
lean_dec(v___y_6533_);
lean_dec_ref(v___y_6532_);
lean_dec(v___y_6531_);
lean_dec_ref(v___y_6530_);
return v_res_6537_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_Opaque(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_ControlFlow(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_String(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_Util(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Assert(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Cbv_Main(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_Opaque(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_ControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Assert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_1624789814____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Tactic_Cbv_cbv_warning = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_cbv_warning);
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_Main_2158550632____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Tactic_Cbv_cbv_maxSteps = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_cbv_maxSteps);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Cbv_Main(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv_Opaque(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv_ControlFlow(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_String(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv_Util(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Replace(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Cbv_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_Opaque(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_ControlFlow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_BuiltinCbvSimprocs_String(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_TheoremsLookup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cbv_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Cbv_Main(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Cbv_Main(builtin);
}
#ifdef __cplusplus
}
#endif

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
v___y_1088_ = v___y_1108_;
v___y_1089_ = v_a_1109_;
v___y_1090_ = v_contextDependent_1110_;
goto v___jp_1087_;
}
else
{
uint8_t v_contextDependent_1111_; 
v_contextDependent_1111_ = lean_ctor_get_uint8(v_a_1109_, sizeof(void*)*2 + 1);
v___y_1088_ = v___y_1108_;
v___y_1089_ = v_a_1109_;
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
lean_dec_ref(v___y_1088_);
v___x_1091_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1089_);
v___x_1092_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1092_, 0, v___x_1091_);
return v___x_1092_;
}
else
{
lean_dec_ref(v___y_1089_);
return v___y_1088_;
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
lean_object* v_inheritedTraceOptions_2542_; lean_object* v___f_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; uint8_t v___x_2547_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v_a_2551_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v_a_2566_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v_a_2571_; lean_object* v___y_2574_; uint8_t v___y_2575_; uint8_t v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v_a_2579_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2584_; uint8_t v___y_2588_; uint8_t v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v_a_2593_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v_a_2598_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v_a_2610_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v_a_2615_; lean_object* v___y_2618_; uint8_t v___y_2619_; lean_object* v___y_2620_; uint8_t v___y_2621_; lean_object* v___y_2622_; lean_object* v_a_2623_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2632_; lean_object* v___y_2633_; uint8_t v___y_2634_; lean_object* v___y_2635_; lean_object* v_a_2636_; 
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
v___x_2553_ = lean_float_of_nat(v___y_2550_);
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
v___x_2562_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4(v___x_2544_, v_hasTrace_2539_, v___x_2545_, v_options_2538_, v___x_2547_, v___y_2549_, v___f_2543_, v___x_2561_, v_a_2270_, v_a_2271_, v_a_2272_, v_a_2273_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_);
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
lean_ctor_set(v___x_2580_, 1, v___y_2574_);
lean_ctor_set_uint8(v___x_2580_, sizeof(void*)*2, v___y_2576_);
lean_ctor_set_uint8(v___x_2580_, sizeof(void*)*2 + 1, v___y_2575_);
v___y_2569_ = v___y_2577_;
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
lean_ctor_set_uint8(v___x_2594_, sizeof(void*)*2 + 1, v___y_2588_);
v___y_2569_ = v___y_2590_;
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
lean_ctor_set(v___x_2624_, 1, v___y_2622_);
lean_ctor_set_uint8(v___x_2624_, sizeof(void*)*2, v___y_2621_);
lean_ctor_set_uint8(v___x_2624_, sizeof(void*)*2 + 1, v___y_2619_);
v___y_2613_ = v___y_2618_;
v___y_2614_ = v___y_2620_;
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
lean_ctor_set(v___x_2638_, 1, v___y_2635_);
lean_ctor_set_uint8(v___x_2638_, sizeof(void*)*2, v___y_2634_);
lean_ctor_set_uint8(v___x_2638_, sizeof(void*)*2 + 1, v___x_2637_);
v___y_2613_ = v___y_2632_;
v___y_2614_ = v___y_2633_;
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
v___y_2569_ = v_a_2641_;
v___y_2570_ = v___x_2644_;
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
v___y_2564_ = v_a_2641_;
v___y_2565_ = v___x_2644_;
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
v___y_2564_ = v_a_2641_;
v___y_2565_ = v___x_2644_;
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
v___y_2569_ = v_a_2641_;
v___y_2570_ = v___x_2644_;
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
v___y_2564_ = v_a_2641_;
v___y_2565_ = v___x_2644_;
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
v___y_2569_ = v_a_2641_;
v___y_2570_ = v___x_2644_;
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
v___y_2574_ = v_a_2699_;
v___y_2575_ = v___x_2643_;
v___y_2576_ = v_contextDependent_2671_;
v___y_2577_ = v_a_2641_;
v___y_2578_ = v___x_2644_;
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
v___y_2564_ = v_a_2641_;
v___y_2565_ = v___x_2644_;
v_a_2566_ = v_a_2703_;
goto v___jp_2563_;
}
}
else
{
lean_dec_ref(v_e_x27_2669_);
v___y_2574_ = v_a_2699_;
v___y_2575_ = v___x_2643_;
v___y_2576_ = v_contextDependent_2671_;
v___y_2577_ = v_a_2641_;
v___y_2578_ = v___x_2644_;
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
v___y_2564_ = v_a_2641_;
v___y_2565_ = v___x_2644_;
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
v___y_2564_ = v_a_2641_;
v___y_2565_ = v___x_2644_;
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
v___y_2564_ = v_a_2641_;
v___y_2565_ = v___x_2644_;
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
v___y_2569_ = v_a_2641_;
v___y_2570_ = v___x_2644_;
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
v___y_2564_ = v_a_2641_;
v___y_2565_ = v___x_2644_;
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
v___y_2564_ = v_a_2641_;
v___y_2565_ = v___x_2644_;
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
v___y_2564_ = v_a_2641_;
v___y_2565_ = v___x_2644_;
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
v___y_2588_ = v___x_2643_;
v___y_2589_ = v_contextDependent_2671_;
v___y_2590_ = v_a_2641_;
v___y_2591_ = v___x_2729_;
v___y_2592_ = v___x_2644_;
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
v___y_2564_ = v_a_2641_;
v___y_2565_ = v___x_2644_;
v_a_2566_ = v_a_2733_;
goto v___jp_2563_;
}
}
else
{
lean_dec_ref(v_e_x27_2669_);
v___y_2588_ = v___x_2643_;
v___y_2589_ = v_contextDependent_2671_;
v___y_2590_ = v_a_2641_;
v___y_2591_ = v___x_2729_;
v___y_2592_ = v___x_2644_;
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
v___y_2564_ = v_a_2641_;
v___y_2565_ = v___x_2644_;
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
v___y_2564_ = v_a_2641_;
v___y_2565_ = v___x_2644_;
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
v___y_2582_ = v_a_2641_;
v___y_2583_ = v___x_2644_;
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
v___y_2564_ = v_a_2641_;
v___y_2565_ = v___x_2644_;
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
v___y_2564_ = v_a_2641_;
v___y_2565_ = v___x_2644_;
v_a_2566_ = v_a_2739_;
goto v___jp_2563_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2269_, 3);
v___y_2582_ = v_a_2641_;
v___y_2583_ = v___x_2644_;
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
v___y_2619_ = v___x_2782_;
v___y_2620_ = v_a_2641_;
v___y_2621_ = v_contextDependent_2769_;
v___y_2622_ = v_a_2797_;
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
v___y_2619_ = v___x_2782_;
v___y_2620_ = v_a_2641_;
v___y_2621_ = v_contextDependent_2769_;
v___y_2622_ = v_a_2797_;
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
v___y_2633_ = v_a_2641_;
v___y_2634_ = v_contextDependent_2769_;
v___y_2635_ = v___x_2827_;
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
v___y_2633_ = v_a_2641_;
v___y_2634_ = v_contextDependent_2769_;
v___y_2635_ = v___x_2827_;
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
v___y_2282_ = v_contextDependent_2369_;
v___y_2283_ = v___x_2382_;
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
v___y_2282_ = v_contextDependent_2369_;
v___y_2283_ = v___x_2382_;
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
lean_ctor_set_uint8(v___x_2285_, sizeof(void*)*2, v___y_2282_);
lean_ctor_set_uint8(v___x_2285_, sizeof(void*)*2 + 1, v___y_2283_);
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
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3342_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3213_ = v___x_3210_;
v_isShared_3214_ = v_isSharedCheck_3342_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3210_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3342_;
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
lean_del_object(v___x_3213_);
lean_inc_ref(v_e_3197_);
v___x_3220_ = l_Lean_Meta_Sym_inferType___redArg(v_e_3197_, v_a_3202_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v_a_3221_; lean_object* v___x_3222_; 
v_a_3221_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3221_);
lean_dec_ref_known(v___x_3220_, 1);
v___x_3222_ = l_Lean_Meta_whnfD(v_a_3221_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_object* v_a_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3325_; 
v_a_3223_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3225_ = v___x_3222_;
v_isShared_3226_ = v_isSharedCheck_3325_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_a_3223_);
lean_dec(v___x_3222_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3325_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
if (lean_obj_tag(v_a_3223_) == 7)
{
lean_object* v___x_3227_; lean_object* v___x_3229_; 
lean_dec_ref_known(v_a_3223_, 3);
lean_dec(v_a_3211_);
lean_dec_ref_known(v_e_3197_, 2);
v___x_3227_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
if (v_isShared_3226_ == 0)
{
lean_ctor_set(v___x_3225_, 0, v___x_3227_);
v___x_3229_ = v___x_3225_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3227_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
else
{
uint8_t v___x_3231_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; uint8_t v___y_3258_; uint8_t v___x_3320_; 
lean_dec(v_a_3223_);
v___x_3231_ = 0;
v___x_3320_ = l_Lean_ConstantInfo_hasValue(v_a_3211_, v___x_3231_);
if (v___x_3320_ == 0)
{
v___y_3258_ = v___x_3320_;
goto v___jp_3257_;
}
else
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; uint8_t v___x_3324_; 
v___x_3321_ = l_Lean_ConstantInfo_levelParams(v_a_3211_);
v___x_3322_ = l_List_lengthTR___redArg(v___x_3321_);
lean_dec(v___x_3321_);
v___x_3323_ = l_List_lengthTR___redArg(v_us_3209_);
v___x_3324_ = lean_nat_dec_eq(v___x_3322_, v___x_3323_);
lean_dec(v___x_3323_);
lean_dec(v___x_3322_);
v___y_3258_ = v___x_3324_;
goto v___jp_3257_;
}
v___jp_3232_:
{
lean_object* v___x_3239_; 
lean_inc_ref(v___y_3233_);
v___x_3239_ = l_Lean_Meta_Sym_mkEqRefl___redArg(v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3248_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3242_ = v___x_3239_;
v_isShared_3243_ = v_isSharedCheck_3248_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_a_3240_);
lean_dec(v___x_3239_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3248_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
lean_object* v___x_3244_; lean_object* v___x_3246_; 
v___x_3244_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3244_, 0, v___y_3233_);
lean_ctor_set(v___x_3244_, 1, v_a_3240_);
lean_ctor_set_uint8(v___x_3244_, sizeof(void*)*2, v___x_3231_);
lean_ctor_set_uint8(v___x_3244_, sizeof(void*)*2 + 1, v___x_3231_);
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 0, v___x_3244_);
v___x_3246_ = v___x_3242_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3244_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
}
else
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3256_; 
lean_dec_ref(v___y_3233_);
v_a_3249_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3251_ = v___x_3239_;
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___x_3239_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3254_; 
if (v_isShared_3252_ == 0)
{
v___x_3254_ = v___x_3251_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
v___jp_3257_:
{
if (v___y_3258_ == 0)
{
lean_object* v___x_3259_; lean_object* v___x_3261_; 
lean_dec(v_a_3211_);
lean_dec_ref_known(v_e_3197_, 2);
v___x_3259_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
if (v_isShared_3226_ == 0)
{
lean_ctor_set(v___x_3225_, 0, v___x_3259_);
v___x_3261_ = v___x_3225_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v___x_3259_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
else
{
lean_object* v___x_3263_; 
lean_del_object(v___x_3225_);
lean_inc(v_us_3209_);
v___x_3263_ = l_Lean_Core_instantiateValueLevelParams(v_a_3211_, v_us_3209_, v___x_3231_, v_a_3205_, v_a_3206_);
lean_dec(v_a_3211_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_object* v_a_3264_; lean_object* v___x_3265_; 
v_a_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc(v_a_3264_);
lean_dec_ref_known(v___x_3263_, 1);
v___x_3265_ = l_Lean_Meta_Sym_unfoldReducible(v_a_3264_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; lean_object* v___x_3267_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_a_3266_);
lean_dec_ref_known(v___x_3265_, 1);
v___x_3267_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_3266_, v_a_3202_);
if (lean_obj_tag(v___x_3267_) == 0)
{
lean_object* v_options_3268_; uint8_t v_hasTrace_3269_; 
v_options_3268_ = lean_ctor_get(v_a_3205_, 2);
v_hasTrace_3269_ = lean_ctor_get_uint8(v_options_3268_, sizeof(void*)*1);
if (v_hasTrace_3269_ == 0)
{
lean_object* v_a_3270_; 
lean_dec_ref_known(v_e_3197_, 2);
v_a_3270_ = lean_ctor_get(v___x_3267_, 0);
lean_inc(v_a_3270_);
lean_dec_ref_known(v___x_3267_, 1);
v___y_3233_ = v_a_3270_;
v___y_3234_ = v_a_3202_;
v___y_3235_ = v_a_3203_;
v___y_3236_ = v_a_3204_;
v___y_3237_ = v_a_3205_;
v___y_3238_ = v_a_3206_;
goto v___jp_3232_;
}
else
{
lean_object* v_a_3271_; lean_object* v_inheritedTraceOptions_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; uint8_t v___x_3275_; 
v_a_3271_ = lean_ctor_get(v___x_3267_, 0);
lean_inc(v_a_3271_);
lean_dec_ref_known(v___x_3267_, 1);
v_inheritedTraceOptions_3272_ = lean_ctor_get(v_a_3205_, 13);
v___x_3273_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1));
v___x_3274_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2);
v___x_3275_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3272_, v_options_3268_, v___x_3274_);
if (v___x_3275_ == 0)
{
lean_dec_ref_known(v_e_3197_, 2);
v___y_3233_ = v_a_3271_;
v___y_3234_ = v_a_3202_;
v___y_3235_ = v_a_3203_;
v___y_3236_ = v_a_3204_;
v___y_3237_ = v_a_3205_;
v___y_3238_ = v_a_3206_;
goto v___jp_3232_;
}
else
{
lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; 
v___x_3276_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1);
lean_inc(v_declName_3208_);
v___x_3277_ = l_Lean_MessageData_ofName(v_declName_3208_);
v___x_3278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3276_);
lean_ctor_set(v___x_3278_, 1, v___x_3277_);
v___x_3279_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8);
v___x_3280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3278_);
lean_ctor_set(v___x_3280_, 1, v___x_3279_);
v___x_3281_ = l_Lean_indentExpr(v_e_3197_);
v___x_3282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3280_);
lean_ctor_set(v___x_3282_, 1, v___x_3281_);
v___x_3283_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_3284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3282_);
lean_ctor_set(v___x_3284_, 1, v___x_3283_);
lean_inc(v_a_3271_);
v___x_3285_ = l_Lean_indentExpr(v_a_3271_);
v___x_3286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3284_);
lean_ctor_set(v___x_3286_, 1, v___x_3285_);
v___x_3287_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_3273_, v___x_3286_, v_a_3203_, v_a_3204_, v_a_3205_, v_a_3206_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_dec_ref_known(v___x_3287_, 1);
v___y_3233_ = v_a_3271_;
v___y_3234_ = v_a_3202_;
v___y_3235_ = v_a_3203_;
v___y_3236_ = v_a_3204_;
v___y_3237_ = v_a_3205_;
v___y_3238_ = v_a_3206_;
goto v___jp_3232_;
}
else
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
lean_dec(v_a_3271_);
v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v___x_3287_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3287_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
}
}
}
}
}
}
else
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3303_; 
lean_dec_ref_known(v_e_3197_, 2);
v_a_3296_ = lean_ctor_get(v___x_3267_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3267_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3298_ = v___x_3267_;
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3267_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3301_; 
if (v_isShared_3299_ == 0)
{
v___x_3301_ = v___x_3298_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3296_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
}
else
{
lean_object* v_a_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3311_; 
lean_dec_ref_known(v_e_3197_, 2);
v_a_3304_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3311_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3306_ = v___x_3265_;
v_isShared_3307_ = v_isSharedCheck_3311_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_a_3304_);
lean_dec(v___x_3265_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3311_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v___x_3309_; 
if (v_isShared_3307_ == 0)
{
v___x_3309_ = v___x_3306_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_a_3304_);
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
else
{
lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3319_; 
lean_dec_ref_known(v_e_3197_, 2);
v_a_3312_ = lean_ctor_get(v___x_3263_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3314_ = v___x_3263_;
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3263_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3317_; 
if (v_isShared_3315_ == 0)
{
v___x_3317_ = v___x_3314_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_a_3312_);
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
else
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3333_; 
lean_dec(v_a_3211_);
lean_dec_ref_known(v_e_3197_, 2);
v_a_3326_ = lean_ctor_get(v___x_3222_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3328_ = v___x_3222_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3222_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3331_; 
if (v_isShared_3329_ == 0)
{
v___x_3331_ = v___x_3328_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3326_);
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
else
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3341_; 
lean_dec(v_a_3211_);
lean_dec_ref_known(v_e_3197_, 2);
v_a_3334_ = lean_ctor_get(v___x_3220_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3336_ = v___x_3220_;
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3220_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3339_; 
if (v_isShared_3337_ == 0)
{
v___x_3339_ = v___x_3336_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_a_3334_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
}
}
else
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3350_; 
lean_dec_ref_known(v_e_3197_, 2);
v_a_3343_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3345_ = v___x_3210_;
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3210_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3348_; 
if (v_isShared_3346_ == 0)
{
v___x_3348_ = v___x_3345_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3343_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
else
{
lean_object* v___x_3351_; lean_object* v___x_3352_; 
lean_dec_ref(v_e_3197_);
v___x_3351_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_3352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3351_);
return v___x_3352_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___boxed(lean_object* v_e_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(v_e_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_);
lean_dec(v_a_3362_);
lean_dec_ref(v_a_3361_);
lean_dec(v_a_3360_);
lean_dec_ref(v_a_3359_);
lean_dec(v_a_3358_);
lean_dec_ref(v_a_3357_);
lean_dec(v_a_3356_);
lean_dec_ref(v_a_3355_);
lean_dec(v_a_3354_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(lean_object* v_x_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v___x_3377_; 
lean_inc_ref(v___y_3366_);
v___x_3377_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_a_3378_);
if (lean_obj_tag(v_a_3378_) == 0)
{
uint8_t v_done_3379_; 
v_done_3379_ = lean_ctor_get_uint8(v_a_3378_, 0);
if (v_done_3379_ == 0)
{
uint8_t v_contextDependent_3380_; lean_object* v___x_3381_; 
lean_dec_ref_known(v___x_3377_, 1);
v_contextDependent_3380_ = lean_ctor_get_uint8(v_a_3378_, 1);
lean_dec_ref_known(v_a_3378_, 0);
v___x_3381_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; uint8_t v___y_3384_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3382_);
if (v_contextDependent_3380_ == 0)
{
lean_dec(v_a_3382_);
return v___x_3381_;
}
else
{
if (lean_obj_tag(v_a_3382_) == 0)
{
uint8_t v_contextDependent_3394_; 
v_contextDependent_3394_ = lean_ctor_get_uint8(v_a_3382_, 1);
v___y_3384_ = v_contextDependent_3394_;
goto v___jp_3383_;
}
else
{
uint8_t v___x_3395_; 
v___x_3395_ = 0;
v___y_3384_ = v___x_3395_;
goto v___jp_3383_;
}
}
v___jp_3383_:
{
if (v___y_3384_ == 0)
{
lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3392_; 
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3392_ == 0)
{
lean_object* v_unused_3393_; 
v_unused_3393_ = lean_ctor_get(v___x_3381_, 0);
lean_dec(v_unused_3393_);
v___x_3386_ = v___x_3381_;
v_isShared_3387_ = v_isSharedCheck_3392_;
goto v_resetjp_3385_;
}
else
{
lean_dec(v___x_3381_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3392_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3388_; lean_object* v___x_3390_; 
v___x_3388_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3382_);
if (v_isShared_3387_ == 0)
{
lean_ctor_set(v___x_3386_, 0, v___x_3388_);
v___x_3390_ = v___x_3386_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3388_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
else
{
lean_dec(v_a_3382_);
return v___x_3381_;
}
}
}
else
{
return v___x_3381_;
}
}
else
{
lean_dec_ref_known(v_a_3378_, 0);
lean_dec_ref(v___y_3366_);
return v___x_3377_;
}
}
else
{
lean_dec_ref_known(v_a_3378_, 2);
lean_dec_ref(v___y_3366_);
return v___x_3377_;
}
}
else
{
lean_dec_ref(v___y_3366_);
return v___x_3377_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0___boxed(lean_object* v_x_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v_x_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___y_3398_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(lean_object* v_e_3412_, lean_object* v_a_3413_, lean_object* v_a_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_){
_start:
{
switch(lean_obj_tag(v_e_3412_))
{
case 9:
{
lean_object* v___x_3426_; 
v___x_3426_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(v_e_3412_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_);
return v___x_3426_;
}
case 11:
{
lean_object* v___x_3427_; 
v___x_3427_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(v_e_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_);
return v___x_3427_;
}
case 4:
{
lean_object* v___x_3428_; 
lean_inc_ref(v_e_3412_);
v___x_3428_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleOpaqueConst(v_e_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_a_3429_; lean_object* v___x_3430_; 
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_a_3429_);
v___x_3430_ = lean_box(0);
if (lean_obj_tag(v_a_3429_) == 0)
{
uint8_t v_done_3431_; 
v_done_3431_ = lean_ctor_get_uint8(v_a_3429_, 0);
if (v_done_3431_ == 0)
{
uint8_t v_contextDependent_3432_; lean_object* v___x_3433_; 
lean_dec_ref_known(v___x_3428_, 1);
v_contextDependent_3432_ = lean_ctor_get_uint8(v_a_3429_, 1);
lean_dec_ref_known(v_a_3429_, 0);
v___x_3433_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v___x_3430_, v_e_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v_a_3434_; uint8_t v___y_3436_; 
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_a_3434_);
if (v_contextDependent_3432_ == 0)
{
lean_dec(v_a_3434_);
return v___x_3433_;
}
else
{
if (lean_obj_tag(v_a_3434_) == 0)
{
uint8_t v_contextDependent_3446_; 
v_contextDependent_3446_ = lean_ctor_get_uint8(v_a_3434_, 1);
v___y_3436_ = v_contextDependent_3446_;
goto v___jp_3435_;
}
else
{
uint8_t v_contextDependent_3447_; 
v_contextDependent_3447_ = lean_ctor_get_uint8(v_a_3434_, sizeof(void*)*2 + 1);
v___y_3436_ = v_contextDependent_3447_;
goto v___jp_3435_;
}
}
v___jp_3435_:
{
if (v___y_3436_ == 0)
{
lean_object* v___x_3438_; uint8_t v_isShared_3439_; uint8_t v_isSharedCheck_3444_; 
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3444_ == 0)
{
lean_object* v_unused_3445_; 
v_unused_3445_ = lean_ctor_get(v___x_3433_, 0);
lean_dec(v_unused_3445_);
v___x_3438_ = v___x_3433_;
v_isShared_3439_ = v_isSharedCheck_3444_;
goto v_resetjp_3437_;
}
else
{
lean_dec(v___x_3433_);
v___x_3438_ = lean_box(0);
v_isShared_3439_ = v_isSharedCheck_3444_;
goto v_resetjp_3437_;
}
v_resetjp_3437_:
{
lean_object* v___x_3440_; lean_object* v___x_3442_; 
v___x_3440_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3434_);
if (v_isShared_3439_ == 0)
{
lean_ctor_set(v___x_3438_, 0, v___x_3440_);
v___x_3442_ = v___x_3438_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3440_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
else
{
lean_dec(v_a_3434_);
return v___x_3433_;
}
}
}
else
{
return v___x_3433_;
}
}
else
{
lean_dec_ref_known(v_a_3429_, 0);
lean_dec_ref_known(v_e_3412_, 2);
return v___x_3428_;
}
}
else
{
uint8_t v_done_3448_; 
v_done_3448_ = lean_ctor_get_uint8(v_a_3429_, sizeof(void*)*2);
if (v_done_3448_ == 0)
{
lean_object* v_e_x27_3449_; lean_object* v_proof_3450_; uint8_t v_contextDependent_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3501_; 
lean_dec_ref_known(v___x_3428_, 1);
v_e_x27_3449_ = lean_ctor_get(v_a_3429_, 0);
v_proof_3450_ = lean_ctor_get(v_a_3429_, 1);
v_contextDependent_3451_ = lean_ctor_get_uint8(v_a_3429_, sizeof(void*)*2 + 1);
v_isSharedCheck_3501_ = !lean_is_exclusive(v_a_3429_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3453_ = v_a_3429_;
v_isShared_3454_ = v_isSharedCheck_3501_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_proof_3450_);
lean_inc(v_e_x27_3449_);
lean_dec(v_a_3429_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3501_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3455_; 
lean_inc_ref(v_e_x27_3449_);
v___x_3455_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v___x_3430_, v_e_x27_3449_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3500_; 
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3458_ = v___x_3455_;
v_isShared_3459_ = v_isSharedCheck_3500_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3455_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3500_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
if (lean_obj_tag(v_a_3456_) == 0)
{
uint8_t v_done_3460_; uint8_t v_contextDependent_3461_; uint8_t v___y_3463_; 
lean_dec_ref_known(v_e_3412_, 2);
v_done_3460_ = lean_ctor_get_uint8(v_a_3456_, 0);
v_contextDependent_3461_ = lean_ctor_get_uint8(v_a_3456_, 1);
lean_dec_ref_known(v_a_3456_, 0);
if (v_contextDependent_3451_ == 0)
{
v___y_3463_ = v_contextDependent_3461_;
goto v___jp_3462_;
}
else
{
v___y_3463_ = v_contextDependent_3451_;
goto v___jp_3462_;
}
v___jp_3462_:
{
lean_object* v___x_3465_; 
if (v_isShared_3454_ == 0)
{
v___x_3465_ = v___x_3453_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_e_x27_3449_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_proof_3450_);
v___x_3465_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
lean_object* v___x_3467_; 
lean_ctor_set_uint8(v___x_3465_, sizeof(void*)*2, v_done_3460_);
lean_ctor_set_uint8(v___x_3465_, sizeof(void*)*2 + 1, v___y_3463_);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 0, v___x_3465_);
v___x_3467_ = v___x_3458_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3465_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
}
else
{
lean_object* v_e_x27_3470_; lean_object* v_proof_3471_; uint8_t v_done_3472_; uint8_t v_contextDependent_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3499_; 
lean_del_object(v___x_3458_);
lean_del_object(v___x_3453_);
v_e_x27_3470_ = lean_ctor_get(v_a_3456_, 0);
v_proof_3471_ = lean_ctor_get(v_a_3456_, 1);
v_done_3472_ = lean_ctor_get_uint8(v_a_3456_, sizeof(void*)*2);
v_contextDependent_3473_ = lean_ctor_get_uint8(v_a_3456_, sizeof(void*)*2 + 1);
v_isSharedCheck_3499_ = !lean_is_exclusive(v_a_3456_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3475_ = v_a_3456_;
v_isShared_3476_ = v_isSharedCheck_3499_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_proof_3471_);
lean_inc(v_e_x27_3470_);
lean_dec(v_a_3456_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3499_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3477_; 
lean_inc_ref(v_e_x27_3470_);
v___x_3477_ = l_Lean_Meta_Sym_Simp_mkEqTrans___redArg(v_e_3412_, v_e_x27_3449_, v_proof_3450_, v_e_x27_3470_, v_proof_3471_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3490_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3480_ = v___x_3477_;
v_isShared_3481_ = v_isSharedCheck_3490_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3477_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3490_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
uint8_t v___y_3483_; 
if (v_contextDependent_3451_ == 0)
{
v___y_3483_ = v_contextDependent_3473_;
goto v___jp_3482_;
}
else
{
v___y_3483_ = v_contextDependent_3451_;
goto v___jp_3482_;
}
v___jp_3482_:
{
lean_object* v___x_3485_; 
if (v_isShared_3476_ == 0)
{
lean_ctor_set(v___x_3475_, 1, v_a_3478_);
v___x_3485_ = v___x_3475_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_e_x27_3470_);
lean_ctor_set(v_reuseFailAlloc_3489_, 1, v_a_3478_);
lean_ctor_set_uint8(v_reuseFailAlloc_3489_, sizeof(void*)*2, v_done_3472_);
v___x_3485_ = v_reuseFailAlloc_3489_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
lean_object* v___x_3487_; 
lean_ctor_set_uint8(v___x_3485_, sizeof(void*)*2 + 1, v___y_3483_);
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 0, v___x_3485_);
v___x_3487_ = v___x_3480_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3485_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
}
else
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3498_; 
lean_del_object(v___x_3475_);
lean_dec_ref(v_e_x27_3470_);
v_a_3491_ = lean_ctor_get(v___x_3477_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3477_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3493_ = v___x_3477_;
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3477_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3496_; 
if (v_isShared_3494_ == 0)
{
v___x_3496_ = v___x_3493_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3491_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3453_);
lean_dec_ref(v_proof_3450_);
lean_dec_ref(v_e_x27_3449_);
lean_dec_ref_known(v_e_3412_, 2);
return v___x_3455_;
}
}
}
else
{
lean_dec_ref_known(v_a_3429_, 2);
lean_dec_ref_known(v_e_3412_, 2);
return v___x_3428_;
}
}
}
else
{
lean_dec_ref_known(v_e_3412_, 2);
return v___x_3428_;
}
}
case 5:
{
lean_object* v___x_3502_; 
lean_inc_ref(v_e_3412_);
v___x_3502_ = l_Lean_Meta_Tactic_Cbv_tryMatcher(v_e_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_a_3503_);
if (lean_obj_tag(v_a_3503_) == 0)
{
uint8_t v_done_3504_; 
v_done_3504_ = lean_ctor_get_uint8(v_a_3503_, 0);
if (v_done_3504_ == 0)
{
uint8_t v_contextDependent_3505_; lean_object* v___x_3506_; 
lean_dec_ref_known(v___x_3502_, 1);
v_contextDependent_3505_ = lean_ctor_get_uint8(v_a_3503_, 1);
lean_dec_ref_known(v_a_3503_, 0);
v___x_3506_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(v_e_3412_, v_a_3413_, v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v_a_3507_; uint8_t v___y_3509_; 
v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
lean_inc(v_a_3507_);
if (v_contextDependent_3505_ == 0)
{
lean_dec(v_a_3507_);
return v___x_3506_;
}
else
{
if (lean_obj_tag(v_a_3507_) == 0)
{
uint8_t v_contextDependent_3519_; 
v_contextDependent_3519_ = lean_ctor_get_uint8(v_a_3507_, 1);
v___y_3509_ = v_contextDependent_3519_;
goto v___jp_3508_;
}
else
{
uint8_t v_contextDependent_3520_; 
v_contextDependent_3520_ = lean_ctor_get_uint8(v_a_3507_, sizeof(void*)*2 + 1);
v___y_3509_ = v_contextDependent_3520_;
goto v___jp_3508_;
}
}
v___jp_3508_:
{
if (v___y_3509_ == 0)
{
lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3517_; 
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3517_ == 0)
{
lean_object* v_unused_3518_; 
v_unused_3518_ = lean_ctor_get(v___x_3506_, 0);
lean_dec(v_unused_3518_);
v___x_3511_ = v___x_3506_;
v_isShared_3512_ = v_isSharedCheck_3517_;
goto v_resetjp_3510_;
}
else
{
lean_dec(v___x_3506_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3517_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3513_; lean_object* v___x_3515_; 
v___x_3513_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3507_);
if (v_isShared_3512_ == 0)
{
lean_ctor_set(v___x_3511_, 0, v___x_3513_);
v___x_3515_ = v___x_3511_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3513_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
else
{
lean_dec(v_a_3507_);
return v___x_3506_;
}
}
}
else
{
return v___x_3506_;
}
}
else
{
lean_dec_ref_known(v_a_3503_, 0);
lean_dec_ref_known(v_e_3412_, 2);
return v___x_3502_;
}
}
else
{
lean_dec_ref_known(v_a_3503_, 2);
lean_dec_ref_known(v_e_3412_, 2);
return v___x_3502_;
}
}
else
{
lean_dec_ref_known(v_e_3412_, 2);
return v___x_3502_;
}
}
case 8:
{
uint8_t v___x_3521_; 
v___x_3521_ = l_Lean_Expr_letNondep_x21(v_e_3412_);
if (v___x_3521_ == 0)
{
lean_object* v___x_3522_; 
v___x_3522_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(v_e_3412_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_);
return v___x_3522_;
}
else
{
lean_object* v___x_3523_; 
v___x_3523_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_e_3412_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3535_; 
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3526_ = v___x_3523_;
v_isShared_3527_ = v_isSharedCheck_3535_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v___x_3523_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3535_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v_e_3528_; lean_object* v_h_3529_; uint8_t v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3533_; 
v_e_3528_ = lean_ctor_get(v_a_3524_, 2);
lean_inc_ref(v_e_3528_);
v_h_3529_ = lean_ctor_get(v_a_3524_, 3);
lean_inc_ref(v_h_3529_);
lean_dec(v_a_3524_);
v___x_3530_ = 0;
v___x_3531_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3531_, 0, v_e_3528_);
lean_ctor_set(v___x_3531_, 1, v_h_3529_);
lean_ctor_set_uint8(v___x_3531_, sizeof(void*)*2, v___x_3530_);
lean_ctor_set_uint8(v___x_3531_, sizeof(void*)*2 + 1, v___x_3530_);
if (v_isShared_3527_ == 0)
{
lean_ctor_set(v___x_3526_, 0, v___x_3531_);
v___x_3533_ = v___x_3526_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3531_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
else
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3543_; 
v_a_3536_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3538_ = v___x_3523_;
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_3523_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3541_; 
if (v_isShared_3539_ == 0)
{
v___x_3541_ = v___x_3538_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3536_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
}
}
case 7:
{
lean_dec_ref_known(v_e_3412_, 3);
goto v___jp_3423_;
}
case 6:
{
lean_dec_ref_known(v_e_3412_, 3);
goto v___jp_3423_;
}
case 1:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
lean_dec_ref_known(v_e_3412_, 1);
v___x_3544_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3544_);
return v___x_3545_;
}
case 2:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; 
lean_dec_ref_known(v_e_3412_, 1);
v___x_3546_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3546_);
return v___x_3547_;
}
case 0:
{
lean_object* v___x_3548_; lean_object* v___x_3549_; 
lean_dec_ref_known(v_e_3412_, 1);
v___x_3548_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3548_);
return v___x_3549_;
}
case 3:
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
lean_dec_ref_known(v_e_3412_, 1);
v___x_3550_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3550_);
return v___x_3551_;
}
default: 
{
lean_object* v___x_3552_; lean_object* v___x_3553_; 
lean_dec_ref(v_e_3412_);
v___x_3552_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_3553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3553_, 0, v___x_3552_);
return v___x_3553_;
}
}
v___jp_3423_:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3424_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3425_, 0, v___x_3424_);
return v___x_3425_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___boxed(lean_object* v_e_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_){
_start:
{
lean_object* v_res_3565_; 
v_res_3565_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(v_e_3554_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
lean_dec_ref(v_a_3560_);
lean_dec(v_a_3559_);
lean_dec_ref(v_a_3558_);
lean_dec(v_a_3557_);
lean_dec_ref(v_a_3556_);
lean_dec(v_a_3555_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre(lean_object* v_simprocs_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_){
_start:
{
lean_object* v___y_3579_; lean_object* v___y_3580_; uint8_t v___y_3581_; lean_object* v___x_3584_; 
lean_inc_ref(v_a_3567_);
v___x_3584_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(v_a_3567_);
if (lean_obj_tag(v___x_3584_) == 0)
{
lean_object* v_a_3585_; 
v_a_3585_ = lean_ctor_get(v___x_3584_, 0);
lean_inc(v_a_3585_);
if (lean_obj_tag(v_a_3585_) == 0)
{
uint8_t v_done_3586_; uint8_t v_contextDependent_3587_; lean_object* v___y_3589_; lean_object* v_a_3590_; lean_object* v___y_3594_; lean_object* v___y_3595_; uint8_t v___y_3596_; lean_object* v___y_3600_; 
v_done_3586_ = lean_ctor_get_uint8(v_a_3585_, 0);
v_contextDependent_3587_ = lean_ctor_get_uint8(v_a_3585_, 1);
lean_dec_ref_known(v_a_3585_, 0);
if (v_done_3586_ == 0)
{
lean_object* v___x_3602_; 
lean_dec_ref_known(v___x_3584_, 1);
lean_inc_ref(v_a_3567_);
v___x_3602_ = l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(v_a_3567_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v_a_3603_; 
v_a_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_a_3603_);
if (lean_obj_tag(v_a_3603_) == 0)
{
uint8_t v_done_3604_; uint8_t v_contextDependent_3605_; lean_object* v___y_3607_; lean_object* v_a_3608_; lean_object* v___y_3612_; 
v_done_3604_ = lean_ctor_get_uint8(v_a_3603_, 0);
v_contextDependent_3605_ = lean_ctor_get_uint8(v_a_3603_, 1);
lean_dec_ref_known(v_a_3603_, 0);
if (v_done_3604_ == 0)
{
lean_object* v_pre_3614_; lean_object* v_erased_3615_; lean_object* v___x_3616_; 
lean_dec_ref_known(v___x_3602_, 1);
v_pre_3614_ = lean_ctor_get(v_simprocs_3566_, 0);
v_erased_3615_ = lean_ctor_get(v_simprocs_3566_, 4);
lean_inc_ref(v_a_3567_);
v___x_3616_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_pre_3614_, v_erased_3615_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v_a_3617_; 
v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
lean_inc(v_a_3617_);
if (lean_obj_tag(v_a_3617_) == 0)
{
uint8_t v_done_3618_; 
v_done_3618_ = lean_ctor_get_uint8(v_a_3617_, 0);
if (v_done_3618_ == 0)
{
uint8_t v_contextDependent_3619_; lean_object* v___x_3620_; 
lean_dec_ref_known(v___x_3616_, 1);
v_contextDependent_3619_ = lean_ctor_get_uint8(v_a_3617_, 1);
lean_dec_ref_known(v_a_3617_, 0);
v___x_3620_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v_a_3621_; uint8_t v___y_3623_; 
v_a_3621_ = lean_ctor_get(v___x_3620_, 0);
lean_inc(v_a_3621_);
if (v_contextDependent_3619_ == 0)
{
lean_dec(v_a_3621_);
v___y_3612_ = v___x_3620_;
goto v___jp_3611_;
}
else
{
if (lean_obj_tag(v_a_3621_) == 0)
{
uint8_t v_contextDependent_3633_; 
v_contextDependent_3633_ = lean_ctor_get_uint8(v_a_3621_, 1);
v___y_3623_ = v_contextDependent_3633_;
goto v___jp_3622_;
}
else
{
uint8_t v_contextDependent_3634_; 
v_contextDependent_3634_ = lean_ctor_get_uint8(v_a_3621_, sizeof(void*)*2 + 1);
v___y_3623_ = v_contextDependent_3634_;
goto v___jp_3622_;
}
}
v___jp_3622_:
{
if (v___y_3623_ == 0)
{
lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3631_; 
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3631_ == 0)
{
lean_object* v_unused_3632_; 
v_unused_3632_ = lean_ctor_get(v___x_3620_, 0);
lean_dec(v_unused_3632_);
v___x_3625_ = v___x_3620_;
v_isShared_3626_ = v_isSharedCheck_3631_;
goto v_resetjp_3624_;
}
else
{
lean_dec(v___x_3620_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3631_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3627_; lean_object* v___x_3629_; 
v___x_3627_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3621_);
lean_inc_ref(v___x_3627_);
if (v_isShared_3626_ == 0)
{
lean_ctor_set(v___x_3625_, 0, v___x_3627_);
v___x_3629_ = v___x_3625_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v___x_3627_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
v___y_3607_ = v___x_3629_;
v_a_3608_ = v___x_3627_;
goto v___jp_3606_;
}
}
}
else
{
lean_dec(v_a_3621_);
v___y_3612_ = v___x_3620_;
goto v___jp_3611_;
}
}
}
else
{
v___y_3612_ = v___x_3620_;
goto v___jp_3611_;
}
}
else
{
lean_dec_ref_known(v_a_3617_, 0);
lean_dec_ref(v_a_3567_);
v___y_3612_ = v___x_3616_;
goto v___jp_3611_;
}
}
else
{
lean_dec_ref_known(v_a_3617_, 2);
lean_dec_ref(v_a_3567_);
v___y_3612_ = v___x_3616_;
goto v___jp_3611_;
}
}
else
{
lean_dec_ref(v_a_3567_);
v___y_3612_ = v___x_3616_;
goto v___jp_3611_;
}
}
else
{
lean_dec_ref(v_a_3567_);
v___y_3600_ = v___x_3602_;
goto v___jp_3599_;
}
v___jp_3606_:
{
if (v_contextDependent_3605_ == 0)
{
v___y_3589_ = v___y_3607_;
v_a_3590_ = v_a_3608_;
goto v___jp_3588_;
}
else
{
if (lean_obj_tag(v_a_3608_) == 0)
{
uint8_t v_contextDependent_3609_; 
v_contextDependent_3609_ = lean_ctor_get_uint8(v_a_3608_, 1);
v___y_3594_ = v___y_3607_;
v___y_3595_ = v_a_3608_;
v___y_3596_ = v_contextDependent_3609_;
goto v___jp_3593_;
}
else
{
uint8_t v_contextDependent_3610_; 
v_contextDependent_3610_ = lean_ctor_get_uint8(v_a_3608_, sizeof(void*)*2 + 1);
v___y_3594_ = v___y_3607_;
v___y_3595_ = v_a_3608_;
v___y_3596_ = v_contextDependent_3610_;
goto v___jp_3593_;
}
}
}
v___jp_3611_:
{
if (lean_obj_tag(v___y_3612_) == 0)
{
lean_object* v_a_3613_; 
v_a_3613_ = lean_ctor_get(v___y_3612_, 0);
lean_inc(v_a_3613_);
v___y_3607_ = v___y_3612_;
v_a_3608_ = v_a_3613_;
goto v___jp_3606_;
}
else
{
return v___y_3612_;
}
}
}
else
{
lean_dec_ref_known(v_a_3603_, 2);
lean_dec_ref(v_a_3567_);
v___y_3600_ = v___x_3602_;
goto v___jp_3599_;
}
}
else
{
lean_dec_ref(v_a_3567_);
v___y_3600_ = v___x_3602_;
goto v___jp_3599_;
}
}
else
{
lean_dec_ref(v_a_3567_);
return v___x_3584_;
}
v___jp_3588_:
{
if (v_contextDependent_3587_ == 0)
{
lean_dec_ref(v_a_3590_);
return v___y_3589_;
}
else
{
if (lean_obj_tag(v_a_3590_) == 0)
{
uint8_t v_contextDependent_3591_; 
v_contextDependent_3591_ = lean_ctor_get_uint8(v_a_3590_, 1);
v___y_3579_ = v_a_3590_;
v___y_3580_ = v___y_3589_;
v___y_3581_ = v_contextDependent_3591_;
goto v___jp_3578_;
}
else
{
uint8_t v_contextDependent_3592_; 
v_contextDependent_3592_ = lean_ctor_get_uint8(v_a_3590_, sizeof(void*)*2 + 1);
v___y_3579_ = v_a_3590_;
v___y_3580_ = v___y_3589_;
v___y_3581_ = v_contextDependent_3592_;
goto v___jp_3578_;
}
}
}
v___jp_3593_:
{
if (v___y_3596_ == 0)
{
lean_object* v___x_3597_; lean_object* v___x_3598_; 
lean_dec_ref(v___y_3594_);
v___x_3597_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3595_);
lean_inc_ref(v___x_3597_);
v___x_3598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3597_);
v___y_3589_ = v___x_3598_;
v_a_3590_ = v___x_3597_;
goto v___jp_3588_;
}
else
{
v___y_3589_ = v___y_3594_;
v_a_3590_ = v___y_3595_;
goto v___jp_3588_;
}
}
v___jp_3599_:
{
if (lean_obj_tag(v___y_3600_) == 0)
{
lean_object* v_a_3601_; 
v_a_3601_ = lean_ctor_get(v___y_3600_, 0);
lean_inc(v_a_3601_);
v___y_3589_ = v___y_3600_;
v_a_3590_ = v_a_3601_;
goto v___jp_3588_;
}
else
{
return v___y_3600_;
}
}
}
else
{
lean_dec_ref_known(v_a_3585_, 2);
lean_dec_ref(v_a_3567_);
return v___x_3584_;
}
}
else
{
lean_dec_ref(v_a_3567_);
return v___x_3584_;
}
v___jp_3578_:
{
if (v___y_3581_ == 0)
{
lean_object* v___x_3582_; lean_object* v___x_3583_; 
lean_dec_ref(v___y_3580_);
v___x_3582_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3579_);
v___x_3583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3582_);
return v___x_3583_;
}
else
{
lean_dec_ref(v___y_3579_);
return v___y_3580_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre___boxed(lean_object* v_simprocs_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_){
_start:
{
lean_object* v_res_3647_; 
v_res_3647_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre(v_simprocs_3635_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_);
lean_dec(v_a_3645_);
lean_dec_ref(v_a_3644_);
lean_dec(v_a_3643_);
lean_dec_ref(v_a_3642_);
lean_dec(v_a_3641_);
lean_dec_ref(v_a_3640_);
lean_dec(v_a_3639_);
lean_dec_ref(v_a_3638_);
lean_dec(v_a_3637_);
lean_dec_ref(v_simprocs_3635_);
return v_res_3647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost(lean_object* v_simprocs_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_){
_start:
{
lean_object* v___y_3661_; lean_object* v___y_3662_; uint8_t v___y_3663_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3666_ = lean_unsigned_to_nat(255u);
lean_inc_ref(v_a_3649_);
v___x_3667_ = l_Lean_Meta_Sym_Simp_evalGround___redArg(v___x_3666_, v_a_3649_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v_a_3668_; 
v_a_3668_ = lean_ctor_get(v___x_3667_, 0);
lean_inc(v_a_3668_);
if (lean_obj_tag(v_a_3668_) == 0)
{
uint8_t v_done_3669_; uint8_t v_contextDependent_3670_; lean_object* v___y_3672_; lean_object* v_a_3673_; lean_object* v___y_3677_; lean_object* v___y_3678_; uint8_t v___y_3679_; lean_object* v___y_3683_; 
v_done_3669_ = lean_ctor_get_uint8(v_a_3668_, 0);
v_contextDependent_3670_ = lean_ctor_get_uint8(v_a_3668_, 1);
lean_dec_ref_known(v_a_3668_, 0);
if (v_done_3669_ == 0)
{
lean_object* v_eval_3685_; lean_object* v_post_3686_; lean_object* v_erased_3687_; lean_object* v___x_3688_; 
lean_dec_ref_known(v___x_3667_, 1);
v_eval_3685_ = lean_ctor_get(v_simprocs_3648_, 1);
v_post_3686_ = lean_ctor_get(v_simprocs_3648_, 2);
v_erased_3687_ = lean_ctor_get(v_simprocs_3648_, 4);
lean_inc_ref(v_a_3649_);
v___x_3688_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_eval_3685_, v_erased_3687_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_object* v_a_3689_; 
v_a_3689_ = lean_ctor_get(v___x_3688_, 0);
lean_inc(v_a_3689_);
if (lean_obj_tag(v_a_3689_) == 0)
{
uint8_t v_done_3690_; uint8_t v_contextDependent_3691_; lean_object* v___y_3693_; lean_object* v_a_3694_; lean_object* v___y_3698_; 
v_done_3690_ = lean_ctor_get_uint8(v_a_3689_, 0);
v_contextDependent_3691_ = lean_ctor_get_uint8(v_a_3689_, 1);
lean_dec_ref_known(v_a_3689_, 0);
if (v_done_3690_ == 0)
{
lean_object* v___x_3700_; 
lean_dec_ref_known(v___x_3688_, 1);
lean_inc_ref(v_a_3649_);
v___x_3700_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp(v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_);
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v_a_3701_; 
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
lean_inc(v_a_3701_);
if (lean_obj_tag(v_a_3701_) == 0)
{
uint8_t v_done_3702_; 
v_done_3702_ = lean_ctor_get_uint8(v_a_3701_, 0);
if (v_done_3702_ == 0)
{
uint8_t v_contextDependent_3703_; lean_object* v___x_3704_; 
lean_dec_ref_known(v___x_3700_, 1);
v_contextDependent_3703_ = lean_ctor_get_uint8(v_a_3701_, 1);
lean_dec_ref_known(v_a_3701_, 0);
v___x_3704_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_post_3686_, v_erased_3687_, v_a_3649_, v_a_3650_, v_a_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_);
if (lean_obj_tag(v___x_3704_) == 0)
{
lean_object* v_a_3705_; uint8_t v___y_3707_; 
v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
lean_inc(v_a_3705_);
if (v_contextDependent_3703_ == 0)
{
lean_dec(v_a_3705_);
v___y_3698_ = v___x_3704_;
goto v___jp_3697_;
}
else
{
if (lean_obj_tag(v_a_3705_) == 0)
{
uint8_t v_contextDependent_3717_; 
v_contextDependent_3717_ = lean_ctor_get_uint8(v_a_3705_, 1);
v___y_3707_ = v_contextDependent_3717_;
goto v___jp_3706_;
}
else
{
uint8_t v_contextDependent_3718_; 
v_contextDependent_3718_ = lean_ctor_get_uint8(v_a_3705_, sizeof(void*)*2 + 1);
v___y_3707_ = v_contextDependent_3718_;
goto v___jp_3706_;
}
}
v___jp_3706_:
{
if (v___y_3707_ == 0)
{
lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3715_; 
v_isSharedCheck_3715_ = !lean_is_exclusive(v___x_3704_);
if (v_isSharedCheck_3715_ == 0)
{
lean_object* v_unused_3716_; 
v_unused_3716_ = lean_ctor_get(v___x_3704_, 0);
lean_dec(v_unused_3716_);
v___x_3709_ = v___x_3704_;
v_isShared_3710_ = v_isSharedCheck_3715_;
goto v_resetjp_3708_;
}
else
{
lean_dec(v___x_3704_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3715_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___x_3711_; lean_object* v___x_3713_; 
v___x_3711_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3705_);
lean_inc_ref(v___x_3711_);
if (v_isShared_3710_ == 0)
{
lean_ctor_set(v___x_3709_, 0, v___x_3711_);
v___x_3713_ = v___x_3709_;
goto v_reusejp_3712_;
}
else
{
lean_object* v_reuseFailAlloc_3714_; 
v_reuseFailAlloc_3714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3714_, 0, v___x_3711_);
v___x_3713_ = v_reuseFailAlloc_3714_;
goto v_reusejp_3712_;
}
v_reusejp_3712_:
{
v___y_3693_ = v___x_3713_;
v_a_3694_ = v___x_3711_;
goto v___jp_3692_;
}
}
}
else
{
lean_dec(v_a_3705_);
v___y_3698_ = v___x_3704_;
goto v___jp_3697_;
}
}
}
else
{
v___y_3698_ = v___x_3704_;
goto v___jp_3697_;
}
}
else
{
lean_dec_ref_known(v_a_3701_, 0);
lean_dec_ref(v_a_3649_);
v___y_3698_ = v___x_3700_;
goto v___jp_3697_;
}
}
else
{
lean_dec_ref_known(v_a_3701_, 2);
lean_dec_ref(v_a_3649_);
v___y_3698_ = v___x_3700_;
goto v___jp_3697_;
}
}
else
{
lean_dec_ref(v_a_3649_);
v___y_3698_ = v___x_3700_;
goto v___jp_3697_;
}
}
else
{
lean_dec_ref(v_a_3649_);
v___y_3683_ = v___x_3688_;
goto v___jp_3682_;
}
v___jp_3692_:
{
if (v_contextDependent_3691_ == 0)
{
v___y_3672_ = v___y_3693_;
v_a_3673_ = v_a_3694_;
goto v___jp_3671_;
}
else
{
if (lean_obj_tag(v_a_3694_) == 0)
{
uint8_t v_contextDependent_3695_; 
v_contextDependent_3695_ = lean_ctor_get_uint8(v_a_3694_, 1);
v___y_3677_ = v___y_3693_;
v___y_3678_ = v_a_3694_;
v___y_3679_ = v_contextDependent_3695_;
goto v___jp_3676_;
}
else
{
uint8_t v_contextDependent_3696_; 
v_contextDependent_3696_ = lean_ctor_get_uint8(v_a_3694_, sizeof(void*)*2 + 1);
v___y_3677_ = v___y_3693_;
v___y_3678_ = v_a_3694_;
v___y_3679_ = v_contextDependent_3696_;
goto v___jp_3676_;
}
}
}
v___jp_3697_:
{
if (lean_obj_tag(v___y_3698_) == 0)
{
lean_object* v_a_3699_; 
v_a_3699_ = lean_ctor_get(v___y_3698_, 0);
lean_inc(v_a_3699_);
v___y_3693_ = v___y_3698_;
v_a_3694_ = v_a_3699_;
goto v___jp_3692_;
}
else
{
return v___y_3698_;
}
}
}
else
{
lean_dec_ref_known(v_a_3689_, 2);
lean_dec_ref(v_a_3649_);
v___y_3683_ = v___x_3688_;
goto v___jp_3682_;
}
}
else
{
lean_dec_ref(v_a_3649_);
v___y_3683_ = v___x_3688_;
goto v___jp_3682_;
}
}
else
{
lean_dec_ref(v_a_3649_);
return v___x_3667_;
}
v___jp_3671_:
{
if (v_contextDependent_3670_ == 0)
{
lean_dec_ref(v_a_3673_);
return v___y_3672_;
}
else
{
if (lean_obj_tag(v_a_3673_) == 0)
{
uint8_t v_contextDependent_3674_; 
v_contextDependent_3674_ = lean_ctor_get_uint8(v_a_3673_, 1);
v___y_3661_ = v___y_3672_;
v___y_3662_ = v_a_3673_;
v___y_3663_ = v_contextDependent_3674_;
goto v___jp_3660_;
}
else
{
uint8_t v_contextDependent_3675_; 
v_contextDependent_3675_ = lean_ctor_get_uint8(v_a_3673_, sizeof(void*)*2 + 1);
v___y_3661_ = v___y_3672_;
v___y_3662_ = v_a_3673_;
v___y_3663_ = v_contextDependent_3675_;
goto v___jp_3660_;
}
}
}
v___jp_3676_:
{
if (v___y_3679_ == 0)
{
lean_object* v___x_3680_; lean_object* v___x_3681_; 
lean_dec_ref(v___y_3677_);
v___x_3680_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3678_);
lean_inc_ref(v___x_3680_);
v___x_3681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3680_);
v___y_3672_ = v___x_3681_;
v_a_3673_ = v___x_3680_;
goto v___jp_3671_;
}
else
{
v___y_3672_ = v___y_3677_;
v_a_3673_ = v___y_3678_;
goto v___jp_3671_;
}
}
v___jp_3682_:
{
if (lean_obj_tag(v___y_3683_) == 0)
{
lean_object* v_a_3684_; 
v_a_3684_ = lean_ctor_get(v___y_3683_, 0);
lean_inc(v_a_3684_);
v___y_3672_ = v___y_3683_;
v_a_3673_ = v_a_3684_;
goto v___jp_3671_;
}
else
{
return v___y_3683_;
}
}
}
else
{
lean_dec_ref_known(v_a_3668_, 2);
lean_dec_ref(v_a_3649_);
return v___x_3667_;
}
}
else
{
lean_dec_ref(v_a_3649_);
return v___x_3667_;
}
v___jp_3660_:
{
if (v___y_3663_ == 0)
{
lean_object* v___x_3664_; lean_object* v___x_3665_; 
lean_dec_ref(v___y_3661_);
v___x_3664_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3662_);
v___x_3665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3664_);
return v___x_3665_;
}
else
{
lean_dec_ref(v___y_3662_);
return v___y_3661_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost___boxed(lean_object* v_simprocs_3719_, lean_object* v_a_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost(v_simprocs_3719_, v_a_3720_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_);
lean_dec(v_a_3729_);
lean_dec_ref(v_a_3728_);
lean_dec(v_a_3727_);
lean_dec_ref(v_a_3726_);
lean_dec(v_a_3725_);
lean_dec_ref(v_a_3724_);
lean_dec(v_a_3723_);
lean_dec_ref(v_a_3722_);
lean_dec(v_a_3721_);
lean_dec_ref(v_simprocs_3719_);
return v_res_3731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(lean_object* v_simprocs_3732_){
_start:
{
lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
lean_inc_ref(v_simprocs_3732_);
v___x_3733_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre___boxed), 12, 1);
lean_closure_set(v___x_3733_, 0, v_simprocs_3732_);
v___x_3734_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost___boxed), 12, 1);
lean_closure_set(v___x_3734_, 0, v_simprocs_3732_);
v___x_3735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3733_);
lean_ctor_set(v___x_3735_, 1, v___x_3734_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(lean_object* v_e_3736_, lean_object* v_config_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_){
_start:
{
lean_object* v___x_3745_; 
v___x_3745_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_3743_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_a_3746_);
lean_dec_ref_known(v___x_3745_, 1);
v___x_3747_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_3746_);
v___x_3748_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3748_, 0, v_e_3736_);
v___x_3749_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_3748_, v___x_3747_, v_config_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_, v_a_3742_, v_a_3743_);
return v___x_3749_;
}
else
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3757_; 
lean_dec_ref(v_config_3737_);
lean_dec_ref(v_e_3736_);
v_a_3750_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3752_ = v___x_3745_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3745_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3755_; 
if (v_isShared_3753_ == 0)
{
v___x_3755_ = v___x_3752_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3750_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___boxed(lean_object* v_e_3758_, lean_object* v_config_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_){
_start:
{
lean_object* v_res_3767_; 
v_res_3767_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_e_3758_, v_config_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_);
lean_dec(v_a_3765_);
lean_dec_ref(v_a_3764_);
lean_dec(v_a_3763_);
lean_dec_ref(v_a_3762_);
lean_dec(v_a_3761_);
lean_dec_ref(v_a_3760_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(lean_object* v___y_3768_){
_start:
{
lean_object* v___x_3770_; lean_object* v_traceState_3771_; lean_object* v_traces_3772_; lean_object* v___x_3773_; lean_object* v_traceState_3774_; lean_object* v_env_3775_; lean_object* v_nextMacroScope_3776_; lean_object* v_ngen_3777_; lean_object* v_auxDeclNGen_3778_; lean_object* v_cache_3779_; lean_object* v_messages_3780_; lean_object* v_infoState_3781_; lean_object* v_snapshotTasks_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3803_; 
v___x_3770_ = lean_st_ref_get(v___y_3768_);
v_traceState_3771_ = lean_ctor_get(v___x_3770_, 4);
lean_inc_ref(v_traceState_3771_);
lean_dec(v___x_3770_);
v_traces_3772_ = lean_ctor_get(v_traceState_3771_, 0);
lean_inc_ref(v_traces_3772_);
lean_dec_ref(v_traceState_3771_);
v___x_3773_ = lean_st_ref_take(v___y_3768_);
v_traceState_3774_ = lean_ctor_get(v___x_3773_, 4);
v_env_3775_ = lean_ctor_get(v___x_3773_, 0);
v_nextMacroScope_3776_ = lean_ctor_get(v___x_3773_, 1);
v_ngen_3777_ = lean_ctor_get(v___x_3773_, 2);
v_auxDeclNGen_3778_ = lean_ctor_get(v___x_3773_, 3);
v_cache_3779_ = lean_ctor_get(v___x_3773_, 5);
v_messages_3780_ = lean_ctor_get(v___x_3773_, 6);
v_infoState_3781_ = lean_ctor_get(v___x_3773_, 7);
v_snapshotTasks_3782_ = lean_ctor_get(v___x_3773_, 8);
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3773_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3784_ = v___x_3773_;
v_isShared_3785_ = v_isSharedCheck_3803_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_snapshotTasks_3782_);
lean_inc(v_infoState_3781_);
lean_inc(v_messages_3780_);
lean_inc(v_cache_3779_);
lean_inc(v_traceState_3774_);
lean_inc(v_auxDeclNGen_3778_);
lean_inc(v_ngen_3777_);
lean_inc(v_nextMacroScope_3776_);
lean_inc(v_env_3775_);
lean_dec(v___x_3773_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3803_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
uint64_t v_tid_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3801_; 
v_tid_3786_ = lean_ctor_get_uint64(v_traceState_3774_, sizeof(void*)*1);
v_isSharedCheck_3801_ = !lean_is_exclusive(v_traceState_3774_);
if (v_isSharedCheck_3801_ == 0)
{
lean_object* v_unused_3802_; 
v_unused_3802_ = lean_ctor_get(v_traceState_3774_, 0);
lean_dec(v_unused_3802_);
v___x_3788_ = v_traceState_3774_;
v_isShared_3789_ = v_isSharedCheck_3801_;
goto v_resetjp_3787_;
}
else
{
lean_dec(v_traceState_3774_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3801_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3794_; 
v___x_3790_ = lean_unsigned_to_nat(32u);
v___x_3791_ = lean_mk_empty_array_with_capacity(v___x_3790_);
lean_dec_ref(v___x_3791_);
v___x_3792_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1);
if (v_isShared_3789_ == 0)
{
lean_ctor_set(v___x_3788_, 0, v___x_3792_);
v___x_3794_ = v___x_3788_;
goto v_reusejp_3793_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v___x_3792_);
lean_ctor_set_uint64(v_reuseFailAlloc_3800_, sizeof(void*)*1, v_tid_3786_);
v___x_3794_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3793_;
}
v_reusejp_3793_:
{
lean_object* v___x_3796_; 
if (v_isShared_3785_ == 0)
{
lean_ctor_set(v___x_3784_, 4, v___x_3794_);
v___x_3796_ = v___x_3784_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_env_3775_);
lean_ctor_set(v_reuseFailAlloc_3799_, 1, v_nextMacroScope_3776_);
lean_ctor_set(v_reuseFailAlloc_3799_, 2, v_ngen_3777_);
lean_ctor_set(v_reuseFailAlloc_3799_, 3, v_auxDeclNGen_3778_);
lean_ctor_set(v_reuseFailAlloc_3799_, 4, v___x_3794_);
lean_ctor_set(v_reuseFailAlloc_3799_, 5, v_cache_3779_);
lean_ctor_set(v_reuseFailAlloc_3799_, 6, v_messages_3780_);
lean_ctor_set(v_reuseFailAlloc_3799_, 7, v_infoState_3781_);
lean_ctor_set(v_reuseFailAlloc_3799_, 8, v_snapshotTasks_3782_);
v___x_3796_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3797_ = lean_st_ref_set(v___y_3768_, v___x_3796_);
v___x_3798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3798_, 0, v_traces_3772_);
return v___x_3798_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg___boxed(lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v___y_3804_);
lean_dec(v___y_3804_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0(lean_object* v___y_3807_, lean_object* v___y_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_){
_start:
{
lean_object* v___x_3812_; 
v___x_3812_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v___y_3810_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___boxed(lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0(v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
return v_res_3818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0(lean_object* v_a_3819_, lean_object* v___x_3820_, lean_object* v___x_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_, lean_object* v___y_3826_, lean_object* v___y_3827_){
_start:
{
lean_object* v___x_3829_; 
v___x_3829_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_3819_, v___y_3823_);
if (lean_obj_tag(v___x_3829_) == 0)
{
lean_object* v_a_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
v_a_3830_ = lean_ctor_get(v___x_3829_, 0);
lean_inc(v_a_3830_);
lean_dec_ref_known(v___x_3829_, 1);
v___x_3831_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3831_, 0, v_a_3830_);
v___x_3832_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_3831_, v___x_3820_, v___x_3821_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_);
return v___x_3832_;
}
else
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3840_; 
lean_dec_ref(v___x_3821_);
lean_dec_ref(v___x_3820_);
v_a_3833_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3835_ = v___x_3829_;
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v___x_3829_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3838_; 
if (v_isShared_3836_ == 0)
{
v___x_3838_ = v___x_3835_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_a_3833_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed(lean_object* v_a_3841_, lean_object* v___x_3842_, lean_object* v___x_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
lean_object* v_res_3851_; 
v_res_3851_ = l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0(v_a_3841_, v___x_3842_, v___x_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
return v_res_3851_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3853_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__0));
v___x_3854_ = l_Lean_stringToMessageData(v___x_3853_);
return v___x_3854_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3856_; lean_object* v___x_3857_; 
v___x_3856_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__2));
v___x_3857_ = l_Lean_stringToMessageData(v___x_3856_);
return v___x_3857_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3859_; lean_object* v___x_3860_; 
v___x_3859_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__4));
v___x_3860_ = l_Lean_stringToMessageData(v___x_3859_);
return v___x_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1(lean_object* v_e_3861_, lean_object* v_x_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_){
_start:
{
if (lean_obj_tag(v_x_3862_) == 0)
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3878_; 
lean_dec_ref(v_e_3861_);
v_a_3868_ = lean_ctor_get(v_x_3862_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v_x_3862_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3870_ = v_x_3862_;
v_isShared_3871_ = v_isSharedCheck_3878_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v_x_3862_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3878_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3876_; 
v___x_3872_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1);
v___x_3873_ = l_Lean_Exception_toMessageData(v_a_3868_);
v___x_3874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3872_);
lean_ctor_set(v___x_3874_, 1, v___x_3873_);
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 0, v___x_3874_);
v___x_3876_ = v___x_3870_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v___x_3874_);
v___x_3876_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
return v___x_3876_;
}
}
}
else
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3900_; 
v_a_3879_ = lean_ctor_get(v_x_3862_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v_x_3862_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3881_ = v_x_3862_;
v_isShared_3882_ = v_isSharedCheck_3900_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v_x_3862_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3900_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
if (lean_obj_tag(v_a_3879_) == 0)
{
lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3887_; 
lean_dec_ref_known(v_a_3879_, 0);
v___x_3883_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3);
v___x_3884_ = l_Lean_indentExpr(v_e_3861_);
v___x_3885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3885_, 0, v___x_3883_);
lean_ctor_set(v___x_3885_, 1, v___x_3884_);
if (v_isShared_3882_ == 0)
{
lean_ctor_set_tag(v___x_3881_, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3885_);
v___x_3887_ = v___x_3881_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3888_; 
v_reuseFailAlloc_3888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3888_, 0, v___x_3885_);
v___x_3887_ = v_reuseFailAlloc_3888_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
return v___x_3887_;
}
}
else
{
lean_object* v_e_x27_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3898_; 
v_e_x27_3889_ = lean_ctor_get(v_a_3879_, 0);
lean_inc_ref(v_e_x27_3889_);
lean_dec_ref_known(v_a_3879_, 2);
v___x_3890_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5);
v___x_3891_ = l_Lean_indentExpr(v_e_3861_);
v___x_3892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3890_);
lean_ctor_set(v___x_3892_, 1, v___x_3891_);
v___x_3893_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_3894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3892_);
lean_ctor_set(v___x_3894_, 1, v___x_3893_);
v___x_3895_ = l_Lean_indentExpr(v_e_x27_3889_);
v___x_3896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3894_);
lean_ctor_set(v___x_3896_, 1, v___x_3895_);
if (v_isShared_3882_ == 0)
{
lean_ctor_set_tag(v___x_3881_, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3896_);
v___x_3898_ = v___x_3881_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v___x_3896_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___boxed(lean_object* v_e_3901_, lean_object* v_x_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_){
_start:
{
lean_object* v_res_3908_; 
v_res_3908_ = l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1(v_e_3901_, v_x_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
lean_dec(v___y_3906_);
lean_dec_ref(v___y_3905_);
lean_dec(v___y_3904_);
lean_dec_ref(v___y_3903_);
return v_res_3908_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(lean_object* v_x_3909_){
_start:
{
if (lean_obj_tag(v_x_3909_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3918_; 
v_a_3911_ = lean_ctor_get(v_x_3909_, 0);
v_isSharedCheck_3918_ = !lean_is_exclusive(v_x_3909_);
if (v_isSharedCheck_3918_ == 0)
{
v___x_3913_ = v_x_3909_;
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v_x_3909_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v___x_3916_; 
if (v_isShared_3914_ == 0)
{
lean_ctor_set_tag(v___x_3913_, 1);
v___x_3916_ = v___x_3913_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_a_3911_);
v___x_3916_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
return v___x_3916_;
}
}
}
else
{
lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3926_; 
v_a_3919_ = lean_ctor_get(v_x_3909_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v_x_3909_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3921_ = v_x_3909_;
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v_x_3909_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3924_; 
if (v_isShared_3922_ == 0)
{
lean_ctor_set_tag(v___x_3921_, 0);
v___x_3924_ = v___x_3921_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3919_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg___boxed(lean_object* v_x_3927_, lean_object* v___y_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_x_3927_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(lean_object* v_oldTraces_3930_, lean_object* v_data_3931_, lean_object* v_ref_3932_, lean_object* v_msg_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_){
_start:
{
lean_object* v_fileName_3939_; lean_object* v_fileMap_3940_; lean_object* v_options_3941_; lean_object* v_currRecDepth_3942_; lean_object* v_maxRecDepth_3943_; lean_object* v_ref_3944_; lean_object* v_currNamespace_3945_; lean_object* v_openDecls_3946_; lean_object* v_initHeartbeats_3947_; lean_object* v_maxHeartbeats_3948_; lean_object* v_quotContext_3949_; lean_object* v_currMacroScope_3950_; uint8_t v_diag_3951_; lean_object* v_cancelTk_x3f_3952_; uint8_t v_suppressElabErrors_3953_; lean_object* v_inheritedTraceOptions_3954_; lean_object* v___x_3955_; lean_object* v_traceState_3956_; lean_object* v_traces_3957_; lean_object* v_ref_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; size_t v_sz_3961_; size_t v___x_3962_; lean_object* v___x_3963_; lean_object* v_msg_3964_; lean_object* v___x_3965_; lean_object* v_a_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_4003_; 
v_fileName_3939_ = lean_ctor_get(v___y_3936_, 0);
v_fileMap_3940_ = lean_ctor_get(v___y_3936_, 1);
v_options_3941_ = lean_ctor_get(v___y_3936_, 2);
v_currRecDepth_3942_ = lean_ctor_get(v___y_3936_, 3);
v_maxRecDepth_3943_ = lean_ctor_get(v___y_3936_, 4);
v_ref_3944_ = lean_ctor_get(v___y_3936_, 5);
v_currNamespace_3945_ = lean_ctor_get(v___y_3936_, 6);
v_openDecls_3946_ = lean_ctor_get(v___y_3936_, 7);
v_initHeartbeats_3947_ = lean_ctor_get(v___y_3936_, 8);
v_maxHeartbeats_3948_ = lean_ctor_get(v___y_3936_, 9);
v_quotContext_3949_ = lean_ctor_get(v___y_3936_, 10);
v_currMacroScope_3950_ = lean_ctor_get(v___y_3936_, 11);
v_diag_3951_ = lean_ctor_get_uint8(v___y_3936_, sizeof(void*)*14);
v_cancelTk_x3f_3952_ = lean_ctor_get(v___y_3936_, 12);
v_suppressElabErrors_3953_ = lean_ctor_get_uint8(v___y_3936_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3954_ = lean_ctor_get(v___y_3936_, 13);
v___x_3955_ = lean_st_ref_get(v___y_3937_);
v_traceState_3956_ = lean_ctor_get(v___x_3955_, 4);
lean_inc_ref(v_traceState_3956_);
lean_dec(v___x_3955_);
v_traces_3957_ = lean_ctor_get(v_traceState_3956_, 0);
lean_inc_ref(v_traces_3957_);
lean_dec_ref(v_traceState_3956_);
v_ref_3958_ = l_Lean_replaceRef(v_ref_3932_, v_ref_3944_);
lean_inc_ref(v_inheritedTraceOptions_3954_);
lean_inc(v_cancelTk_x3f_3952_);
lean_inc(v_currMacroScope_3950_);
lean_inc(v_quotContext_3949_);
lean_inc(v_maxHeartbeats_3948_);
lean_inc(v_initHeartbeats_3947_);
lean_inc(v_openDecls_3946_);
lean_inc(v_currNamespace_3945_);
lean_inc(v_maxRecDepth_3943_);
lean_inc(v_currRecDepth_3942_);
lean_inc_ref(v_options_3941_);
lean_inc_ref(v_fileMap_3940_);
lean_inc_ref(v_fileName_3939_);
v___x_3959_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3959_, 0, v_fileName_3939_);
lean_ctor_set(v___x_3959_, 1, v_fileMap_3940_);
lean_ctor_set(v___x_3959_, 2, v_options_3941_);
lean_ctor_set(v___x_3959_, 3, v_currRecDepth_3942_);
lean_ctor_set(v___x_3959_, 4, v_maxRecDepth_3943_);
lean_ctor_set(v___x_3959_, 5, v_ref_3958_);
lean_ctor_set(v___x_3959_, 6, v_currNamespace_3945_);
lean_ctor_set(v___x_3959_, 7, v_openDecls_3946_);
lean_ctor_set(v___x_3959_, 8, v_initHeartbeats_3947_);
lean_ctor_set(v___x_3959_, 9, v_maxHeartbeats_3948_);
lean_ctor_set(v___x_3959_, 10, v_quotContext_3949_);
lean_ctor_set(v___x_3959_, 11, v_currMacroScope_3950_);
lean_ctor_set(v___x_3959_, 12, v_cancelTk_x3f_3952_);
lean_ctor_set(v___x_3959_, 13, v_inheritedTraceOptions_3954_);
lean_ctor_set_uint8(v___x_3959_, sizeof(void*)*14, v_diag_3951_);
lean_ctor_set_uint8(v___x_3959_, sizeof(void*)*14 + 1, v_suppressElabErrors_3953_);
v___x_3960_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3957_);
lean_dec_ref(v_traces_3957_);
v_sz_3961_ = lean_array_size(v___x_3960_);
v___x_3962_ = ((size_t)0ULL);
v___x_3963_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5(v_sz_3961_, v___x_3962_, v___x_3960_);
v_msg_3964_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3964_, 0, v_data_3931_);
lean_ctor_set(v_msg_3964_, 1, v_msg_3933_);
lean_ctor_set(v_msg_3964_, 2, v___x_3963_);
v___x_3965_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_3964_, v___y_3934_, v___y_3935_, v___x_3959_, v___y_3937_);
lean_dec_ref_known(v___x_3959_, 14);
v_a_3966_ = lean_ctor_get(v___x_3965_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3968_ = v___x_3965_;
v_isShared_3969_ = v_isSharedCheck_4003_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_a_3966_);
lean_dec(v___x_3965_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_4003_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3970_; lean_object* v_traceState_3971_; lean_object* v_env_3972_; lean_object* v_nextMacroScope_3973_; lean_object* v_ngen_3974_; lean_object* v_auxDeclNGen_3975_; lean_object* v_cache_3976_; lean_object* v_messages_3977_; lean_object* v_infoState_3978_; lean_object* v_snapshotTasks_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_4002_; 
v___x_3970_ = lean_st_ref_take(v___y_3937_);
v_traceState_3971_ = lean_ctor_get(v___x_3970_, 4);
v_env_3972_ = lean_ctor_get(v___x_3970_, 0);
v_nextMacroScope_3973_ = lean_ctor_get(v___x_3970_, 1);
v_ngen_3974_ = lean_ctor_get(v___x_3970_, 2);
v_auxDeclNGen_3975_ = lean_ctor_get(v___x_3970_, 3);
v_cache_3976_ = lean_ctor_get(v___x_3970_, 5);
v_messages_3977_ = lean_ctor_get(v___x_3970_, 6);
v_infoState_3978_ = lean_ctor_get(v___x_3970_, 7);
v_snapshotTasks_3979_ = lean_ctor_get(v___x_3970_, 8);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3970_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3981_ = v___x_3970_;
v_isShared_3982_ = v_isSharedCheck_4002_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_snapshotTasks_3979_);
lean_inc(v_infoState_3978_);
lean_inc(v_messages_3977_);
lean_inc(v_cache_3976_);
lean_inc(v_traceState_3971_);
lean_inc(v_auxDeclNGen_3975_);
lean_inc(v_ngen_3974_);
lean_inc(v_nextMacroScope_3973_);
lean_inc(v_env_3972_);
lean_dec(v___x_3970_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_4002_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
uint64_t v_tid_3983_; lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_4000_; 
v_tid_3983_ = lean_ctor_get_uint64(v_traceState_3971_, sizeof(void*)*1);
v_isSharedCheck_4000_ = !lean_is_exclusive(v_traceState_3971_);
if (v_isSharedCheck_4000_ == 0)
{
lean_object* v_unused_4001_; 
v_unused_4001_ = lean_ctor_get(v_traceState_3971_, 0);
lean_dec(v_unused_4001_);
v___x_3985_ = v_traceState_3971_;
v_isShared_3986_ = v_isSharedCheck_4000_;
goto v_resetjp_3984_;
}
else
{
lean_dec(v_traceState_3971_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_4000_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3990_; 
v___x_3987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3987_, 0, v_ref_3932_);
lean_ctor_set(v___x_3987_, 1, v_a_3966_);
v___x_3988_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3930_, v___x_3987_);
if (v_isShared_3986_ == 0)
{
lean_ctor_set(v___x_3985_, 0, v___x_3988_);
v___x_3990_ = v___x_3985_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v___x_3988_);
lean_ctor_set_uint64(v_reuseFailAlloc_3999_, sizeof(void*)*1, v_tid_3983_);
v___x_3990_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
lean_object* v___x_3992_; 
if (v_isShared_3982_ == 0)
{
lean_ctor_set(v___x_3981_, 4, v___x_3990_);
v___x_3992_ = v___x_3981_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_env_3972_);
lean_ctor_set(v_reuseFailAlloc_3998_, 1, v_nextMacroScope_3973_);
lean_ctor_set(v_reuseFailAlloc_3998_, 2, v_ngen_3974_);
lean_ctor_set(v_reuseFailAlloc_3998_, 3, v_auxDeclNGen_3975_);
lean_ctor_set(v_reuseFailAlloc_3998_, 4, v___x_3990_);
lean_ctor_set(v_reuseFailAlloc_3998_, 5, v_cache_3976_);
lean_ctor_set(v_reuseFailAlloc_3998_, 6, v_messages_3977_);
lean_ctor_set(v_reuseFailAlloc_3998_, 7, v_infoState_3978_);
lean_ctor_set(v_reuseFailAlloc_3998_, 8, v_snapshotTasks_3979_);
v___x_3992_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3996_; 
v___x_3993_ = lean_st_ref_set(v___y_3937_, v___x_3992_);
v___x_3994_ = lean_box(0);
if (v_isShared_3969_ == 0)
{
lean_ctor_set(v___x_3968_, 0, v___x_3994_);
v___x_3996_ = v___x_3968_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v___x_3994_);
v___x_3996_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
return v___x_3996_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1___boxed(lean_object* v_oldTraces_4004_, lean_object* v_data_4005_, lean_object* v_ref_4006_, lean_object* v_msg_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
lean_object* v_res_4013_; 
v_res_4013_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(v_oldTraces_4004_, v_data_4005_, v_ref_4006_, v_msg_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4010_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(lean_object* v_cls_4014_, uint8_t v_collapsed_4015_, lean_object* v_tag_4016_, lean_object* v_opts_4017_, uint8_t v_clsEnabled_4018_, lean_object* v_oldTraces_4019_, lean_object* v_msg_4020_, lean_object* v_resStartStop_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
lean_object* v_fst_4027_; lean_object* v_snd_4028_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v_data_4032_; lean_object* v_fst_4043_; lean_object* v_snd_4044_; lean_object* v___x_4045_; uint8_t v___x_4046_; lean_object* v___y_4048_; lean_object* v_a_4049_; uint8_t v___y_4064_; double v___y_4095_; 
v_fst_4027_ = lean_ctor_get(v_resStartStop_4021_, 0);
lean_inc(v_fst_4027_);
v_snd_4028_ = lean_ctor_get(v_resStartStop_4021_, 1);
lean_inc(v_snd_4028_);
lean_dec_ref(v_resStartStop_4021_);
v_fst_4043_ = lean_ctor_get(v_snd_4028_, 0);
lean_inc(v_fst_4043_);
v_snd_4044_ = lean_ctor_get(v_snd_4028_, 1);
lean_inc(v_snd_4044_);
lean_dec(v_snd_4028_);
v___x_4045_ = l_Lean_trace_profiler;
v___x_4046_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4017_, v___x_4045_);
if (v___x_4046_ == 0)
{
v___y_4064_ = v___x_4046_;
goto v___jp_4063_;
}
else
{
lean_object* v___x_4100_; uint8_t v___x_4101_; 
v___x_4100_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4101_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4017_, v___x_4100_);
if (v___x_4101_ == 0)
{
lean_object* v___x_4102_; lean_object* v___x_4103_; double v___x_4104_; double v___x_4105_; double v___x_4106_; 
v___x_4102_ = l_Lean_trace_profiler_threshold;
v___x_4103_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4017_, v___x_4102_);
v___x_4104_ = lean_float_of_nat(v___x_4103_);
v___x_4105_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2);
v___x_4106_ = lean_float_div(v___x_4104_, v___x_4105_);
v___y_4095_ = v___x_4106_;
goto v___jp_4094_;
}
else
{
lean_object* v___x_4107_; lean_object* v___x_4108_; double v___x_4109_; 
v___x_4107_ = l_Lean_trace_profiler_threshold;
v___x_4108_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4017_, v___x_4107_);
v___x_4109_ = lean_float_of_nat(v___x_4108_);
v___y_4095_ = v___x_4109_;
goto v___jp_4094_;
}
}
v___jp_4029_:
{
lean_object* v___x_4033_; 
lean_inc(v___y_4030_);
v___x_4033_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(v_oldTraces_4019_, v_data_4032_, v___y_4030_, v___y_4031_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_object* v___x_4034_; 
lean_dec_ref_known(v___x_4033_, 1);
v___x_4034_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_4027_);
return v___x_4034_;
}
else
{
lean_object* v_a_4035_; lean_object* v___x_4037_; uint8_t v_isShared_4038_; uint8_t v_isSharedCheck_4042_; 
lean_dec(v_fst_4027_);
v_a_4035_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4037_ = v___x_4033_;
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
else
{
lean_inc(v_a_4035_);
lean_dec(v___x_4033_);
v___x_4037_ = lean_box(0);
v_isShared_4038_ = v_isSharedCheck_4042_;
goto v_resetjp_4036_;
}
v_resetjp_4036_:
{
lean_object* v___x_4040_; 
if (v_isShared_4038_ == 0)
{
v___x_4040_ = v___x_4037_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_a_4035_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
}
}
v___jp_4047_:
{
uint8_t v_result_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; double v___x_4053_; lean_object* v_data_4054_; 
v_result_4050_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(v_fst_4027_);
v___x_4051_ = lean_box(v_result_4050_);
v___x_4052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4051_);
v___x_4053_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_4016_);
lean_inc_ref(v___x_4052_);
lean_inc(v_cls_4014_);
v_data_4054_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4054_, 0, v_cls_4014_);
lean_ctor_set(v_data_4054_, 1, v___x_4052_);
lean_ctor_set(v_data_4054_, 2, v_tag_4016_);
lean_ctor_set_float(v_data_4054_, sizeof(void*)*3, v___x_4053_);
lean_ctor_set_float(v_data_4054_, sizeof(void*)*3 + 8, v___x_4053_);
lean_ctor_set_uint8(v_data_4054_, sizeof(void*)*3 + 16, v_collapsed_4015_);
if (v___x_4046_ == 0)
{
lean_dec_ref_known(v___x_4052_, 1);
lean_dec(v_snd_4044_);
lean_dec(v_fst_4043_);
lean_dec_ref(v_tag_4016_);
lean_dec(v_cls_4014_);
v___y_4030_ = v___y_4048_;
v___y_4031_ = v_a_4049_;
v_data_4032_ = v_data_4054_;
goto v___jp_4029_;
}
else
{
lean_object* v_data_4055_; double v___x_4056_; double v___x_4057_; 
lean_dec_ref_known(v_data_4054_, 3);
v_data_4055_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4055_, 0, v_cls_4014_);
lean_ctor_set(v_data_4055_, 1, v___x_4052_);
lean_ctor_set(v_data_4055_, 2, v_tag_4016_);
v___x_4056_ = lean_unbox_float(v_fst_4043_);
lean_dec(v_fst_4043_);
lean_ctor_set_float(v_data_4055_, sizeof(void*)*3, v___x_4056_);
v___x_4057_ = lean_unbox_float(v_snd_4044_);
lean_dec(v_snd_4044_);
lean_ctor_set_float(v_data_4055_, sizeof(void*)*3 + 8, v___x_4057_);
lean_ctor_set_uint8(v_data_4055_, sizeof(void*)*3 + 16, v_collapsed_4015_);
v___y_4030_ = v___y_4048_;
v___y_4031_ = v_a_4049_;
v_data_4032_ = v_data_4055_;
goto v___jp_4029_;
}
}
v___jp_4058_:
{
lean_object* v_ref_4059_; lean_object* v___x_4060_; 
v_ref_4059_ = lean_ctor_get(v___y_4024_, 5);
lean_inc(v___y_4025_);
lean_inc_ref(v___y_4024_);
lean_inc(v___y_4023_);
lean_inc_ref(v___y_4022_);
lean_inc(v_fst_4027_);
v___x_4060_ = lean_apply_6(v_msg_4020_, v_fst_4027_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, lean_box(0));
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_object* v_a_4061_; 
v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
lean_inc(v_a_4061_);
lean_dec_ref_known(v___x_4060_, 1);
v___y_4048_ = v_ref_4059_;
v_a_4049_ = v_a_4061_;
goto v___jp_4047_;
}
else
{
lean_object* v___x_4062_; 
lean_dec_ref_known(v___x_4060_, 1);
v___x_4062_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
v___y_4048_ = v_ref_4059_;
v_a_4049_ = v___x_4062_;
goto v___jp_4047_;
}
}
v___jp_4063_:
{
if (v_clsEnabled_4018_ == 0)
{
if (v___y_4064_ == 0)
{
lean_object* v___x_4065_; lean_object* v_traceState_4066_; lean_object* v_env_4067_; lean_object* v_nextMacroScope_4068_; lean_object* v_ngen_4069_; lean_object* v_auxDeclNGen_4070_; lean_object* v_cache_4071_; lean_object* v_messages_4072_; lean_object* v_infoState_4073_; lean_object* v_snapshotTasks_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4093_; 
lean_dec(v_snd_4044_);
lean_dec(v_fst_4043_);
lean_dec_ref(v_msg_4020_);
lean_dec_ref(v_tag_4016_);
lean_dec(v_cls_4014_);
v___x_4065_ = lean_st_ref_take(v___y_4025_);
v_traceState_4066_ = lean_ctor_get(v___x_4065_, 4);
v_env_4067_ = lean_ctor_get(v___x_4065_, 0);
v_nextMacroScope_4068_ = lean_ctor_get(v___x_4065_, 1);
v_ngen_4069_ = lean_ctor_get(v___x_4065_, 2);
v_auxDeclNGen_4070_ = lean_ctor_get(v___x_4065_, 3);
v_cache_4071_ = lean_ctor_get(v___x_4065_, 5);
v_messages_4072_ = lean_ctor_get(v___x_4065_, 6);
v_infoState_4073_ = lean_ctor_get(v___x_4065_, 7);
v_snapshotTasks_4074_ = lean_ctor_get(v___x_4065_, 8);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4065_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4076_ = v___x_4065_;
v_isShared_4077_ = v_isSharedCheck_4093_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_snapshotTasks_4074_);
lean_inc(v_infoState_4073_);
lean_inc(v_messages_4072_);
lean_inc(v_cache_4071_);
lean_inc(v_traceState_4066_);
lean_inc(v_auxDeclNGen_4070_);
lean_inc(v_ngen_4069_);
lean_inc(v_nextMacroScope_4068_);
lean_inc(v_env_4067_);
lean_dec(v___x_4065_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4093_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
uint64_t v_tid_4078_; lean_object* v_traces_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4092_; 
v_tid_4078_ = lean_ctor_get_uint64(v_traceState_4066_, sizeof(void*)*1);
v_traces_4079_ = lean_ctor_get(v_traceState_4066_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v_traceState_4066_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4081_ = v_traceState_4066_;
v_isShared_4082_ = v_isSharedCheck_4092_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_traces_4079_);
lean_dec(v_traceState_4066_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4092_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4083_; lean_object* v___x_4085_; 
v___x_4083_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4019_, v_traces_4079_);
lean_dec_ref(v_traces_4079_);
if (v_isShared_4082_ == 0)
{
lean_ctor_set(v___x_4081_, 0, v___x_4083_);
v___x_4085_ = v___x_4081_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v___x_4083_);
lean_ctor_set_uint64(v_reuseFailAlloc_4091_, sizeof(void*)*1, v_tid_4078_);
v___x_4085_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
lean_object* v___x_4087_; 
if (v_isShared_4077_ == 0)
{
lean_ctor_set(v___x_4076_, 4, v___x_4085_);
v___x_4087_ = v___x_4076_;
goto v_reusejp_4086_;
}
else
{
lean_object* v_reuseFailAlloc_4090_; 
v_reuseFailAlloc_4090_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4090_, 0, v_env_4067_);
lean_ctor_set(v_reuseFailAlloc_4090_, 1, v_nextMacroScope_4068_);
lean_ctor_set(v_reuseFailAlloc_4090_, 2, v_ngen_4069_);
lean_ctor_set(v_reuseFailAlloc_4090_, 3, v_auxDeclNGen_4070_);
lean_ctor_set(v_reuseFailAlloc_4090_, 4, v___x_4085_);
lean_ctor_set(v_reuseFailAlloc_4090_, 5, v_cache_4071_);
lean_ctor_set(v_reuseFailAlloc_4090_, 6, v_messages_4072_);
lean_ctor_set(v_reuseFailAlloc_4090_, 7, v_infoState_4073_);
lean_ctor_set(v_reuseFailAlloc_4090_, 8, v_snapshotTasks_4074_);
v___x_4087_ = v_reuseFailAlloc_4090_;
goto v_reusejp_4086_;
}
v_reusejp_4086_:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; 
v___x_4088_ = lean_st_ref_set(v___y_4025_, v___x_4087_);
v___x_4089_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_4027_);
return v___x_4089_;
}
}
}
}
}
else
{
goto v___jp_4058_;
}
}
else
{
goto v___jp_4058_;
}
}
v___jp_4094_:
{
double v___x_4096_; double v___x_4097_; double v___x_4098_; uint8_t v___x_4099_; 
v___x_4096_ = lean_unbox_float(v_snd_4044_);
v___x_4097_ = lean_unbox_float(v_fst_4043_);
v___x_4098_ = lean_float_sub(v___x_4096_, v___x_4097_);
v___x_4099_ = lean_float_decLt(v___y_4095_, v___x_4098_);
v___y_4064_ = v___x_4099_;
goto v___jp_4063_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1___boxed(lean_object* v_cls_4110_, lean_object* v_collapsed_4111_, lean_object* v_tag_4112_, lean_object* v_opts_4113_, lean_object* v_clsEnabled_4114_, lean_object* v_oldTraces_4115_, lean_object* v_msg_4116_, lean_object* v_resStartStop_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_){
_start:
{
uint8_t v_collapsed_boxed_4123_; uint8_t v_clsEnabled_boxed_4124_; lean_object* v_res_4125_; 
v_collapsed_boxed_4123_ = lean_unbox(v_collapsed_4111_);
v_clsEnabled_boxed_4124_ = lean_unbox(v_clsEnabled_4114_);
v_res_4125_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(v_cls_4110_, v_collapsed_boxed_4123_, v_tag_4112_, v_opts_4113_, v_clsEnabled_boxed_4124_, v_oldTraces_4115_, v_msg_4116_, v_resStartStop_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
lean_dec_ref(v_opts_4113_);
return v_res_4125_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1(void){
_start:
{
lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
v___x_4130_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_4131_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
v___x_4132_ = l_Lean_Name_append(v___x_4131_, v___x_4130_);
return v___x_4132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry(lean_object* v_e_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_){
_start:
{
lean_object* v_options_4139_; uint8_t v_hasTrace_4140_; 
v_options_4139_ = lean_ctor_get(v_a_4136_, 2);
v_hasTrace_4140_ = lean_ctor_get_uint8(v_options_4139_, sizeof(void*)*1);
if (v_hasTrace_4140_ == 0)
{
lean_object* v___x_4141_; 
v___x_4141_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4137_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v_a_4142_; lean_object* v___x_4143_; 
v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_a_4142_);
lean_dec_ref_known(v___x_4141_, 1);
v___x_4143_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v_a_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___f_4150_; lean_object* v___x_4151_; 
v_a_4144_ = lean_ctor_get(v___x_4143_, 0);
lean_inc(v_a_4144_);
lean_dec_ref_known(v___x_4143_, 1);
v___x_4145_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4146_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4139_, v___x_4145_);
v___x_4147_ = lean_unsigned_to_nat(2u);
v___x_4148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4146_);
lean_ctor_set(v___x_4148_, 1, v___x_4147_);
v___x_4149_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4142_);
v___f_4150_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4150_, 0, v_a_4144_);
lean_closure_set(v___f_4150_, 1, v___x_4149_);
lean_closure_set(v___f_4150_, 2, v___x_4148_);
v___x_4151_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_4150_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_);
return v___x_4151_;
}
else
{
lean_object* v_a_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4159_; 
lean_dec(v_a_4142_);
v_a_4152_ = lean_ctor_get(v___x_4143_, 0);
v_isSharedCheck_4159_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4159_ == 0)
{
v___x_4154_ = v___x_4143_;
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_a_4152_);
lean_dec(v___x_4143_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4157_; 
if (v_isShared_4155_ == 0)
{
v___x_4157_ = v___x_4154_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_a_4152_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
return v___x_4157_;
}
}
}
}
else
{
lean_object* v_a_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4167_; 
lean_dec_ref(v_e_4133_);
v_a_4160_ = lean_ctor_get(v___x_4141_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_4141_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4162_ = v___x_4141_;
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_a_4160_);
lean_dec(v___x_4141_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___x_4165_; 
if (v_isShared_4163_ == 0)
{
v___x_4165_ = v___x_4162_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v_a_4160_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
return v___x_4165_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_4168_; lean_object* v___f_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; uint8_t v___x_4173_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v_a_4177_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v_a_4192_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v_a_4197_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v_a_4209_; 
v_inheritedTraceOptions_4168_ = lean_ctor_get(v_a_4136_, 13);
lean_inc_ref(v_e_4133_);
v___f_4169_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___boxed), 7, 1);
lean_closure_set(v___f_4169_, 0, v_e_4133_);
v___x_4170_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_4171_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_4172_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_4173_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4168_, v_options_4139_, v___x_4172_);
if (v___x_4173_ == 0)
{
lean_object* v___x_4262_; uint8_t v___x_4263_; 
v___x_4262_ = l_Lean_trace_profiler;
v___x_4263_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_4139_, v___x_4262_);
if (v___x_4263_ == 0)
{
lean_object* v___x_4264_; 
lean_dec_ref(v___f_4169_);
v___x_4264_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4137_);
if (lean_obj_tag(v___x_4264_) == 0)
{
lean_object* v_a_4265_; lean_object* v___x_4266_; 
v_a_4265_ = lean_ctor_get(v___x_4264_, 0);
lean_inc(v_a_4265_);
lean_dec_ref_known(v___x_4264_, 1);
v___x_4266_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_);
if (lean_obj_tag(v___x_4266_) == 0)
{
lean_object* v_a_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___f_4273_; lean_object* v___x_4274_; 
v_a_4267_ = lean_ctor_get(v___x_4266_, 0);
lean_inc(v_a_4267_);
lean_dec_ref_known(v___x_4266_, 1);
v___x_4268_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4269_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4139_, v___x_4268_);
v___x_4270_ = lean_unsigned_to_nat(2u);
v___x_4271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4271_, 0, v___x_4269_);
lean_ctor_set(v___x_4271_, 1, v___x_4270_);
v___x_4272_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4265_);
v___f_4273_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4273_, 0, v_a_4267_);
lean_closure_set(v___f_4273_, 1, v___x_4272_);
lean_closure_set(v___f_4273_, 2, v___x_4271_);
v___x_4274_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_4273_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_);
return v___x_4274_;
}
else
{
lean_object* v_a_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4282_; 
lean_dec(v_a_4265_);
v_a_4275_ = lean_ctor_get(v___x_4266_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4277_ = v___x_4266_;
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_a_4275_);
lean_dec(v___x_4266_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
lean_object* v___x_4280_; 
if (v_isShared_4278_ == 0)
{
v___x_4280_ = v___x_4277_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_a_4275_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
return v___x_4280_;
}
}
}
}
else
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4290_; 
lean_dec_ref(v_e_4133_);
v_a_4283_ = lean_ctor_get(v___x_4264_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4285_ = v___x_4264_;
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v___x_4264_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4288_; 
if (v_isShared_4286_ == 0)
{
v___x_4288_ = v___x_4285_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_a_4283_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
return v___x_4288_;
}
}
}
}
else
{
goto v___jp_4211_;
}
}
else
{
goto v___jp_4211_;
}
v___jp_4174_:
{
lean_object* v___x_4178_; double v___x_4179_; double v___x_4180_; double v___x_4181_; double v___x_4182_; double v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4178_ = lean_io_mono_nanos_now();
v___x_4179_ = lean_float_of_nat(v___y_4176_);
v___x_4180_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_4181_ = lean_float_div(v___x_4179_, v___x_4180_);
v___x_4182_ = lean_float_of_nat(v___x_4178_);
v___x_4183_ = lean_float_div(v___x_4182_, v___x_4180_);
v___x_4184_ = lean_box_float(v___x_4181_);
v___x_4185_ = lean_box_float(v___x_4183_);
v___x_4186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4186_, 0, v___x_4184_);
lean_ctor_set(v___x_4186_, 1, v___x_4185_);
v___x_4187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4187_, 0, v_a_4177_);
lean_ctor_set(v___x_4187_, 1, v___x_4186_);
v___x_4188_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(v___x_4170_, v_hasTrace_4140_, v___x_4171_, v_options_4139_, v___x_4173_, v___y_4175_, v___f_4169_, v___x_4187_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_);
return v___x_4188_;
}
v___jp_4189_:
{
lean_object* v___x_4193_; 
v___x_4193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4193_, 0, v_a_4192_);
v___y_4175_ = v___y_4190_;
v___y_4176_ = v___y_4191_;
v_a_4177_ = v___x_4193_;
goto v___jp_4174_;
}
v___jp_4194_:
{
lean_object* v___x_4198_; double v___x_4199_; double v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4198_ = lean_io_get_num_heartbeats();
v___x_4199_ = lean_float_of_nat(v___y_4195_);
v___x_4200_ = lean_float_of_nat(v___x_4198_);
v___x_4201_ = lean_box_float(v___x_4199_);
v___x_4202_ = lean_box_float(v___x_4200_);
v___x_4203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4203_, 0, v___x_4201_);
lean_ctor_set(v___x_4203_, 1, v___x_4202_);
v___x_4204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4204_, 0, v_a_4197_);
lean_ctor_set(v___x_4204_, 1, v___x_4203_);
v___x_4205_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(v___x_4170_, v_hasTrace_4140_, v___x_4171_, v_options_4139_, v___x_4173_, v___y_4196_, v___f_4169_, v___x_4204_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_);
return v___x_4205_;
}
v___jp_4206_:
{
lean_object* v___x_4210_; 
v___x_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4210_, 0, v_a_4209_);
v___y_4195_ = v___y_4207_;
v___y_4196_ = v___y_4208_;
v_a_4197_ = v___x_4210_;
goto v___jp_4194_;
}
v___jp_4211_:
{
lean_object* v___x_4212_; lean_object* v_a_4213_; lean_object* v___x_4214_; uint8_t v___x_4215_; 
v___x_4212_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v_a_4137_);
v_a_4213_ = lean_ctor_get(v___x_4212_, 0);
lean_inc(v_a_4213_);
lean_dec_ref(v___x_4212_);
v___x_4214_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4215_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_4139_, v___x_4214_);
if (v___x_4215_ == 0)
{
lean_object* v___x_4216_; lean_object* v___x_4217_; 
v___x_4216_ = lean_io_mono_nanos_now();
v___x_4217_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4137_);
if (lean_obj_tag(v___x_4217_) == 0)
{
lean_object* v_a_4218_; lean_object* v___x_4219_; 
v_a_4218_ = lean_ctor_get(v___x_4217_, 0);
lean_inc(v_a_4218_);
lean_dec_ref_known(v___x_4217_, 1);
v___x_4219_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_);
if (lean_obj_tag(v___x_4219_) == 0)
{
lean_object* v_a_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; lean_object* v___f_4226_; lean_object* v___x_4227_; 
v_a_4220_ = lean_ctor_get(v___x_4219_, 0);
lean_inc(v_a_4220_);
lean_dec_ref_known(v___x_4219_, 1);
v___x_4221_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4222_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4139_, v___x_4221_);
v___x_4223_ = lean_unsigned_to_nat(2u);
v___x_4224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4224_, 0, v___x_4222_);
lean_ctor_set(v___x_4224_, 1, v___x_4223_);
v___x_4225_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4218_);
v___f_4226_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4226_, 0, v_a_4220_);
lean_closure_set(v___f_4226_, 1, v___x_4225_);
lean_closure_set(v___f_4226_, 2, v___x_4224_);
v___x_4227_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_4226_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_object* v_a_4228_; lean_object* v___x_4230_; uint8_t v_isShared_4231_; uint8_t v_isSharedCheck_4235_; 
v_a_4228_ = lean_ctor_get(v___x_4227_, 0);
v_isSharedCheck_4235_ = !lean_is_exclusive(v___x_4227_);
if (v_isSharedCheck_4235_ == 0)
{
v___x_4230_ = v___x_4227_;
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
else
{
lean_inc(v_a_4228_);
lean_dec(v___x_4227_);
v___x_4230_ = lean_box(0);
v_isShared_4231_ = v_isSharedCheck_4235_;
goto v_resetjp_4229_;
}
v_resetjp_4229_:
{
lean_object* v___x_4233_; 
if (v_isShared_4231_ == 0)
{
lean_ctor_set_tag(v___x_4230_, 1);
v___x_4233_ = v___x_4230_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4234_; 
v_reuseFailAlloc_4234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4234_, 0, v_a_4228_);
v___x_4233_ = v_reuseFailAlloc_4234_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
v___y_4175_ = v_a_4213_;
v___y_4176_ = v___x_4216_;
v_a_4177_ = v___x_4233_;
goto v___jp_4174_;
}
}
}
else
{
lean_object* v_a_4236_; 
v_a_4236_ = lean_ctor_get(v___x_4227_, 0);
lean_inc(v_a_4236_);
lean_dec_ref_known(v___x_4227_, 1);
v___y_4190_ = v_a_4213_;
v___y_4191_ = v___x_4216_;
v_a_4192_ = v_a_4236_;
goto v___jp_4189_;
}
}
else
{
lean_object* v_a_4237_; 
lean_dec(v_a_4218_);
v_a_4237_ = lean_ctor_get(v___x_4219_, 0);
lean_inc(v_a_4237_);
lean_dec_ref_known(v___x_4219_, 1);
v___y_4190_ = v_a_4213_;
v___y_4191_ = v___x_4216_;
v_a_4192_ = v_a_4237_;
goto v___jp_4189_;
}
}
else
{
lean_object* v_a_4238_; 
lean_dec_ref(v_e_4133_);
v_a_4238_ = lean_ctor_get(v___x_4217_, 0);
lean_inc(v_a_4238_);
lean_dec_ref_known(v___x_4217_, 1);
v___y_4190_ = v_a_4213_;
v___y_4191_ = v___x_4216_;
v_a_4192_ = v_a_4238_;
goto v___jp_4189_;
}
}
else
{
lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4239_ = lean_io_get_num_heartbeats();
v___x_4240_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4137_);
if (lean_obj_tag(v___x_4240_) == 0)
{
lean_object* v_a_4241_; lean_object* v___x_4242_; 
v_a_4241_ = lean_ctor_get(v___x_4240_, 0);
lean_inc(v_a_4241_);
lean_dec_ref_known(v___x_4240_, 1);
v___x_4242_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4133_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_);
if (lean_obj_tag(v___x_4242_) == 0)
{
lean_object* v_a_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___f_4249_; lean_object* v___x_4250_; 
v_a_4243_ = lean_ctor_get(v___x_4242_, 0);
lean_inc(v_a_4243_);
lean_dec_ref_known(v___x_4242_, 1);
v___x_4244_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4245_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4139_, v___x_4244_);
v___x_4246_ = lean_unsigned_to_nat(2u);
v___x_4247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4247_, 0, v___x_4245_);
lean_ctor_set(v___x_4247_, 1, v___x_4246_);
v___x_4248_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4241_);
v___f_4249_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4249_, 0, v_a_4243_);
lean_closure_set(v___f_4249_, 1, v___x_4248_);
lean_closure_set(v___f_4249_, 2, v___x_4247_);
v___x_4250_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_4249_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_);
if (lean_obj_tag(v___x_4250_) == 0)
{
lean_object* v_a_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4258_; 
v_a_4251_ = lean_ctor_get(v___x_4250_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4250_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4253_ = v___x_4250_;
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_a_4251_);
lean_dec(v___x_4250_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v___x_4256_; 
if (v_isShared_4254_ == 0)
{
lean_ctor_set_tag(v___x_4253_, 1);
v___x_4256_ = v___x_4253_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_a_4251_);
v___x_4256_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
v___y_4195_ = v___x_4239_;
v___y_4196_ = v_a_4213_;
v_a_4197_ = v___x_4256_;
goto v___jp_4194_;
}
}
}
else
{
lean_object* v_a_4259_; 
v_a_4259_ = lean_ctor_get(v___x_4250_, 0);
lean_inc(v_a_4259_);
lean_dec_ref_known(v___x_4250_, 1);
v___y_4207_ = v___x_4239_;
v___y_4208_ = v_a_4213_;
v_a_4209_ = v_a_4259_;
goto v___jp_4206_;
}
}
else
{
lean_object* v_a_4260_; 
lean_dec(v_a_4241_);
v_a_4260_ = lean_ctor_get(v___x_4242_, 0);
lean_inc(v_a_4260_);
lean_dec_ref_known(v___x_4242_, 1);
v___y_4207_ = v___x_4239_;
v___y_4208_ = v_a_4213_;
v_a_4209_ = v_a_4260_;
goto v___jp_4206_;
}
}
else
{
lean_object* v_a_4261_; 
lean_dec_ref(v_e_4133_);
v_a_4261_ = lean_ctor_get(v___x_4240_, 0);
lean_inc(v_a_4261_);
lean_dec_ref_known(v___x_4240_, 1);
v___y_4207_ = v___x_4239_;
v___y_4208_ = v_a_4213_;
v_a_4209_ = v_a_4261_;
goto v___jp_4206_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___boxed(lean_object* v_e_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_){
_start:
{
lean_object* v_res_4297_; 
v_res_4297_ = l_Lean_Meta_Tactic_Cbv_cbvEntry(v_e_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_);
lean_dec(v_a_4295_);
lean_dec_ref(v_a_4294_);
lean_dec(v_a_4293_);
lean_dec_ref(v_a_4292_);
return v_res_4297_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2(lean_object* v_00_u03b1_4298_, lean_object* v_x_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_){
_start:
{
lean_object* v___x_4305_; 
v___x_4305_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_x_4299_);
return v___x_4305_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___boxed(lean_object* v_00_u03b1_4306_, lean_object* v_x_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_){
_start:
{
lean_object* v_res_4313_; 
v_res_4313_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2(v_00_u03b1_4306_, v_x_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_);
lean_dec(v___y_4311_);
lean_dec_ref(v___y_4310_);
lean_dec(v___y_4309_);
lean_dec_ref(v___y_4308_);
return v_res_4313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(lean_object* v___y_4314_){
_start:
{
lean_object* v___x_4316_; lean_object* v_traceState_4317_; lean_object* v_traces_4318_; lean_object* v___x_4319_; lean_object* v_traceState_4320_; lean_object* v_env_4321_; lean_object* v_nextMacroScope_4322_; lean_object* v_ngen_4323_; lean_object* v_auxDeclNGen_4324_; lean_object* v_cache_4325_; lean_object* v_messages_4326_; lean_object* v_infoState_4327_; lean_object* v_snapshotTasks_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4349_; 
v___x_4316_ = lean_st_ref_get(v___y_4314_);
v_traceState_4317_ = lean_ctor_get(v___x_4316_, 4);
lean_inc_ref(v_traceState_4317_);
lean_dec(v___x_4316_);
v_traces_4318_ = lean_ctor_get(v_traceState_4317_, 0);
lean_inc_ref(v_traces_4318_);
lean_dec_ref(v_traceState_4317_);
v___x_4319_ = lean_st_ref_take(v___y_4314_);
v_traceState_4320_ = lean_ctor_get(v___x_4319_, 4);
v_env_4321_ = lean_ctor_get(v___x_4319_, 0);
v_nextMacroScope_4322_ = lean_ctor_get(v___x_4319_, 1);
v_ngen_4323_ = lean_ctor_get(v___x_4319_, 2);
v_auxDeclNGen_4324_ = lean_ctor_get(v___x_4319_, 3);
v_cache_4325_ = lean_ctor_get(v___x_4319_, 5);
v_messages_4326_ = lean_ctor_get(v___x_4319_, 6);
v_infoState_4327_ = lean_ctor_get(v___x_4319_, 7);
v_snapshotTasks_4328_ = lean_ctor_get(v___x_4319_, 8);
v_isSharedCheck_4349_ = !lean_is_exclusive(v___x_4319_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4330_ = v___x_4319_;
v_isShared_4331_ = v_isSharedCheck_4349_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_snapshotTasks_4328_);
lean_inc(v_infoState_4327_);
lean_inc(v_messages_4326_);
lean_inc(v_cache_4325_);
lean_inc(v_traceState_4320_);
lean_inc(v_auxDeclNGen_4324_);
lean_inc(v_ngen_4323_);
lean_inc(v_nextMacroScope_4322_);
lean_inc(v_env_4321_);
lean_dec(v___x_4319_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4349_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
uint64_t v_tid_4332_; lean_object* v___x_4334_; uint8_t v_isShared_4335_; uint8_t v_isSharedCheck_4347_; 
v_tid_4332_ = lean_ctor_get_uint64(v_traceState_4320_, sizeof(void*)*1);
v_isSharedCheck_4347_ = !lean_is_exclusive(v_traceState_4320_);
if (v_isSharedCheck_4347_ == 0)
{
lean_object* v_unused_4348_; 
v_unused_4348_ = lean_ctor_get(v_traceState_4320_, 0);
lean_dec(v_unused_4348_);
v___x_4334_ = v_traceState_4320_;
v_isShared_4335_ = v_isSharedCheck_4347_;
goto v_resetjp_4333_;
}
else
{
lean_dec(v_traceState_4320_);
v___x_4334_ = lean_box(0);
v_isShared_4335_ = v_isSharedCheck_4347_;
goto v_resetjp_4333_;
}
v_resetjp_4333_:
{
lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4340_; 
v___x_4336_ = lean_unsigned_to_nat(32u);
v___x_4337_ = lean_mk_empty_array_with_capacity(v___x_4336_);
lean_dec_ref(v___x_4337_);
v___x_4338_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1);
if (v_isShared_4335_ == 0)
{
lean_ctor_set(v___x_4334_, 0, v___x_4338_);
v___x_4340_ = v___x_4334_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v___x_4338_);
lean_ctor_set_uint64(v_reuseFailAlloc_4346_, sizeof(void*)*1, v_tid_4332_);
v___x_4340_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
lean_object* v___x_4342_; 
if (v_isShared_4331_ == 0)
{
lean_ctor_set(v___x_4330_, 4, v___x_4340_);
v___x_4342_ = v___x_4330_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_env_4321_);
lean_ctor_set(v_reuseFailAlloc_4345_, 1, v_nextMacroScope_4322_);
lean_ctor_set(v_reuseFailAlloc_4345_, 2, v_ngen_4323_);
lean_ctor_set(v_reuseFailAlloc_4345_, 3, v_auxDeclNGen_4324_);
lean_ctor_set(v_reuseFailAlloc_4345_, 4, v___x_4340_);
lean_ctor_set(v_reuseFailAlloc_4345_, 5, v_cache_4325_);
lean_ctor_set(v_reuseFailAlloc_4345_, 6, v_messages_4326_);
lean_ctor_set(v_reuseFailAlloc_4345_, 7, v_infoState_4327_);
lean_ctor_set(v_reuseFailAlloc_4345_, 8, v_snapshotTasks_4328_);
v___x_4342_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
lean_object* v___x_4343_; lean_object* v___x_4344_; 
v___x_4343_ = lean_st_ref_set(v___y_4314_, v___x_4342_);
v___x_4344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4344_, 0, v_traces_4318_);
return v___x_4344_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg___boxed(lean_object* v___y_4350_, lean_object* v___y_4351_){
_start:
{
lean_object* v_res_4352_; 
v_res_4352_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(v___y_4350_);
lean_dec(v___y_4350_);
return v_res_4352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1(lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_){
_start:
{
lean_object* v___x_4360_; 
v___x_4360_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(v___y_4358_);
return v___x_4360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___boxed(lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_){
_start:
{
lean_object* v_res_4368_; 
v_res_4368_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1(v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_);
lean_dec(v___y_4366_);
lean_dec_ref(v___y_4365_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
lean_dec(v___y_4362_);
lean_dec_ref(v___y_4361_);
return v_res_4368_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0(lean_object* v_x_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_){
_start:
{
lean_object* v___x_4377_; 
lean_inc(v___y_4371_);
lean_inc_ref(v___y_4370_);
v___x_4377_ = lean_apply_7(v_x_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_, lean_box(0));
return v___x_4377_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0___boxed(lean_object* v_x_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_){
_start:
{
lean_object* v_res_4386_; 
v_res_4386_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0(v_x_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
return v_res_4386_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg(lean_object* v_mvarId_4387_, lean_object* v_x_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_){
_start:
{
lean_object* v___f_4396_; lean_object* v___x_4397_; 
lean_inc(v___y_4390_);
lean_inc_ref(v___y_4389_);
v___f_4396_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4396_, 0, v_x_4388_);
lean_closure_set(v___f_4396_, 1, v___y_4389_);
lean_closure_set(v___f_4396_, 2, v___y_4390_);
v___x_4397_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4387_, v___f_4396_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
if (lean_obj_tag(v___x_4397_) == 0)
{
return v___x_4397_;
}
else
{
lean_object* v_a_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4405_; 
v_a_4398_ = lean_ctor_get(v___x_4397_, 0);
v_isSharedCheck_4405_ = !lean_is_exclusive(v___x_4397_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4400_ = v___x_4397_;
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_a_4398_);
lean_dec(v___x_4397_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4403_; 
if (v_isShared_4401_ == 0)
{
v___x_4403_ = v___x_4400_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_a_4398_);
v___x_4403_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
return v___x_4403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___boxed(lean_object* v_mvarId_4406_, lean_object* v_x_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_){
_start:
{
lean_object* v_res_4415_; 
v_res_4415_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg(v_mvarId_4406_, v_x_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
lean_dec(v___y_4413_);
lean_dec_ref(v___y_4412_);
lean_dec(v___y_4411_);
lean_dec_ref(v___y_4410_);
lean_dec(v___y_4409_);
lean_dec_ref(v___y_4408_);
return v_res_4415_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4(lean_object* v_00_u03b1_4416_, lean_object* v_mvarId_4417_, lean_object* v_x_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_){
_start:
{
lean_object* v___x_4426_; 
v___x_4426_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg(v_mvarId_4417_, v_x_4418_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___boxed(lean_object* v_00_u03b1_4427_, lean_object* v_mvarId_4428_, lean_object* v_x_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_){
_start:
{
lean_object* v_res_4437_; 
v_res_4437_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4(v_00_u03b1_4427_, v_mvarId_4428_, v_x_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
return v_res_4437_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4439_; lean_object* v___x_4440_; 
v___x_4439_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__0));
v___x_4440_ = l_Lean_stringToMessageData(v___x_4439_);
return v___x_4440_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4442_; lean_object* v___x_4443_; 
v___x_4442_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__2));
v___x_4443_ = l_Lean_stringToMessageData(v___x_4442_);
return v___x_4443_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4445_; lean_object* v___x_4446_; 
v___x_4445_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__4));
v___x_4446_ = l_Lean_stringToMessageData(v___x_4445_);
return v___x_4446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0(lean_object* v_a_4447_, lean_object* v_x_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_){
_start:
{
if (lean_obj_tag(v_x_4448_) == 0)
{
lean_object* v_a_4456_; lean_object* v___x_4458_; uint8_t v_isShared_4459_; uint8_t v_isSharedCheck_4466_; 
lean_dec_ref(v_a_4447_);
v_a_4456_ = lean_ctor_get(v_x_4448_, 0);
v_isSharedCheck_4466_ = !lean_is_exclusive(v_x_4448_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4458_ = v_x_4448_;
v_isShared_4459_ = v_isSharedCheck_4466_;
goto v_resetjp_4457_;
}
else
{
lean_inc(v_a_4456_);
lean_dec(v_x_4448_);
v___x_4458_ = lean_box(0);
v_isShared_4459_ = v_isSharedCheck_4466_;
goto v_resetjp_4457_;
}
v_resetjp_4457_:
{
lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4464_; 
v___x_4460_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1);
v___x_4461_ = l_Lean_Exception_toMessageData(v_a_4456_);
v___x_4462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4462_, 0, v___x_4460_);
lean_ctor_set(v___x_4462_, 1, v___x_4461_);
if (v_isShared_4459_ == 0)
{
lean_ctor_set(v___x_4458_, 0, v___x_4462_);
v___x_4464_ = v___x_4458_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v___x_4462_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
return v___x_4464_;
}
}
}
else
{
lean_object* v_a_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4486_; 
v_a_4467_ = lean_ctor_get(v_x_4448_, 0);
v_isSharedCheck_4486_ = !lean_is_exclusive(v_x_4448_);
if (v_isSharedCheck_4486_ == 0)
{
v___x_4469_ = v_x_4448_;
v_isShared_4470_ = v_isSharedCheck_4486_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_a_4467_);
lean_dec(v_x_4448_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4486_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
if (lean_obj_tag(v_a_4467_) == 0)
{
lean_object* v___x_4471_; lean_object* v___x_4473_; 
lean_dec_ref_known(v_a_4467_, 0);
lean_dec_ref(v_a_4447_);
v___x_4471_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3);
if (v_isShared_4470_ == 0)
{
lean_ctor_set_tag(v___x_4469_, 0);
lean_ctor_set(v___x_4469_, 0, v___x_4471_);
v___x_4473_ = v___x_4469_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v___x_4471_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
else
{
lean_object* v_e_x27_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4484_; 
v_e_x27_4475_ = lean_ctor_get(v_a_4467_, 0);
lean_inc_ref(v_e_x27_4475_);
lean_dec_ref_known(v_a_4467_, 2);
v___x_4476_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5, &l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5);
v___x_4477_ = l_Lean_indentExpr(v_a_4447_);
v___x_4478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4478_, 0, v___x_4476_);
lean_ctor_set(v___x_4478_, 1, v___x_4477_);
v___x_4479_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_4480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4480_, 0, v___x_4478_);
lean_ctor_set(v___x_4480_, 1, v___x_4479_);
v___x_4481_ = l_Lean_indentExpr(v_e_x27_4475_);
v___x_4482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4482_, 0, v___x_4480_);
lean_ctor_set(v___x_4482_, 1, v___x_4481_);
if (v_isShared_4470_ == 0)
{
lean_ctor_set_tag(v___x_4469_, 0);
lean_ctor_set(v___x_4469_, 0, v___x_4482_);
v___x_4484_ = v___x_4469_;
goto v_reusejp_4483_;
}
else
{
lean_object* v_reuseFailAlloc_4485_; 
v_reuseFailAlloc_4485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4485_, 0, v___x_4482_);
v___x_4484_ = v_reuseFailAlloc_4485_;
goto v_reusejp_4483_;
}
v_reusejp_4483_:
{
return v___x_4484_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___boxed(lean_object* v_a_4487_, lean_object* v_x_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_){
_start:
{
lean_object* v_res_4496_; 
v_res_4496_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0(v_a_4487_, v_x_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_);
lean_dec(v___y_4494_);
lean_dec_ref(v___y_4493_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
return v_res_4496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg(lean_object* v_oldTraces_4497_, lean_object* v_data_4498_, lean_object* v_ref_4499_, lean_object* v_msg_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_){
_start:
{
lean_object* v_fileName_4506_; lean_object* v_fileMap_4507_; lean_object* v_options_4508_; lean_object* v_currRecDepth_4509_; lean_object* v_maxRecDepth_4510_; lean_object* v_ref_4511_; lean_object* v_currNamespace_4512_; lean_object* v_openDecls_4513_; lean_object* v_initHeartbeats_4514_; lean_object* v_maxHeartbeats_4515_; lean_object* v_quotContext_4516_; lean_object* v_currMacroScope_4517_; uint8_t v_diag_4518_; lean_object* v_cancelTk_x3f_4519_; uint8_t v_suppressElabErrors_4520_; lean_object* v_inheritedTraceOptions_4521_; lean_object* v___x_4522_; lean_object* v_traceState_4523_; lean_object* v_traces_4524_; lean_object* v_ref_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; size_t v_sz_4528_; size_t v___x_4529_; lean_object* v___x_4530_; lean_object* v_msg_4531_; lean_object* v___x_4532_; lean_object* v_a_4533_; lean_object* v___x_4535_; uint8_t v_isShared_4536_; uint8_t v_isSharedCheck_4570_; 
v_fileName_4506_ = lean_ctor_get(v___y_4503_, 0);
v_fileMap_4507_ = lean_ctor_get(v___y_4503_, 1);
v_options_4508_ = lean_ctor_get(v___y_4503_, 2);
v_currRecDepth_4509_ = lean_ctor_get(v___y_4503_, 3);
v_maxRecDepth_4510_ = lean_ctor_get(v___y_4503_, 4);
v_ref_4511_ = lean_ctor_get(v___y_4503_, 5);
v_currNamespace_4512_ = lean_ctor_get(v___y_4503_, 6);
v_openDecls_4513_ = lean_ctor_get(v___y_4503_, 7);
v_initHeartbeats_4514_ = lean_ctor_get(v___y_4503_, 8);
v_maxHeartbeats_4515_ = lean_ctor_get(v___y_4503_, 9);
v_quotContext_4516_ = lean_ctor_get(v___y_4503_, 10);
v_currMacroScope_4517_ = lean_ctor_get(v___y_4503_, 11);
v_diag_4518_ = lean_ctor_get_uint8(v___y_4503_, sizeof(void*)*14);
v_cancelTk_x3f_4519_ = lean_ctor_get(v___y_4503_, 12);
v_suppressElabErrors_4520_ = lean_ctor_get_uint8(v___y_4503_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4521_ = lean_ctor_get(v___y_4503_, 13);
v___x_4522_ = lean_st_ref_get(v___y_4504_);
v_traceState_4523_ = lean_ctor_get(v___x_4522_, 4);
lean_inc_ref(v_traceState_4523_);
lean_dec(v___x_4522_);
v_traces_4524_ = lean_ctor_get(v_traceState_4523_, 0);
lean_inc_ref(v_traces_4524_);
lean_dec_ref(v_traceState_4523_);
v_ref_4525_ = l_Lean_replaceRef(v_ref_4499_, v_ref_4511_);
lean_inc_ref(v_inheritedTraceOptions_4521_);
lean_inc(v_cancelTk_x3f_4519_);
lean_inc(v_currMacroScope_4517_);
lean_inc(v_quotContext_4516_);
lean_inc(v_maxHeartbeats_4515_);
lean_inc(v_initHeartbeats_4514_);
lean_inc(v_openDecls_4513_);
lean_inc(v_currNamespace_4512_);
lean_inc(v_maxRecDepth_4510_);
lean_inc(v_currRecDepth_4509_);
lean_inc_ref(v_options_4508_);
lean_inc_ref(v_fileMap_4507_);
lean_inc_ref(v_fileName_4506_);
v___x_4526_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4526_, 0, v_fileName_4506_);
lean_ctor_set(v___x_4526_, 1, v_fileMap_4507_);
lean_ctor_set(v___x_4526_, 2, v_options_4508_);
lean_ctor_set(v___x_4526_, 3, v_currRecDepth_4509_);
lean_ctor_set(v___x_4526_, 4, v_maxRecDepth_4510_);
lean_ctor_set(v___x_4526_, 5, v_ref_4525_);
lean_ctor_set(v___x_4526_, 6, v_currNamespace_4512_);
lean_ctor_set(v___x_4526_, 7, v_openDecls_4513_);
lean_ctor_set(v___x_4526_, 8, v_initHeartbeats_4514_);
lean_ctor_set(v___x_4526_, 9, v_maxHeartbeats_4515_);
lean_ctor_set(v___x_4526_, 10, v_quotContext_4516_);
lean_ctor_set(v___x_4526_, 11, v_currMacroScope_4517_);
lean_ctor_set(v___x_4526_, 12, v_cancelTk_x3f_4519_);
lean_ctor_set(v___x_4526_, 13, v_inheritedTraceOptions_4521_);
lean_ctor_set_uint8(v___x_4526_, sizeof(void*)*14, v_diag_4518_);
lean_ctor_set_uint8(v___x_4526_, sizeof(void*)*14 + 1, v_suppressElabErrors_4520_);
v___x_4527_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4524_);
lean_dec_ref(v_traces_4524_);
v_sz_4528_ = lean_array_size(v___x_4527_);
v___x_4529_ = ((size_t)0ULL);
v___x_4530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5(v_sz_4528_, v___x_4529_, v___x_4527_);
v_msg_4531_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4531_, 0, v_data_4498_);
lean_ctor_set(v_msg_4531_, 1, v_msg_4500_);
lean_ctor_set(v_msg_4531_, 2, v___x_4530_);
v___x_4532_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_4531_, v___y_4501_, v___y_4502_, v___x_4526_, v___y_4504_);
lean_dec_ref_known(v___x_4526_, 14);
v_a_4533_ = lean_ctor_get(v___x_4532_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4532_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4535_ = v___x_4532_;
v_isShared_4536_ = v_isSharedCheck_4570_;
goto v_resetjp_4534_;
}
else
{
lean_inc(v_a_4533_);
lean_dec(v___x_4532_);
v___x_4535_ = lean_box(0);
v_isShared_4536_ = v_isSharedCheck_4570_;
goto v_resetjp_4534_;
}
v_resetjp_4534_:
{
lean_object* v___x_4537_; lean_object* v_traceState_4538_; lean_object* v_env_4539_; lean_object* v_nextMacroScope_4540_; lean_object* v_ngen_4541_; lean_object* v_auxDeclNGen_4542_; lean_object* v_cache_4543_; lean_object* v_messages_4544_; lean_object* v_infoState_4545_; lean_object* v_snapshotTasks_4546_; lean_object* v___x_4548_; uint8_t v_isShared_4549_; uint8_t v_isSharedCheck_4569_; 
v___x_4537_ = lean_st_ref_take(v___y_4504_);
v_traceState_4538_ = lean_ctor_get(v___x_4537_, 4);
v_env_4539_ = lean_ctor_get(v___x_4537_, 0);
v_nextMacroScope_4540_ = lean_ctor_get(v___x_4537_, 1);
v_ngen_4541_ = lean_ctor_get(v___x_4537_, 2);
v_auxDeclNGen_4542_ = lean_ctor_get(v___x_4537_, 3);
v_cache_4543_ = lean_ctor_get(v___x_4537_, 5);
v_messages_4544_ = lean_ctor_get(v___x_4537_, 6);
v_infoState_4545_ = lean_ctor_get(v___x_4537_, 7);
v_snapshotTasks_4546_ = lean_ctor_get(v___x_4537_, 8);
v_isSharedCheck_4569_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4569_ == 0)
{
v___x_4548_ = v___x_4537_;
v_isShared_4549_ = v_isSharedCheck_4569_;
goto v_resetjp_4547_;
}
else
{
lean_inc(v_snapshotTasks_4546_);
lean_inc(v_infoState_4545_);
lean_inc(v_messages_4544_);
lean_inc(v_cache_4543_);
lean_inc(v_traceState_4538_);
lean_inc(v_auxDeclNGen_4542_);
lean_inc(v_ngen_4541_);
lean_inc(v_nextMacroScope_4540_);
lean_inc(v_env_4539_);
lean_dec(v___x_4537_);
v___x_4548_ = lean_box(0);
v_isShared_4549_ = v_isSharedCheck_4569_;
goto v_resetjp_4547_;
}
v_resetjp_4547_:
{
uint64_t v_tid_4550_; lean_object* v___x_4552_; uint8_t v_isShared_4553_; uint8_t v_isSharedCheck_4567_; 
v_tid_4550_ = lean_ctor_get_uint64(v_traceState_4538_, sizeof(void*)*1);
v_isSharedCheck_4567_ = !lean_is_exclusive(v_traceState_4538_);
if (v_isSharedCheck_4567_ == 0)
{
lean_object* v_unused_4568_; 
v_unused_4568_ = lean_ctor_get(v_traceState_4538_, 0);
lean_dec(v_unused_4568_);
v___x_4552_ = v_traceState_4538_;
v_isShared_4553_ = v_isSharedCheck_4567_;
goto v_resetjp_4551_;
}
else
{
lean_dec(v_traceState_4538_);
v___x_4552_ = lean_box(0);
v_isShared_4553_ = v_isSharedCheck_4567_;
goto v_resetjp_4551_;
}
v_resetjp_4551_:
{
lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4557_; 
v___x_4554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4554_, 0, v_ref_4499_);
lean_ctor_set(v___x_4554_, 1, v_a_4533_);
v___x_4555_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4497_, v___x_4554_);
if (v_isShared_4553_ == 0)
{
lean_ctor_set(v___x_4552_, 0, v___x_4555_);
v___x_4557_ = v___x_4552_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4566_; 
v_reuseFailAlloc_4566_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4566_, 0, v___x_4555_);
lean_ctor_set_uint64(v_reuseFailAlloc_4566_, sizeof(void*)*1, v_tid_4550_);
v___x_4557_ = v_reuseFailAlloc_4566_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
lean_object* v___x_4559_; 
if (v_isShared_4549_ == 0)
{
lean_ctor_set(v___x_4548_, 4, v___x_4557_);
v___x_4559_ = v___x_4548_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v_env_4539_);
lean_ctor_set(v_reuseFailAlloc_4565_, 1, v_nextMacroScope_4540_);
lean_ctor_set(v_reuseFailAlloc_4565_, 2, v_ngen_4541_);
lean_ctor_set(v_reuseFailAlloc_4565_, 3, v_auxDeclNGen_4542_);
lean_ctor_set(v_reuseFailAlloc_4565_, 4, v___x_4557_);
lean_ctor_set(v_reuseFailAlloc_4565_, 5, v_cache_4543_);
lean_ctor_set(v_reuseFailAlloc_4565_, 6, v_messages_4544_);
lean_ctor_set(v_reuseFailAlloc_4565_, 7, v_infoState_4545_);
lean_ctor_set(v_reuseFailAlloc_4565_, 8, v_snapshotTasks_4546_);
v___x_4559_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4563_; 
v___x_4560_ = lean_st_ref_set(v___y_4504_, v___x_4559_);
v___x_4561_ = lean_box(0);
if (v_isShared_4536_ == 0)
{
lean_ctor_set(v___x_4535_, 0, v___x_4561_);
v___x_4563_ = v___x_4535_;
goto v_reusejp_4562_;
}
else
{
lean_object* v_reuseFailAlloc_4564_; 
v_reuseFailAlloc_4564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4564_, 0, v___x_4561_);
v___x_4563_ = v_reuseFailAlloc_4564_;
goto v_reusejp_4562_;
}
v_reusejp_4562_:
{
return v___x_4563_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg___boxed(lean_object* v_oldTraces_4571_, lean_object* v_data_4572_, lean_object* v_ref_4573_, lean_object* v_msg_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_){
_start:
{
lean_object* v_res_4580_; 
v_res_4580_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg(v_oldTraces_4571_, v_data_4572_, v_ref_4573_, v_msg_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_);
lean_dec(v___y_4578_);
lean_dec_ref(v___y_4577_);
lean_dec(v___y_4576_);
lean_dec_ref(v___y_4575_);
return v_res_4580_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(lean_object* v_x_4581_){
_start:
{
if (lean_obj_tag(v_x_4581_) == 0)
{
lean_object* v_a_4583_; lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4590_; 
v_a_4583_ = lean_ctor_get(v_x_4581_, 0);
v_isSharedCheck_4590_ = !lean_is_exclusive(v_x_4581_);
if (v_isSharedCheck_4590_ == 0)
{
v___x_4585_ = v_x_4581_;
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
else
{
lean_inc(v_a_4583_);
lean_dec(v_x_4581_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4590_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v___x_4588_; 
if (v_isShared_4586_ == 0)
{
lean_ctor_set_tag(v___x_4585_, 1);
v___x_4588_ = v___x_4585_;
goto v_reusejp_4587_;
}
else
{
lean_object* v_reuseFailAlloc_4589_; 
v_reuseFailAlloc_4589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4589_, 0, v_a_4583_);
v___x_4588_ = v_reuseFailAlloc_4589_;
goto v_reusejp_4587_;
}
v_reusejp_4587_:
{
return v___x_4588_;
}
}
}
else
{
lean_object* v_a_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4598_; 
v_a_4591_ = lean_ctor_get(v_x_4581_, 0);
v_isSharedCheck_4598_ = !lean_is_exclusive(v_x_4581_);
if (v_isSharedCheck_4598_ == 0)
{
v___x_4593_ = v_x_4581_;
v_isShared_4594_ = v_isSharedCheck_4598_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_a_4591_);
lean_dec(v_x_4581_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4598_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
lean_object* v___x_4596_; 
if (v_isShared_4594_ == 0)
{
lean_ctor_set_tag(v___x_4593_, 0);
v___x_4596_ = v___x_4593_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4597_; 
v_reuseFailAlloc_4597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4597_, 0, v_a_4591_);
v___x_4596_ = v_reuseFailAlloc_4597_;
goto v_reusejp_4595_;
}
v_reusejp_4595_:
{
return v___x_4596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg___boxed(lean_object* v_x_4599_, lean_object* v___y_4600_){
_start:
{
lean_object* v_res_4601_; 
v_res_4601_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(v_x_4599_);
return v_res_4601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(lean_object* v_cls_4602_, uint8_t v_collapsed_4603_, lean_object* v_tag_4604_, lean_object* v_opts_4605_, uint8_t v_clsEnabled_4606_, lean_object* v_oldTraces_4607_, lean_object* v_msg_4608_, lean_object* v_resStartStop_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_){
_start:
{
lean_object* v_fst_4617_; lean_object* v_snd_4618_; lean_object* v___y_4620_; lean_object* v___y_4621_; lean_object* v_data_4622_; lean_object* v_fst_4633_; lean_object* v_snd_4634_; lean_object* v___x_4635_; uint8_t v___x_4636_; lean_object* v___y_4638_; lean_object* v_a_4639_; uint8_t v___y_4654_; double v___y_4685_; 
v_fst_4617_ = lean_ctor_get(v_resStartStop_4609_, 0);
lean_inc(v_fst_4617_);
v_snd_4618_ = lean_ctor_get(v_resStartStop_4609_, 1);
lean_inc(v_snd_4618_);
lean_dec_ref(v_resStartStop_4609_);
v_fst_4633_ = lean_ctor_get(v_snd_4618_, 0);
lean_inc(v_fst_4633_);
v_snd_4634_ = lean_ctor_get(v_snd_4618_, 1);
lean_inc(v_snd_4634_);
lean_dec(v_snd_4618_);
v___x_4635_ = l_Lean_trace_profiler;
v___x_4636_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4605_, v___x_4635_);
if (v___x_4636_ == 0)
{
v___y_4654_ = v___x_4636_;
goto v___jp_4653_;
}
else
{
lean_object* v___x_4690_; uint8_t v___x_4691_; 
v___x_4690_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4691_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4605_, v___x_4690_);
if (v___x_4691_ == 0)
{
lean_object* v___x_4692_; lean_object* v___x_4693_; double v___x_4694_; double v___x_4695_; double v___x_4696_; 
v___x_4692_ = l_Lean_trace_profiler_threshold;
v___x_4693_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4605_, v___x_4692_);
v___x_4694_ = lean_float_of_nat(v___x_4693_);
v___x_4695_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2);
v___x_4696_ = lean_float_div(v___x_4694_, v___x_4695_);
v___y_4685_ = v___x_4696_;
goto v___jp_4684_;
}
else
{
lean_object* v___x_4697_; lean_object* v___x_4698_; double v___x_4699_; 
v___x_4697_ = l_Lean_trace_profiler_threshold;
v___x_4698_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4605_, v___x_4697_);
v___x_4699_ = lean_float_of_nat(v___x_4698_);
v___y_4685_ = v___x_4699_;
goto v___jp_4684_;
}
}
v___jp_4619_:
{
lean_object* v___x_4623_; 
lean_inc(v___y_4620_);
v___x_4623_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg(v_oldTraces_4607_, v_data_4622_, v___y_4620_, v___y_4621_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_);
if (lean_obj_tag(v___x_4623_) == 0)
{
lean_object* v___x_4624_; 
lean_dec_ref_known(v___x_4623_, 1);
v___x_4624_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(v_fst_4617_);
return v___x_4624_;
}
else
{
lean_object* v_a_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4632_; 
lean_dec(v_fst_4617_);
v_a_4625_ = lean_ctor_get(v___x_4623_, 0);
v_isSharedCheck_4632_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4632_ == 0)
{
v___x_4627_ = v___x_4623_;
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_a_4625_);
lean_dec(v___x_4623_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v___x_4630_; 
if (v_isShared_4628_ == 0)
{
v___x_4630_ = v___x_4627_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4631_; 
v_reuseFailAlloc_4631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4631_, 0, v_a_4625_);
v___x_4630_ = v_reuseFailAlloc_4631_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
return v___x_4630_;
}
}
}
}
v___jp_4637_:
{
uint8_t v_result_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; double v___x_4643_; lean_object* v_data_4644_; 
v_result_4640_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(v_fst_4617_);
v___x_4641_ = lean_box(v_result_4640_);
v___x_4642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4642_, 0, v___x_4641_);
v___x_4643_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_4604_);
lean_inc_ref(v___x_4642_);
lean_inc(v_cls_4602_);
v_data_4644_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4644_, 0, v_cls_4602_);
lean_ctor_set(v_data_4644_, 1, v___x_4642_);
lean_ctor_set(v_data_4644_, 2, v_tag_4604_);
lean_ctor_set_float(v_data_4644_, sizeof(void*)*3, v___x_4643_);
lean_ctor_set_float(v_data_4644_, sizeof(void*)*3 + 8, v___x_4643_);
lean_ctor_set_uint8(v_data_4644_, sizeof(void*)*3 + 16, v_collapsed_4603_);
if (v___x_4636_ == 0)
{
lean_dec_ref_known(v___x_4642_, 1);
lean_dec(v_snd_4634_);
lean_dec(v_fst_4633_);
lean_dec_ref(v_tag_4604_);
lean_dec(v_cls_4602_);
v___y_4620_ = v___y_4638_;
v___y_4621_ = v_a_4639_;
v_data_4622_ = v_data_4644_;
goto v___jp_4619_;
}
else
{
lean_object* v_data_4645_; double v___x_4646_; double v___x_4647_; 
lean_dec_ref_known(v_data_4644_, 3);
v_data_4645_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4645_, 0, v_cls_4602_);
lean_ctor_set(v_data_4645_, 1, v___x_4642_);
lean_ctor_set(v_data_4645_, 2, v_tag_4604_);
v___x_4646_ = lean_unbox_float(v_fst_4633_);
lean_dec(v_fst_4633_);
lean_ctor_set_float(v_data_4645_, sizeof(void*)*3, v___x_4646_);
v___x_4647_ = lean_unbox_float(v_snd_4634_);
lean_dec(v_snd_4634_);
lean_ctor_set_float(v_data_4645_, sizeof(void*)*3 + 8, v___x_4647_);
lean_ctor_set_uint8(v_data_4645_, sizeof(void*)*3 + 16, v_collapsed_4603_);
v___y_4620_ = v___y_4638_;
v___y_4621_ = v_a_4639_;
v_data_4622_ = v_data_4645_;
goto v___jp_4619_;
}
}
v___jp_4648_:
{
lean_object* v_ref_4649_; lean_object* v___x_4650_; 
v_ref_4649_ = lean_ctor_get(v___y_4614_, 5);
lean_inc(v___y_4615_);
lean_inc_ref(v___y_4614_);
lean_inc(v___y_4613_);
lean_inc_ref(v___y_4612_);
lean_inc(v___y_4611_);
lean_inc_ref(v___y_4610_);
lean_inc(v_fst_4617_);
v___x_4650_ = lean_apply_8(v_msg_4608_, v_fst_4617_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_, lean_box(0));
if (lean_obj_tag(v___x_4650_) == 0)
{
lean_object* v_a_4651_; 
v_a_4651_ = lean_ctor_get(v___x_4650_, 0);
lean_inc(v_a_4651_);
lean_dec_ref_known(v___x_4650_, 1);
v___y_4638_ = v_ref_4649_;
v_a_4639_ = v_a_4651_;
goto v___jp_4637_;
}
else
{
lean_object* v___x_4652_; 
lean_dec_ref_known(v___x_4650_, 1);
v___x_4652_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
v___y_4638_ = v_ref_4649_;
v_a_4639_ = v___x_4652_;
goto v___jp_4637_;
}
}
v___jp_4653_:
{
if (v_clsEnabled_4606_ == 0)
{
if (v___y_4654_ == 0)
{
lean_object* v___x_4655_; lean_object* v_traceState_4656_; lean_object* v_env_4657_; lean_object* v_nextMacroScope_4658_; lean_object* v_ngen_4659_; lean_object* v_auxDeclNGen_4660_; lean_object* v_cache_4661_; lean_object* v_messages_4662_; lean_object* v_infoState_4663_; lean_object* v_snapshotTasks_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4683_; 
lean_dec(v_snd_4634_);
lean_dec(v_fst_4633_);
lean_dec_ref(v_msg_4608_);
lean_dec_ref(v_tag_4604_);
lean_dec(v_cls_4602_);
v___x_4655_ = lean_st_ref_take(v___y_4615_);
v_traceState_4656_ = lean_ctor_get(v___x_4655_, 4);
v_env_4657_ = lean_ctor_get(v___x_4655_, 0);
v_nextMacroScope_4658_ = lean_ctor_get(v___x_4655_, 1);
v_ngen_4659_ = lean_ctor_get(v___x_4655_, 2);
v_auxDeclNGen_4660_ = lean_ctor_get(v___x_4655_, 3);
v_cache_4661_ = lean_ctor_get(v___x_4655_, 5);
v_messages_4662_ = lean_ctor_get(v___x_4655_, 6);
v_infoState_4663_ = lean_ctor_get(v___x_4655_, 7);
v_snapshotTasks_4664_ = lean_ctor_get(v___x_4655_, 8);
v_isSharedCheck_4683_ = !lean_is_exclusive(v___x_4655_);
if (v_isSharedCheck_4683_ == 0)
{
v___x_4666_ = v___x_4655_;
v_isShared_4667_ = v_isSharedCheck_4683_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_snapshotTasks_4664_);
lean_inc(v_infoState_4663_);
lean_inc(v_messages_4662_);
lean_inc(v_cache_4661_);
lean_inc(v_traceState_4656_);
lean_inc(v_auxDeclNGen_4660_);
lean_inc(v_ngen_4659_);
lean_inc(v_nextMacroScope_4658_);
lean_inc(v_env_4657_);
lean_dec(v___x_4655_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4683_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
uint64_t v_tid_4668_; lean_object* v_traces_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4682_; 
v_tid_4668_ = lean_ctor_get_uint64(v_traceState_4656_, sizeof(void*)*1);
v_traces_4669_ = lean_ctor_get(v_traceState_4656_, 0);
v_isSharedCheck_4682_ = !lean_is_exclusive(v_traceState_4656_);
if (v_isSharedCheck_4682_ == 0)
{
v___x_4671_ = v_traceState_4656_;
v_isShared_4672_ = v_isSharedCheck_4682_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_traces_4669_);
lean_dec(v_traceState_4656_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4682_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v___x_4673_; lean_object* v___x_4675_; 
v___x_4673_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4607_, v_traces_4669_);
lean_dec_ref(v_traces_4669_);
if (v_isShared_4672_ == 0)
{
lean_ctor_set(v___x_4671_, 0, v___x_4673_);
v___x_4675_ = v___x_4671_;
goto v_reusejp_4674_;
}
else
{
lean_object* v_reuseFailAlloc_4681_; 
v_reuseFailAlloc_4681_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4681_, 0, v___x_4673_);
lean_ctor_set_uint64(v_reuseFailAlloc_4681_, sizeof(void*)*1, v_tid_4668_);
v___x_4675_ = v_reuseFailAlloc_4681_;
goto v_reusejp_4674_;
}
v_reusejp_4674_:
{
lean_object* v___x_4677_; 
if (v_isShared_4667_ == 0)
{
lean_ctor_set(v___x_4666_, 4, v___x_4675_);
v___x_4677_ = v___x_4666_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4680_; 
v_reuseFailAlloc_4680_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4680_, 0, v_env_4657_);
lean_ctor_set(v_reuseFailAlloc_4680_, 1, v_nextMacroScope_4658_);
lean_ctor_set(v_reuseFailAlloc_4680_, 2, v_ngen_4659_);
lean_ctor_set(v_reuseFailAlloc_4680_, 3, v_auxDeclNGen_4660_);
lean_ctor_set(v_reuseFailAlloc_4680_, 4, v___x_4675_);
lean_ctor_set(v_reuseFailAlloc_4680_, 5, v_cache_4661_);
lean_ctor_set(v_reuseFailAlloc_4680_, 6, v_messages_4662_);
lean_ctor_set(v_reuseFailAlloc_4680_, 7, v_infoState_4663_);
lean_ctor_set(v_reuseFailAlloc_4680_, 8, v_snapshotTasks_4664_);
v___x_4677_ = v_reuseFailAlloc_4680_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
lean_object* v___x_4678_; lean_object* v___x_4679_; 
v___x_4678_ = lean_st_ref_set(v___y_4615_, v___x_4677_);
v___x_4679_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(v_fst_4617_);
return v___x_4679_;
}
}
}
}
}
else
{
goto v___jp_4648_;
}
}
else
{
goto v___jp_4648_;
}
}
v___jp_4684_:
{
double v___x_4686_; double v___x_4687_; double v___x_4688_; uint8_t v___x_4689_; 
v___x_4686_ = lean_unbox_float(v_snd_4634_);
v___x_4687_ = lean_unbox_float(v_fst_4633_);
v___x_4688_ = lean_float_sub(v___x_4686_, v___x_4687_);
v___x_4689_ = lean_float_decLt(v___y_4685_, v___x_4688_);
v___y_4654_ = v___x_4689_;
goto v___jp_4653_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2___boxed(lean_object* v_cls_4700_, lean_object* v_collapsed_4701_, lean_object* v_tag_4702_, lean_object* v_opts_4703_, lean_object* v_clsEnabled_4704_, lean_object* v_oldTraces_4705_, lean_object* v_msg_4706_, lean_object* v_resStartStop_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_, lean_object* v___y_4714_){
_start:
{
uint8_t v_collapsed_boxed_4715_; uint8_t v_clsEnabled_boxed_4716_; lean_object* v_res_4717_; 
v_collapsed_boxed_4715_ = lean_unbox(v_collapsed_4701_);
v_clsEnabled_boxed_4716_ = lean_unbox(v_clsEnabled_4704_);
v_res_4717_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v_cls_4700_, v_collapsed_boxed_4715_, v_tag_4702_, v_opts_4703_, v_clsEnabled_boxed_4716_, v_oldTraces_4705_, v_msg_4706_, v_resStartStop_4707_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_);
lean_dec(v___y_4713_);
lean_dec_ref(v___y_4712_);
lean_dec(v___y_4711_);
lean_dec_ref(v___y_4710_);
lean_dec(v___y_4709_);
lean_dec_ref(v___y_4708_);
lean_dec_ref(v_opts_4703_);
return v_res_4717_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4719_; lean_object* v___x_4720_; 
v___x_4719_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__0));
v___x_4720_ = l_Lean_stringToMessageData(v___x_4719_);
return v___x_4720_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4722_; lean_object* v___x_4723_; 
v___x_4722_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__2));
v___x_4723_ = l_Lean_stringToMessageData(v___x_4722_);
return v___x_4723_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4725_; lean_object* v___x_4726_; 
v___x_4725_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__4));
v___x_4726_ = l_Lean_stringToMessageData(v___x_4725_);
return v___x_4726_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0(lean_object* v_a_4727_, lean_object* v___x_4728_, lean_object* v_x_4729_, lean_object* v___y_4730_, lean_object* v___y_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_){
_start:
{
if (lean_obj_tag(v_x_4729_) == 0)
{
lean_object* v_a_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4752_; 
lean_dec_ref(v___x_4728_);
v_a_4737_ = lean_ctor_get(v_x_4729_, 0);
v_isSharedCheck_4752_ = !lean_is_exclusive(v_x_4729_);
if (v_isSharedCheck_4752_ == 0)
{
v___x_4739_ = v_x_4729_;
v_isShared_4740_ = v_isSharedCheck_4752_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_a_4737_);
lean_dec(v_x_4729_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4752_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4750_; 
v___x_4741_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1);
v___x_4742_ = l_Lean_LocalDecl_userName(v_a_4727_);
v___x_4743_ = l_Lean_MessageData_ofName(v___x_4742_);
v___x_4744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4744_, 0, v___x_4741_);
lean_ctor_set(v___x_4744_, 1, v___x_4743_);
v___x_4745_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3);
v___x_4746_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4746_, 0, v___x_4744_);
lean_ctor_set(v___x_4746_, 1, v___x_4745_);
v___x_4747_ = l_Lean_Exception_toMessageData(v_a_4737_);
v___x_4748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4748_, 0, v___x_4746_);
lean_ctor_set(v___x_4748_, 1, v___x_4747_);
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 0, v___x_4748_);
v___x_4750_ = v___x_4739_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v___x_4748_);
v___x_4750_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
return v___x_4750_;
}
}
}
else
{
lean_object* v_a_4753_; lean_object* v___x_4755_; uint8_t v_isShared_4756_; uint8_t v_isSharedCheck_4782_; 
v_a_4753_ = lean_ctor_get(v_x_4729_, 0);
v_isSharedCheck_4782_ = !lean_is_exclusive(v_x_4729_);
if (v_isSharedCheck_4782_ == 0)
{
v___x_4755_ = v_x_4729_;
v_isShared_4756_ = v_isSharedCheck_4782_;
goto v_resetjp_4754_;
}
else
{
lean_inc(v_a_4753_);
lean_dec(v_x_4729_);
v___x_4755_ = lean_box(0);
v_isShared_4756_ = v_isSharedCheck_4782_;
goto v_resetjp_4754_;
}
v_resetjp_4754_:
{
if (lean_obj_tag(v_a_4753_) == 0)
{
lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4764_; 
lean_dec_ref_known(v_a_4753_, 0);
lean_dec_ref(v___x_4728_);
v___x_4757_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1);
v___x_4758_ = l_Lean_LocalDecl_userName(v_a_4727_);
v___x_4759_ = l_Lean_MessageData_ofName(v___x_4758_);
v___x_4760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4760_, 0, v___x_4757_);
lean_ctor_set(v___x_4760_, 1, v___x_4759_);
v___x_4761_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5);
v___x_4762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4762_, 0, v___x_4760_);
lean_ctor_set(v___x_4762_, 1, v___x_4761_);
if (v_isShared_4756_ == 0)
{
lean_ctor_set_tag(v___x_4755_, 0);
lean_ctor_set(v___x_4755_, 0, v___x_4762_);
v___x_4764_ = v___x_4755_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v___x_4762_);
v___x_4764_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
return v___x_4764_;
}
}
else
{
lean_object* v_e_x27_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4780_; 
v_e_x27_4766_ = lean_ctor_get(v_a_4753_, 0);
lean_inc_ref(v_e_x27_4766_);
lean_dec_ref_known(v_a_4753_, 2);
v___x_4767_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1);
v___x_4768_ = l_Lean_LocalDecl_userName(v_a_4727_);
v___x_4769_ = l_Lean_MessageData_ofName(v___x_4768_);
v___x_4770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4770_, 0, v___x_4767_);
lean_ctor_set(v___x_4770_, 1, v___x_4769_);
v___x_4771_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8);
v___x_4772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4772_, 0, v___x_4770_);
lean_ctor_set(v___x_4772_, 1, v___x_4771_);
v___x_4773_ = l_Lean_indentExpr(v___x_4728_);
v___x_4774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4774_, 0, v___x_4772_);
lean_ctor_set(v___x_4774_, 1, v___x_4773_);
v___x_4775_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_4776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4776_, 0, v___x_4774_);
lean_ctor_set(v___x_4776_, 1, v___x_4775_);
v___x_4777_ = l_Lean_indentExpr(v_e_x27_4766_);
v___x_4778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4778_, 0, v___x_4776_);
lean_ctor_set(v___x_4778_, 1, v___x_4777_);
if (v_isShared_4756_ == 0)
{
lean_ctor_set_tag(v___x_4755_, 0);
lean_ctor_set(v___x_4755_, 0, v___x_4778_);
v___x_4780_ = v___x_4755_;
goto v_reusejp_4779_;
}
else
{
lean_object* v_reuseFailAlloc_4781_; 
v_reuseFailAlloc_4781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4781_, 0, v___x_4778_);
v___x_4780_ = v_reuseFailAlloc_4781_;
goto v_reusejp_4779_;
}
v_reusejp_4779_:
{
return v___x_4780_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___boxed(lean_object* v_a_4783_, lean_object* v___x_4784_, lean_object* v_x_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_){
_start:
{
lean_object* v_res_4793_; 
v_res_4793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0(v_a_4783_, v___x_4784_, v_x_4785_, v___y_4786_, v___y_4787_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_);
lean_dec(v___y_4791_);
lean_dec_ref(v___y_4790_);
lean_dec(v___y_4789_);
lean_dec_ref(v___y_4788_);
lean_dec(v___y_4787_);
lean_dec_ref(v___y_4786_);
lean_dec_ref(v_a_4783_);
return v_res_4793_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(lean_object* v_x_4794_, lean_object* v_x_4795_, lean_object* v_x_4796_, lean_object* v_x_4797_){
_start:
{
lean_object* v_ks_4798_; lean_object* v_vs_4799_; lean_object* v___x_4801_; uint8_t v_isShared_4802_; uint8_t v_isSharedCheck_4823_; 
v_ks_4798_ = lean_ctor_get(v_x_4794_, 0);
v_vs_4799_ = lean_ctor_get(v_x_4794_, 1);
v_isSharedCheck_4823_ = !lean_is_exclusive(v_x_4794_);
if (v_isSharedCheck_4823_ == 0)
{
v___x_4801_ = v_x_4794_;
v_isShared_4802_ = v_isSharedCheck_4823_;
goto v_resetjp_4800_;
}
else
{
lean_inc(v_vs_4799_);
lean_inc(v_ks_4798_);
lean_dec(v_x_4794_);
v___x_4801_ = lean_box(0);
v_isShared_4802_ = v_isSharedCheck_4823_;
goto v_resetjp_4800_;
}
v_resetjp_4800_:
{
lean_object* v___x_4803_; uint8_t v___x_4804_; 
v___x_4803_ = lean_array_get_size(v_ks_4798_);
v___x_4804_ = lean_nat_dec_lt(v_x_4795_, v___x_4803_);
if (v___x_4804_ == 0)
{
lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4808_; 
lean_dec(v_x_4795_);
v___x_4805_ = lean_array_push(v_ks_4798_, v_x_4796_);
v___x_4806_ = lean_array_push(v_vs_4799_, v_x_4797_);
if (v_isShared_4802_ == 0)
{
lean_ctor_set(v___x_4801_, 1, v___x_4806_);
lean_ctor_set(v___x_4801_, 0, v___x_4805_);
v___x_4808_ = v___x_4801_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4809_; 
v_reuseFailAlloc_4809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4809_, 0, v___x_4805_);
lean_ctor_set(v_reuseFailAlloc_4809_, 1, v___x_4806_);
v___x_4808_ = v_reuseFailAlloc_4809_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
return v___x_4808_;
}
}
else
{
lean_object* v_k_x27_4810_; uint8_t v___x_4811_; 
v_k_x27_4810_ = lean_array_fget_borrowed(v_ks_4798_, v_x_4795_);
v___x_4811_ = l_Lean_instBEqMVarId_beq(v_x_4796_, v_k_x27_4810_);
if (v___x_4811_ == 0)
{
lean_object* v___x_4813_; 
if (v_isShared_4802_ == 0)
{
v___x_4813_ = v___x_4801_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4817_; 
v_reuseFailAlloc_4817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4817_, 0, v_ks_4798_);
lean_ctor_set(v_reuseFailAlloc_4817_, 1, v_vs_4799_);
v___x_4813_ = v_reuseFailAlloc_4817_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
lean_object* v___x_4814_; lean_object* v___x_4815_; 
v___x_4814_ = lean_unsigned_to_nat(1u);
v___x_4815_ = lean_nat_add(v_x_4795_, v___x_4814_);
lean_dec(v_x_4795_);
v_x_4794_ = v___x_4813_;
v_x_4795_ = v___x_4815_;
goto _start;
}
}
else
{
lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4821_; 
v___x_4818_ = lean_array_fset(v_ks_4798_, v_x_4795_, v_x_4796_);
v___x_4819_ = lean_array_fset(v_vs_4799_, v_x_4795_, v_x_4797_);
lean_dec(v_x_4795_);
if (v_isShared_4802_ == 0)
{
lean_ctor_set(v___x_4801_, 1, v___x_4819_);
lean_ctor_set(v___x_4801_, 0, v___x_4818_);
v___x_4821_ = v___x_4801_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v___x_4818_);
lean_ctor_set(v_reuseFailAlloc_4822_, 1, v___x_4819_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_n_4824_, lean_object* v_k_4825_, lean_object* v_v_4826_){
_start:
{
lean_object* v___x_4827_; lean_object* v___x_4828_; 
v___x_4827_ = lean_unsigned_to_nat(0u);
v___x_4828_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_n_4824_, v___x_4827_, v_k_4825_, v_v_4826_);
return v___x_4828_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_4829_; 
v___x_4829_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4829_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(lean_object* v_x_4830_, size_t v_x_4831_, size_t v_x_4832_, lean_object* v_x_4833_, lean_object* v_x_4834_){
_start:
{
if (lean_obj_tag(v_x_4830_) == 0)
{
lean_object* v_es_4835_; size_t v___x_4836_; size_t v___x_4837_; lean_object* v_j_4838_; lean_object* v___x_4839_; uint8_t v___x_4840_; 
v_es_4835_ = lean_ctor_get(v_x_4830_, 0);
v___x_4836_ = ((size_t)31ULL);
v___x_4837_ = lean_usize_land(v_x_4831_, v___x_4836_);
v_j_4838_ = lean_usize_to_nat(v___x_4837_);
v___x_4839_ = lean_array_get_size(v_es_4835_);
v___x_4840_ = lean_nat_dec_lt(v_j_4838_, v___x_4839_);
if (v___x_4840_ == 0)
{
lean_dec(v_j_4838_);
lean_dec(v_x_4834_);
lean_dec(v_x_4833_);
return v_x_4830_;
}
else
{
lean_object* v___x_4842_; uint8_t v_isShared_4843_; uint8_t v_isSharedCheck_4879_; 
lean_inc_ref(v_es_4835_);
v_isSharedCheck_4879_ = !lean_is_exclusive(v_x_4830_);
if (v_isSharedCheck_4879_ == 0)
{
lean_object* v_unused_4880_; 
v_unused_4880_ = lean_ctor_get(v_x_4830_, 0);
lean_dec(v_unused_4880_);
v___x_4842_ = v_x_4830_;
v_isShared_4843_ = v_isSharedCheck_4879_;
goto v_resetjp_4841_;
}
else
{
lean_dec(v_x_4830_);
v___x_4842_ = lean_box(0);
v_isShared_4843_ = v_isSharedCheck_4879_;
goto v_resetjp_4841_;
}
v_resetjp_4841_:
{
lean_object* v_v_4844_; lean_object* v___x_4845_; lean_object* v_xs_x27_4846_; lean_object* v___y_4848_; 
v_v_4844_ = lean_array_fget(v_es_4835_, v_j_4838_);
v___x_4845_ = lean_box(0);
v_xs_x27_4846_ = lean_array_fset(v_es_4835_, v_j_4838_, v___x_4845_);
switch(lean_obj_tag(v_v_4844_))
{
case 0:
{
lean_object* v_key_4853_; lean_object* v_val_4854_; lean_object* v___x_4856_; uint8_t v_isShared_4857_; uint8_t v_isSharedCheck_4864_; 
v_key_4853_ = lean_ctor_get(v_v_4844_, 0);
v_val_4854_ = lean_ctor_get(v_v_4844_, 1);
v_isSharedCheck_4864_ = !lean_is_exclusive(v_v_4844_);
if (v_isSharedCheck_4864_ == 0)
{
v___x_4856_ = v_v_4844_;
v_isShared_4857_ = v_isSharedCheck_4864_;
goto v_resetjp_4855_;
}
else
{
lean_inc(v_val_4854_);
lean_inc(v_key_4853_);
lean_dec(v_v_4844_);
v___x_4856_ = lean_box(0);
v_isShared_4857_ = v_isSharedCheck_4864_;
goto v_resetjp_4855_;
}
v_resetjp_4855_:
{
uint8_t v___x_4858_; 
v___x_4858_ = l_Lean_instBEqMVarId_beq(v_x_4833_, v_key_4853_);
if (v___x_4858_ == 0)
{
lean_object* v___x_4859_; lean_object* v___x_4860_; 
lean_del_object(v___x_4856_);
v___x_4859_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4853_, v_val_4854_, v_x_4833_, v_x_4834_);
v___x_4860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4860_, 0, v___x_4859_);
v___y_4848_ = v___x_4860_;
goto v___jp_4847_;
}
else
{
lean_object* v___x_4862_; 
lean_dec(v_val_4854_);
lean_dec(v_key_4853_);
if (v_isShared_4857_ == 0)
{
lean_ctor_set(v___x_4856_, 1, v_x_4834_);
lean_ctor_set(v___x_4856_, 0, v_x_4833_);
v___x_4862_ = v___x_4856_;
goto v_reusejp_4861_;
}
else
{
lean_object* v_reuseFailAlloc_4863_; 
v_reuseFailAlloc_4863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4863_, 0, v_x_4833_);
lean_ctor_set(v_reuseFailAlloc_4863_, 1, v_x_4834_);
v___x_4862_ = v_reuseFailAlloc_4863_;
goto v_reusejp_4861_;
}
v_reusejp_4861_:
{
v___y_4848_ = v___x_4862_;
goto v___jp_4847_;
}
}
}
}
case 1:
{
lean_object* v_node_4865_; lean_object* v___x_4867_; uint8_t v_isShared_4868_; uint8_t v_isSharedCheck_4877_; 
v_node_4865_ = lean_ctor_get(v_v_4844_, 0);
v_isSharedCheck_4877_ = !lean_is_exclusive(v_v_4844_);
if (v_isSharedCheck_4877_ == 0)
{
v___x_4867_ = v_v_4844_;
v_isShared_4868_ = v_isSharedCheck_4877_;
goto v_resetjp_4866_;
}
else
{
lean_inc(v_node_4865_);
lean_dec(v_v_4844_);
v___x_4867_ = lean_box(0);
v_isShared_4868_ = v_isSharedCheck_4877_;
goto v_resetjp_4866_;
}
v_resetjp_4866_:
{
size_t v___x_4869_; size_t v___x_4870_; size_t v___x_4871_; size_t v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4875_; 
v___x_4869_ = ((size_t)5ULL);
v___x_4870_ = lean_usize_shift_right(v_x_4831_, v___x_4869_);
v___x_4871_ = ((size_t)1ULL);
v___x_4872_ = lean_usize_add(v_x_4832_, v___x_4871_);
v___x_4873_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_node_4865_, v___x_4870_, v___x_4872_, v_x_4833_, v_x_4834_);
if (v_isShared_4868_ == 0)
{
lean_ctor_set(v___x_4867_, 0, v___x_4873_);
v___x_4875_ = v___x_4867_;
goto v_reusejp_4874_;
}
else
{
lean_object* v_reuseFailAlloc_4876_; 
v_reuseFailAlloc_4876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4876_, 0, v___x_4873_);
v___x_4875_ = v_reuseFailAlloc_4876_;
goto v_reusejp_4874_;
}
v_reusejp_4874_:
{
v___y_4848_ = v___x_4875_;
goto v___jp_4847_;
}
}
}
default: 
{
lean_object* v___x_4878_; 
v___x_4878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4878_, 0, v_x_4833_);
lean_ctor_set(v___x_4878_, 1, v_x_4834_);
v___y_4848_ = v___x_4878_;
goto v___jp_4847_;
}
}
v___jp_4847_:
{
lean_object* v___x_4849_; lean_object* v___x_4851_; 
v___x_4849_ = lean_array_fset(v_xs_x27_4846_, v_j_4838_, v___y_4848_);
lean_dec(v_j_4838_);
if (v_isShared_4843_ == 0)
{
lean_ctor_set(v___x_4842_, 0, v___x_4849_);
v___x_4851_ = v___x_4842_;
goto v_reusejp_4850_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v___x_4849_);
v___x_4851_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4850_;
}
v_reusejp_4850_:
{
return v___x_4851_;
}
}
}
}
}
else
{
lean_object* v_ks_4881_; lean_object* v_vs_4882_; lean_object* v___x_4884_; uint8_t v_isShared_4885_; uint8_t v_isSharedCheck_4902_; 
v_ks_4881_ = lean_ctor_get(v_x_4830_, 0);
v_vs_4882_ = lean_ctor_get(v_x_4830_, 1);
v_isSharedCheck_4902_ = !lean_is_exclusive(v_x_4830_);
if (v_isSharedCheck_4902_ == 0)
{
v___x_4884_ = v_x_4830_;
v_isShared_4885_ = v_isSharedCheck_4902_;
goto v_resetjp_4883_;
}
else
{
lean_inc(v_vs_4882_);
lean_inc(v_ks_4881_);
lean_dec(v_x_4830_);
v___x_4884_ = lean_box(0);
v_isShared_4885_ = v_isSharedCheck_4902_;
goto v_resetjp_4883_;
}
v_resetjp_4883_:
{
lean_object* v___x_4887_; 
if (v_isShared_4885_ == 0)
{
v___x_4887_ = v___x_4884_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v_ks_4881_);
lean_ctor_set(v_reuseFailAlloc_4901_, 1, v_vs_4882_);
v___x_4887_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
lean_object* v_newNode_4888_; uint8_t v___y_4890_; size_t v___x_4896_; uint8_t v___x_4897_; 
v_newNode_4888_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7___redArg(v___x_4887_, v_x_4833_, v_x_4834_);
v___x_4896_ = ((size_t)7ULL);
v___x_4897_ = lean_usize_dec_le(v___x_4896_, v_x_4832_);
if (v___x_4897_ == 0)
{
lean_object* v___x_4898_; lean_object* v___x_4899_; uint8_t v___x_4900_; 
v___x_4898_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4888_);
v___x_4899_ = lean_unsigned_to_nat(4u);
v___x_4900_ = lean_nat_dec_lt(v___x_4898_, v___x_4899_);
lean_dec(v___x_4898_);
v___y_4890_ = v___x_4900_;
goto v___jp_4889_;
}
else
{
v___y_4890_ = v___x_4897_;
goto v___jp_4889_;
}
v___jp_4889_:
{
if (v___y_4890_ == 0)
{
lean_object* v_ks_4891_; lean_object* v_vs_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; 
v_ks_4891_ = lean_ctor_get(v_newNode_4888_, 0);
lean_inc_ref(v_ks_4891_);
v_vs_4892_ = lean_ctor_get(v_newNode_4888_, 1);
lean_inc_ref(v_vs_4892_);
lean_dec_ref(v_newNode_4888_);
v___x_4893_ = lean_unsigned_to_nat(0u);
v___x_4894_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_4895_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg(v_x_4832_, v_ks_4891_, v_vs_4892_, v___x_4893_, v___x_4894_);
lean_dec_ref(v_vs_4892_);
lean_dec_ref(v_ks_4891_);
return v___x_4895_;
}
else
{
return v_newNode_4888_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg(size_t v_depth_4903_, lean_object* v_keys_4904_, lean_object* v_vals_4905_, lean_object* v_i_4906_, lean_object* v_entries_4907_){
_start:
{
lean_object* v___x_4908_; uint8_t v___x_4909_; 
v___x_4908_ = lean_array_get_size(v_keys_4904_);
v___x_4909_ = lean_nat_dec_lt(v_i_4906_, v___x_4908_);
if (v___x_4909_ == 0)
{
lean_dec(v_i_4906_);
return v_entries_4907_;
}
else
{
lean_object* v_k_4910_; lean_object* v_v_4911_; uint64_t v___x_4912_; size_t v_h_4913_; size_t v___x_4914_; lean_object* v___x_4915_; size_t v___x_4916_; size_t v___x_4917_; size_t v___x_4918_; size_t v_h_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; 
v_k_4910_ = lean_array_fget_borrowed(v_keys_4904_, v_i_4906_);
v_v_4911_ = lean_array_fget_borrowed(v_vals_4905_, v_i_4906_);
v___x_4912_ = l_Lean_instHashableMVarId_hash(v_k_4910_);
v_h_4913_ = lean_uint64_to_usize(v___x_4912_);
v___x_4914_ = ((size_t)5ULL);
v___x_4915_ = lean_unsigned_to_nat(1u);
v___x_4916_ = ((size_t)1ULL);
v___x_4917_ = lean_usize_sub(v_depth_4903_, v___x_4916_);
v___x_4918_ = lean_usize_mul(v___x_4914_, v___x_4917_);
v_h_4919_ = lean_usize_shift_right(v_h_4913_, v___x_4918_);
v___x_4920_ = lean_nat_add(v_i_4906_, v___x_4915_);
lean_dec(v_i_4906_);
lean_inc(v_v_4911_);
lean_inc(v_k_4910_);
v___x_4921_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_entries_4907_, v_h_4919_, v_depth_4903_, v_k_4910_, v_v_4911_);
v_i_4906_ = v___x_4920_;
v_entries_4907_ = v___x_4921_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object* v_depth_4923_, lean_object* v_keys_4924_, lean_object* v_vals_4925_, lean_object* v_i_4926_, lean_object* v_entries_4927_){
_start:
{
size_t v_depth_boxed_4928_; lean_object* v_res_4929_; 
v_depth_boxed_4928_ = lean_unbox_usize(v_depth_4923_);
lean_dec(v_depth_4923_);
v_res_4929_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg(v_depth_boxed_4928_, v_keys_4924_, v_vals_4925_, v_i_4926_, v_entries_4927_);
lean_dec_ref(v_vals_4925_);
lean_dec_ref(v_keys_4924_);
return v_res_4929_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_x_4930_, lean_object* v_x_4931_, lean_object* v_x_4932_, lean_object* v_x_4933_, lean_object* v_x_4934_){
_start:
{
size_t v_x_52796__boxed_4935_; size_t v_x_52797__boxed_4936_; lean_object* v_res_4937_; 
v_x_52796__boxed_4935_ = lean_unbox_usize(v_x_4931_);
lean_dec(v_x_4931_);
v_x_52797__boxed_4936_ = lean_unbox_usize(v_x_4932_);
lean_dec(v_x_4932_);
v_res_4937_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_x_4930_, v_x_52796__boxed_4935_, v_x_52797__boxed_4936_, v_x_4933_, v_x_4934_);
return v_res_4937_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0___redArg(lean_object* v_x_4938_, lean_object* v_x_4939_, lean_object* v_x_4940_){
_start:
{
uint64_t v___x_4941_; size_t v___x_4942_; size_t v___x_4943_; lean_object* v___x_4944_; 
v___x_4941_ = l_Lean_instHashableMVarId_hash(v_x_4939_);
v___x_4942_ = lean_uint64_to_usize(v___x_4941_);
v___x_4943_ = ((size_t)1ULL);
v___x_4944_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_x_4938_, v___x_4942_, v___x_4943_, v_x_4939_, v_x_4940_);
return v___x_4944_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(lean_object* v_mvarId_4945_, lean_object* v_val_4946_, lean_object* v___y_4947_){
_start:
{
lean_object* v___x_4949_; lean_object* v_mctx_4950_; lean_object* v_cache_4951_; lean_object* v_zetaDeltaFVarIds_4952_; lean_object* v_postponed_4953_; lean_object* v_diag_4954_; lean_object* v___x_4956_; uint8_t v_isShared_4957_; uint8_t v_isSharedCheck_4982_; 
v___x_4949_ = lean_st_ref_take(v___y_4947_);
v_mctx_4950_ = lean_ctor_get(v___x_4949_, 0);
v_cache_4951_ = lean_ctor_get(v___x_4949_, 1);
v_zetaDeltaFVarIds_4952_ = lean_ctor_get(v___x_4949_, 2);
v_postponed_4953_ = lean_ctor_get(v___x_4949_, 3);
v_diag_4954_ = lean_ctor_get(v___x_4949_, 4);
v_isSharedCheck_4982_ = !lean_is_exclusive(v___x_4949_);
if (v_isSharedCheck_4982_ == 0)
{
v___x_4956_ = v___x_4949_;
v_isShared_4957_ = v_isSharedCheck_4982_;
goto v_resetjp_4955_;
}
else
{
lean_inc(v_diag_4954_);
lean_inc(v_postponed_4953_);
lean_inc(v_zetaDeltaFVarIds_4952_);
lean_inc(v_cache_4951_);
lean_inc(v_mctx_4950_);
lean_dec(v___x_4949_);
v___x_4956_ = lean_box(0);
v_isShared_4957_ = v_isSharedCheck_4982_;
goto v_resetjp_4955_;
}
v_resetjp_4955_:
{
lean_object* v_depth_4958_; lean_object* v_levelAssignDepth_4959_; lean_object* v_lmvarCounter_4960_; lean_object* v_mvarCounter_4961_; lean_object* v_lDecls_4962_; lean_object* v_decls_4963_; lean_object* v_userNames_4964_; lean_object* v_lAssignment_4965_; lean_object* v_eAssignment_4966_; lean_object* v_dAssignment_4967_; lean_object* v___x_4969_; uint8_t v_isShared_4970_; uint8_t v_isSharedCheck_4981_; 
v_depth_4958_ = lean_ctor_get(v_mctx_4950_, 0);
v_levelAssignDepth_4959_ = lean_ctor_get(v_mctx_4950_, 1);
v_lmvarCounter_4960_ = lean_ctor_get(v_mctx_4950_, 2);
v_mvarCounter_4961_ = lean_ctor_get(v_mctx_4950_, 3);
v_lDecls_4962_ = lean_ctor_get(v_mctx_4950_, 4);
v_decls_4963_ = lean_ctor_get(v_mctx_4950_, 5);
v_userNames_4964_ = lean_ctor_get(v_mctx_4950_, 6);
v_lAssignment_4965_ = lean_ctor_get(v_mctx_4950_, 7);
v_eAssignment_4966_ = lean_ctor_get(v_mctx_4950_, 8);
v_dAssignment_4967_ = lean_ctor_get(v_mctx_4950_, 9);
v_isSharedCheck_4981_ = !lean_is_exclusive(v_mctx_4950_);
if (v_isSharedCheck_4981_ == 0)
{
v___x_4969_ = v_mctx_4950_;
v_isShared_4970_ = v_isSharedCheck_4981_;
goto v_resetjp_4968_;
}
else
{
lean_inc(v_dAssignment_4967_);
lean_inc(v_eAssignment_4966_);
lean_inc(v_lAssignment_4965_);
lean_inc(v_userNames_4964_);
lean_inc(v_decls_4963_);
lean_inc(v_lDecls_4962_);
lean_inc(v_mvarCounter_4961_);
lean_inc(v_lmvarCounter_4960_);
lean_inc(v_levelAssignDepth_4959_);
lean_inc(v_depth_4958_);
lean_dec(v_mctx_4950_);
v___x_4969_ = lean_box(0);
v_isShared_4970_ = v_isSharedCheck_4981_;
goto v_resetjp_4968_;
}
v_resetjp_4968_:
{
lean_object* v___x_4971_; lean_object* v___x_4973_; 
v___x_4971_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0___redArg(v_eAssignment_4966_, v_mvarId_4945_, v_val_4946_);
if (v_isShared_4970_ == 0)
{
lean_ctor_set(v___x_4969_, 8, v___x_4971_);
v___x_4973_ = v___x_4969_;
goto v_reusejp_4972_;
}
else
{
lean_object* v_reuseFailAlloc_4980_; 
v_reuseFailAlloc_4980_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4980_, 0, v_depth_4958_);
lean_ctor_set(v_reuseFailAlloc_4980_, 1, v_levelAssignDepth_4959_);
lean_ctor_set(v_reuseFailAlloc_4980_, 2, v_lmvarCounter_4960_);
lean_ctor_set(v_reuseFailAlloc_4980_, 3, v_mvarCounter_4961_);
lean_ctor_set(v_reuseFailAlloc_4980_, 4, v_lDecls_4962_);
lean_ctor_set(v_reuseFailAlloc_4980_, 5, v_decls_4963_);
lean_ctor_set(v_reuseFailAlloc_4980_, 6, v_userNames_4964_);
lean_ctor_set(v_reuseFailAlloc_4980_, 7, v_lAssignment_4965_);
lean_ctor_set(v_reuseFailAlloc_4980_, 8, v___x_4971_);
lean_ctor_set(v_reuseFailAlloc_4980_, 9, v_dAssignment_4967_);
v___x_4973_ = v_reuseFailAlloc_4980_;
goto v_reusejp_4972_;
}
v_reusejp_4972_:
{
lean_object* v___x_4975_; 
if (v_isShared_4957_ == 0)
{
lean_ctor_set(v___x_4956_, 0, v___x_4973_);
v___x_4975_ = v___x_4956_;
goto v_reusejp_4974_;
}
else
{
lean_object* v_reuseFailAlloc_4979_; 
v_reuseFailAlloc_4979_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4979_, 0, v___x_4973_);
lean_ctor_set(v_reuseFailAlloc_4979_, 1, v_cache_4951_);
lean_ctor_set(v_reuseFailAlloc_4979_, 2, v_zetaDeltaFVarIds_4952_);
lean_ctor_set(v_reuseFailAlloc_4979_, 3, v_postponed_4953_);
lean_ctor_set(v_reuseFailAlloc_4979_, 4, v_diag_4954_);
v___x_4975_ = v_reuseFailAlloc_4979_;
goto v_reusejp_4974_;
}
v_reusejp_4974_:
{
lean_object* v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; 
v___x_4976_ = lean_st_ref_set(v___y_4947_, v___x_4975_);
v___x_4977_ = lean_box(0);
v___x_4978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4978_, 0, v___x_4977_);
return v___x_4978_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg___boxed(lean_object* v_mvarId_4983_, lean_object* v_val_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_){
_start:
{
lean_object* v_res_4987_; 
v_res_4987_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(v_mvarId_4983_, v_val_4984_, v___y_4985_);
lean_dec(v___y_4985_);
return v_res_4987_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3(lean_object* v_mvarId_4995_, lean_object* v___x_4996_, lean_object* v_as_4997_, size_t v_sz_4998_, size_t v_i_4999_, lean_object* v_b_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_){
_start:
{
lean_object* v_a_5009_; uint8_t v___x_5013_; 
v___x_5013_ = lean_usize_dec_lt(v_i_4999_, v_sz_4998_);
if (v___x_5013_ == 0)
{
lean_object* v___x_5014_; 
lean_dec_ref(v___x_4996_);
lean_dec(v_mvarId_4995_);
v___x_5014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5014_, 0, v_b_5000_);
return v___x_5014_;
}
else
{
lean_object* v_a_5015_; lean_object* v___x_5016_; 
v_a_5015_ = lean_array_uget_borrowed(v_as_4997_, v_i_4999_);
lean_inc(v_a_5015_);
v___x_5016_ = l_Lean_FVarId_getDecl___redArg(v_a_5015_, v___y_5003_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5016_) == 0)
{
lean_object* v_options_5017_; lean_object* v_a_5018_; lean_object* v_snd_5019_; lean_object* v___x_5021_; uint8_t v_isShared_5022_; uint8_t v_isSharedCheck_5210_; 
v_options_5017_ = lean_ctor_get(v___y_5005_, 2);
v_a_5018_ = lean_ctor_get(v___x_5016_, 0);
lean_inc(v_a_5018_);
lean_dec_ref_known(v___x_5016_, 1);
v_snd_5019_ = lean_ctor_get(v_b_5000_, 1);
v_isSharedCheck_5210_ = !lean_is_exclusive(v_b_5000_);
if (v_isSharedCheck_5210_ == 0)
{
lean_object* v_unused_5211_; 
v_unused_5211_ = lean_ctor_get(v_b_5000_, 0);
lean_dec(v_unused_5211_);
v___x_5021_ = v_b_5000_;
v_isShared_5022_ = v_isSharedCheck_5210_;
goto v_resetjp_5020_;
}
else
{
lean_inc(v_snd_5019_);
lean_dec(v_b_5000_);
v___x_5021_ = lean_box(0);
v_isShared_5022_ = v_isSharedCheck_5210_;
goto v_resetjp_5020_;
}
v_resetjp_5020_:
{
lean_object* v_inheritedTraceOptions_5023_; uint8_t v_hasTrace_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; lean_object* v___y_5028_; 
v_inheritedTraceOptions_5023_ = lean_ctor_get(v___y_5005_, 13);
v_hasTrace_5024_ = lean_ctor_get_uint8(v_options_5017_, sizeof(void*)*1);
v___x_5025_ = lean_box(0);
v___x_5026_ = l_Lean_LocalDecl_type(v_a_5018_);
if (v_hasTrace_5024_ == 0)
{
lean_object* v___x_5125_; 
lean_inc_ref(v___x_4996_);
lean_inc_ref(v___x_5026_);
v___x_5125_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5026_, v___x_4996_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
v___y_5028_ = v___x_5125_;
goto v___jp_5027_;
}
else
{
lean_object* v___f_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; uint8_t v___x_5130_; lean_object* v___y_5132_; lean_object* v___y_5133_; lean_object* v_a_5134_; lean_object* v___y_5147_; lean_object* v___y_5148_; lean_object* v_a_5149_; 
lean_inc_ref(v___x_5026_);
lean_inc(v_a_5018_);
v___f_5126_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___boxed), 10, 2);
lean_closure_set(v___f_5126_, 0, v_a_5018_);
lean_closure_set(v___f_5126_, 1, v___x_5026_);
v___x_5127_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_5128_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_5129_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_5130_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5023_, v_options_5017_, v___x_5129_);
if (v___x_5130_ == 0)
{
lean_object* v___x_5207_; uint8_t v___x_5208_; 
v___x_5207_ = l_Lean_trace_profiler;
v___x_5208_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5017_, v___x_5207_);
if (v___x_5208_ == 0)
{
lean_object* v___x_5209_; 
lean_dec_ref(v___f_5126_);
lean_inc_ref(v___x_4996_);
lean_inc_ref(v___x_5026_);
v___x_5209_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5026_, v___x_4996_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
v___y_5028_ = v___x_5209_;
goto v___jp_5027_;
}
else
{
goto v___jp_5158_;
}
}
else
{
goto v___jp_5158_;
}
v___jp_5131_:
{
lean_object* v___x_5135_; double v___x_5136_; double v___x_5137_; double v___x_5138_; double v___x_5139_; double v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; 
v___x_5135_ = lean_io_mono_nanos_now();
v___x_5136_ = lean_float_of_nat(v___y_5133_);
v___x_5137_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_5138_ = lean_float_div(v___x_5136_, v___x_5137_);
v___x_5139_ = lean_float_of_nat(v___x_5135_);
v___x_5140_ = lean_float_div(v___x_5139_, v___x_5137_);
v___x_5141_ = lean_box_float(v___x_5138_);
v___x_5142_ = lean_box_float(v___x_5140_);
v___x_5143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5143_, 0, v___x_5141_);
lean_ctor_set(v___x_5143_, 1, v___x_5142_);
v___x_5144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5144_, 0, v_a_5134_);
lean_ctor_set(v___x_5144_, 1, v___x_5143_);
v___x_5145_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v___x_5127_, v_hasTrace_5024_, v___x_5128_, v_options_5017_, v___x_5130_, v___y_5132_, v___f_5126_, v___x_5144_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
v___y_5028_ = v___x_5145_;
goto v___jp_5027_;
}
v___jp_5146_:
{
lean_object* v___x_5150_; double v___x_5151_; double v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; 
v___x_5150_ = lean_io_get_num_heartbeats();
v___x_5151_ = lean_float_of_nat(v___y_5148_);
v___x_5152_ = lean_float_of_nat(v___x_5150_);
v___x_5153_ = lean_box_float(v___x_5151_);
v___x_5154_ = lean_box_float(v___x_5152_);
v___x_5155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5155_, 0, v___x_5153_);
lean_ctor_set(v___x_5155_, 1, v___x_5154_);
v___x_5156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5156_, 0, v_a_5149_);
lean_ctor_set(v___x_5156_, 1, v___x_5155_);
v___x_5157_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v___x_5127_, v_hasTrace_5024_, v___x_5128_, v_options_5017_, v___x_5130_, v___y_5147_, v___f_5126_, v___x_5156_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
v___y_5028_ = v___x_5157_;
goto v___jp_5027_;
}
v___jp_5158_:
{
lean_object* v___x_5159_; 
v___x_5159_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(v___y_5006_);
if (lean_obj_tag(v___x_5159_) == 0)
{
lean_object* v_a_5160_; lean_object* v___x_5161_; uint8_t v___x_5162_; 
v_a_5160_ = lean_ctor_get(v___x_5159_, 0);
lean_inc(v_a_5160_);
lean_dec_ref_known(v___x_5159_, 1);
v___x_5161_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5162_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5017_, v___x_5161_);
if (v___x_5162_ == 0)
{
lean_object* v___x_5163_; lean_object* v___x_5164_; 
v___x_5163_ = lean_io_mono_nanos_now();
lean_inc_ref(v___x_4996_);
lean_inc_ref(v___x_5026_);
v___x_5164_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5026_, v___x_4996_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5164_) == 0)
{
lean_object* v_a_5165_; lean_object* v___x_5167_; uint8_t v_isShared_5168_; uint8_t v_isSharedCheck_5172_; 
v_a_5165_ = lean_ctor_get(v___x_5164_, 0);
v_isSharedCheck_5172_ = !lean_is_exclusive(v___x_5164_);
if (v_isSharedCheck_5172_ == 0)
{
v___x_5167_ = v___x_5164_;
v_isShared_5168_ = v_isSharedCheck_5172_;
goto v_resetjp_5166_;
}
else
{
lean_inc(v_a_5165_);
lean_dec(v___x_5164_);
v___x_5167_ = lean_box(0);
v_isShared_5168_ = v_isSharedCheck_5172_;
goto v_resetjp_5166_;
}
v_resetjp_5166_:
{
lean_object* v___x_5170_; 
if (v_isShared_5168_ == 0)
{
lean_ctor_set_tag(v___x_5167_, 1);
v___x_5170_ = v___x_5167_;
goto v_reusejp_5169_;
}
else
{
lean_object* v_reuseFailAlloc_5171_; 
v_reuseFailAlloc_5171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5171_, 0, v_a_5165_);
v___x_5170_ = v_reuseFailAlloc_5171_;
goto v_reusejp_5169_;
}
v_reusejp_5169_:
{
v___y_5132_ = v_a_5160_;
v___y_5133_ = v___x_5163_;
v_a_5134_ = v___x_5170_;
goto v___jp_5131_;
}
}
}
else
{
lean_object* v_a_5173_; lean_object* v___x_5175_; uint8_t v_isShared_5176_; uint8_t v_isSharedCheck_5180_; 
v_a_5173_ = lean_ctor_get(v___x_5164_, 0);
v_isSharedCheck_5180_ = !lean_is_exclusive(v___x_5164_);
if (v_isSharedCheck_5180_ == 0)
{
v___x_5175_ = v___x_5164_;
v_isShared_5176_ = v_isSharedCheck_5180_;
goto v_resetjp_5174_;
}
else
{
lean_inc(v_a_5173_);
lean_dec(v___x_5164_);
v___x_5175_ = lean_box(0);
v_isShared_5176_ = v_isSharedCheck_5180_;
goto v_resetjp_5174_;
}
v_resetjp_5174_:
{
lean_object* v___x_5178_; 
if (v_isShared_5176_ == 0)
{
lean_ctor_set_tag(v___x_5175_, 0);
v___x_5178_ = v___x_5175_;
goto v_reusejp_5177_;
}
else
{
lean_object* v_reuseFailAlloc_5179_; 
v_reuseFailAlloc_5179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5179_, 0, v_a_5173_);
v___x_5178_ = v_reuseFailAlloc_5179_;
goto v_reusejp_5177_;
}
v_reusejp_5177_:
{
v___y_5132_ = v_a_5160_;
v___y_5133_ = v___x_5163_;
v_a_5134_ = v___x_5178_;
goto v___jp_5131_;
}
}
}
}
else
{
lean_object* v___x_5181_; lean_object* v___x_5182_; 
v___x_5181_ = lean_io_get_num_heartbeats();
lean_inc_ref(v___x_4996_);
lean_inc_ref(v___x_5026_);
v___x_5182_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5026_, v___x_4996_, v___y_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5182_) == 0)
{
lean_object* v_a_5183_; lean_object* v___x_5185_; uint8_t v_isShared_5186_; uint8_t v_isSharedCheck_5190_; 
v_a_5183_ = lean_ctor_get(v___x_5182_, 0);
v_isSharedCheck_5190_ = !lean_is_exclusive(v___x_5182_);
if (v_isSharedCheck_5190_ == 0)
{
v___x_5185_ = v___x_5182_;
v_isShared_5186_ = v_isSharedCheck_5190_;
goto v_resetjp_5184_;
}
else
{
lean_inc(v_a_5183_);
lean_dec(v___x_5182_);
v___x_5185_ = lean_box(0);
v_isShared_5186_ = v_isSharedCheck_5190_;
goto v_resetjp_5184_;
}
v_resetjp_5184_:
{
lean_object* v___x_5188_; 
if (v_isShared_5186_ == 0)
{
lean_ctor_set_tag(v___x_5185_, 1);
v___x_5188_ = v___x_5185_;
goto v_reusejp_5187_;
}
else
{
lean_object* v_reuseFailAlloc_5189_; 
v_reuseFailAlloc_5189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5189_, 0, v_a_5183_);
v___x_5188_ = v_reuseFailAlloc_5189_;
goto v_reusejp_5187_;
}
v_reusejp_5187_:
{
v___y_5147_ = v_a_5160_;
v___y_5148_ = v___x_5181_;
v_a_5149_ = v___x_5188_;
goto v___jp_5146_;
}
}
}
else
{
lean_object* v_a_5191_; lean_object* v___x_5193_; uint8_t v_isShared_5194_; uint8_t v_isSharedCheck_5198_; 
v_a_5191_ = lean_ctor_get(v___x_5182_, 0);
v_isSharedCheck_5198_ = !lean_is_exclusive(v___x_5182_);
if (v_isSharedCheck_5198_ == 0)
{
v___x_5193_ = v___x_5182_;
v_isShared_5194_ = v_isSharedCheck_5198_;
goto v_resetjp_5192_;
}
else
{
lean_inc(v_a_5191_);
lean_dec(v___x_5182_);
v___x_5193_ = lean_box(0);
v_isShared_5194_ = v_isSharedCheck_5198_;
goto v_resetjp_5192_;
}
v_resetjp_5192_:
{
lean_object* v___x_5196_; 
if (v_isShared_5194_ == 0)
{
lean_ctor_set_tag(v___x_5193_, 0);
v___x_5196_ = v___x_5193_;
goto v_reusejp_5195_;
}
else
{
lean_object* v_reuseFailAlloc_5197_; 
v_reuseFailAlloc_5197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5197_, 0, v_a_5191_);
v___x_5196_ = v_reuseFailAlloc_5197_;
goto v_reusejp_5195_;
}
v_reusejp_5195_:
{
v___y_5147_ = v_a_5160_;
v___y_5148_ = v___x_5181_;
v_a_5149_ = v___x_5196_;
goto v___jp_5146_;
}
}
}
}
}
else
{
lean_object* v_a_5199_; lean_object* v___x_5201_; uint8_t v_isShared_5202_; uint8_t v_isSharedCheck_5206_; 
lean_dec_ref(v___f_5126_);
lean_dec_ref(v___x_5026_);
lean_del_object(v___x_5021_);
lean_dec(v_snd_5019_);
lean_dec(v_a_5018_);
lean_dec_ref(v___x_4996_);
lean_dec(v_mvarId_4995_);
v_a_5199_ = lean_ctor_get(v___x_5159_, 0);
v_isSharedCheck_5206_ = !lean_is_exclusive(v___x_5159_);
if (v_isSharedCheck_5206_ == 0)
{
v___x_5201_ = v___x_5159_;
v_isShared_5202_ = v_isSharedCheck_5206_;
goto v_resetjp_5200_;
}
else
{
lean_inc(v_a_5199_);
lean_dec(v___x_5159_);
v___x_5201_ = lean_box(0);
v_isShared_5202_ = v_isSharedCheck_5206_;
goto v_resetjp_5200_;
}
v_resetjp_5200_:
{
lean_object* v___x_5204_; 
if (v_isShared_5202_ == 0)
{
v___x_5204_ = v___x_5201_;
goto v_reusejp_5203_;
}
else
{
lean_object* v_reuseFailAlloc_5205_; 
v_reuseFailAlloc_5205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5205_, 0, v_a_5199_);
v___x_5204_ = v_reuseFailAlloc_5205_;
goto v_reusejp_5203_;
}
v_reusejp_5203_:
{
return v___x_5204_;
}
}
}
}
}
v___jp_5027_:
{
if (lean_obj_tag(v___y_5028_) == 0)
{
lean_object* v_a_5029_; 
v_a_5029_ = lean_ctor_get(v___y_5028_, 0);
lean_inc(v_a_5029_);
lean_dec_ref_known(v___y_5028_, 1);
if (lean_obj_tag(v_a_5029_) == 0)
{
lean_object* v___x_5031_; 
lean_dec_ref_known(v_a_5029_, 0);
lean_dec_ref(v___x_5026_);
lean_dec(v_a_5018_);
if (v_isShared_5022_ == 0)
{
lean_ctor_set(v___x_5021_, 0, v___x_5025_);
v___x_5031_ = v___x_5021_;
goto v_reusejp_5030_;
}
else
{
lean_object* v_reuseFailAlloc_5032_; 
v_reuseFailAlloc_5032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5032_, 0, v___x_5025_);
lean_ctor_set(v_reuseFailAlloc_5032_, 1, v_snd_5019_);
v___x_5031_ = v_reuseFailAlloc_5032_;
goto v_reusejp_5030_;
}
v_reusejp_5030_:
{
v_a_5009_ = v___x_5031_;
goto v___jp_5008_;
}
}
else
{
lean_object* v_e_x27_5033_; lean_object* v_proof_5034_; uint8_t v___x_5035_; 
v_e_x27_5033_ = lean_ctor_get(v_a_5029_, 0);
lean_inc_ref_n(v_e_x27_5033_, 2);
v_proof_5034_ = lean_ctor_get(v_a_5029_, 1);
lean_inc_ref(v_proof_5034_);
lean_dec_ref_known(v_a_5029_, 2);
v___x_5035_ = l_Lean_Expr_isFalse(v_e_x27_5033_);
if (v___x_5035_ == 0)
{
lean_object* v___x_5036_; 
lean_inc_ref(v___x_5026_);
v___x_5036_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_5026_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5036_) == 0)
{
lean_object* v_a_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; uint8_t v___x_5045_; uint8_t v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5050_; 
v_a_5037_ = lean_ctor_get(v___x_5036_, 0);
lean_inc(v_a_5037_);
lean_dec_ref_known(v___x_5036_, 1);
v___x_5038_ = l_Lean_LocalDecl_userName(v_a_5018_);
lean_dec(v_a_5018_);
v___x_5039_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__2));
v___x_5040_ = lean_box(0);
v___x_5041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5041_, 0, v_a_5037_);
lean_ctor_set(v___x_5041_, 1, v___x_5040_);
v___x_5042_ = l_Lean_mkConst(v___x_5039_, v___x_5041_);
lean_inc(v_a_5015_);
v___x_5043_ = l_Lean_mkFVar(v_a_5015_);
lean_inc_ref(v_e_x27_5033_);
v___x_5044_ = l_Lean_mkApp4(v___x_5042_, v___x_5026_, v_e_x27_5033_, v_proof_5034_, v___x_5043_);
v___x_5045_ = 0;
v___x_5046_ = 0;
v___x_5047_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5047_, 0, v___x_5038_);
lean_ctor_set(v___x_5047_, 1, v_e_x27_5033_);
lean_ctor_set(v___x_5047_, 2, v___x_5044_);
lean_ctor_set_uint8(v___x_5047_, sizeof(void*)*3, v___x_5045_);
lean_ctor_set_uint8(v___x_5047_, sizeof(void*)*3 + 1, v___x_5046_);
v___x_5048_ = lean_array_push(v_snd_5019_, v___x_5047_);
if (v_isShared_5022_ == 0)
{
lean_ctor_set(v___x_5021_, 1, v___x_5048_);
lean_ctor_set(v___x_5021_, 0, v___x_5025_);
v___x_5050_ = v___x_5021_;
goto v_reusejp_5049_;
}
else
{
lean_object* v_reuseFailAlloc_5051_; 
v_reuseFailAlloc_5051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5051_, 0, v___x_5025_);
lean_ctor_set(v_reuseFailAlloc_5051_, 1, v___x_5048_);
v___x_5050_ = v_reuseFailAlloc_5051_;
goto v_reusejp_5049_;
}
v_reusejp_5049_:
{
v_a_5009_ = v___x_5050_;
goto v___jp_5008_;
}
}
else
{
lean_object* v_a_5052_; lean_object* v___x_5054_; uint8_t v_isShared_5055_; uint8_t v_isSharedCheck_5059_; 
lean_dec_ref(v_proof_5034_);
lean_dec_ref(v_e_x27_5033_);
lean_dec_ref(v___x_5026_);
lean_del_object(v___x_5021_);
lean_dec(v_snd_5019_);
lean_dec(v_a_5018_);
lean_dec_ref(v___x_4996_);
lean_dec(v_mvarId_4995_);
v_a_5052_ = lean_ctor_get(v___x_5036_, 0);
v_isSharedCheck_5059_ = !lean_is_exclusive(v___x_5036_);
if (v_isSharedCheck_5059_ == 0)
{
v___x_5054_ = v___x_5036_;
v_isShared_5055_ = v_isSharedCheck_5059_;
goto v_resetjp_5053_;
}
else
{
lean_inc(v_a_5052_);
lean_dec(v___x_5036_);
v___x_5054_ = lean_box(0);
v_isShared_5055_ = v_isSharedCheck_5059_;
goto v_resetjp_5053_;
}
v_resetjp_5053_:
{
lean_object* v___x_5057_; 
if (v_isShared_5055_ == 0)
{
v___x_5057_ = v___x_5054_;
goto v_reusejp_5056_;
}
else
{
lean_object* v_reuseFailAlloc_5058_; 
v_reuseFailAlloc_5058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5058_, 0, v_a_5052_);
v___x_5057_ = v_reuseFailAlloc_5058_;
goto v_reusejp_5056_;
}
v_reusejp_5056_:
{
return v___x_5057_;
}
}
}
}
else
{
lean_object* v___x_5060_; 
lean_dec(v_a_5018_);
lean_dec_ref(v___x_4996_);
lean_inc_ref(v___x_5026_);
v___x_5060_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_5026_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5060_) == 0)
{
lean_object* v_a_5061_; lean_object* v___x_5062_; 
v_a_5061_ = lean_ctor_get(v___x_5060_, 0);
lean_inc(v_a_5061_);
lean_dec_ref_known(v___x_5060_, 1);
lean_inc(v_mvarId_4995_);
v___x_5062_ = l_Lean_MVarId_getType(v_mvarId_4995_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5062_) == 0)
{
lean_object* v_a_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; 
v_a_5063_ = lean_ctor_get(v___x_5062_, 0);
lean_inc(v_a_5063_);
lean_dec_ref_known(v___x_5062_, 1);
v___x_5064_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__2));
v___x_5065_ = lean_box(0);
v___x_5066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5066_, 0, v_a_5061_);
lean_ctor_set(v___x_5066_, 1, v___x_5065_);
v___x_5067_ = l_Lean_mkConst(v___x_5064_, v___x_5066_);
lean_inc(v_a_5015_);
v___x_5068_ = l_Lean_mkFVar(v_a_5015_);
v___x_5069_ = l_Lean_mkApp4(v___x_5067_, v___x_5026_, v_e_x27_5033_, v_proof_5034_, v___x_5068_);
v___x_5070_ = l_Lean_Meta_mkFalseElim(v_a_5063_, v___x_5069_, v___y_5003_, v___y_5004_, v___y_5005_, v___y_5006_);
if (lean_obj_tag(v___x_5070_) == 0)
{
lean_object* v_a_5071_; lean_object* v___x_5072_; 
v_a_5071_ = lean_ctor_get(v___x_5070_, 0);
lean_inc(v_a_5071_);
lean_dec_ref_known(v___x_5070_, 1);
v___x_5072_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(v_mvarId_4995_, v_a_5071_, v___y_5004_);
if (lean_obj_tag(v___x_5072_) == 0)
{
lean_object* v___x_5074_; uint8_t v_isShared_5075_; uint8_t v_isSharedCheck_5083_; 
v_isSharedCheck_5083_ = !lean_is_exclusive(v___x_5072_);
if (v_isSharedCheck_5083_ == 0)
{
lean_object* v_unused_5084_; 
v_unused_5084_ = lean_ctor_get(v___x_5072_, 0);
lean_dec(v_unused_5084_);
v___x_5074_ = v___x_5072_;
v_isShared_5075_ = v_isSharedCheck_5083_;
goto v_resetjp_5073_;
}
else
{
lean_dec(v___x_5072_);
v___x_5074_ = lean_box(0);
v_isShared_5075_ = v_isSharedCheck_5083_;
goto v_resetjp_5073_;
}
v_resetjp_5073_:
{
lean_object* v___x_5076_; lean_object* v___x_5078_; 
v___x_5076_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__3));
if (v_isShared_5022_ == 0)
{
lean_ctor_set(v___x_5021_, 0, v___x_5076_);
v___x_5078_ = v___x_5021_;
goto v_reusejp_5077_;
}
else
{
lean_object* v_reuseFailAlloc_5082_; 
v_reuseFailAlloc_5082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5082_, 0, v___x_5076_);
lean_ctor_set(v_reuseFailAlloc_5082_, 1, v_snd_5019_);
v___x_5078_ = v_reuseFailAlloc_5082_;
goto v_reusejp_5077_;
}
v_reusejp_5077_:
{
lean_object* v___x_5080_; 
if (v_isShared_5075_ == 0)
{
lean_ctor_set(v___x_5074_, 0, v___x_5078_);
v___x_5080_ = v___x_5074_;
goto v_reusejp_5079_;
}
else
{
lean_object* v_reuseFailAlloc_5081_; 
v_reuseFailAlloc_5081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5081_, 0, v___x_5078_);
v___x_5080_ = v_reuseFailAlloc_5081_;
goto v_reusejp_5079_;
}
v_reusejp_5079_:
{
return v___x_5080_;
}
}
}
}
else
{
lean_object* v_a_5085_; lean_object* v___x_5087_; uint8_t v_isShared_5088_; uint8_t v_isSharedCheck_5092_; 
lean_del_object(v___x_5021_);
lean_dec(v_snd_5019_);
v_a_5085_ = lean_ctor_get(v___x_5072_, 0);
v_isSharedCheck_5092_ = !lean_is_exclusive(v___x_5072_);
if (v_isSharedCheck_5092_ == 0)
{
v___x_5087_ = v___x_5072_;
v_isShared_5088_ = v_isSharedCheck_5092_;
goto v_resetjp_5086_;
}
else
{
lean_inc(v_a_5085_);
lean_dec(v___x_5072_);
v___x_5087_ = lean_box(0);
v_isShared_5088_ = v_isSharedCheck_5092_;
goto v_resetjp_5086_;
}
v_resetjp_5086_:
{
lean_object* v___x_5090_; 
if (v_isShared_5088_ == 0)
{
v___x_5090_ = v___x_5087_;
goto v_reusejp_5089_;
}
else
{
lean_object* v_reuseFailAlloc_5091_; 
v_reuseFailAlloc_5091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5091_, 0, v_a_5085_);
v___x_5090_ = v_reuseFailAlloc_5091_;
goto v_reusejp_5089_;
}
v_reusejp_5089_:
{
return v___x_5090_;
}
}
}
}
else
{
lean_object* v_a_5093_; lean_object* v___x_5095_; uint8_t v_isShared_5096_; uint8_t v_isSharedCheck_5100_; 
lean_del_object(v___x_5021_);
lean_dec(v_snd_5019_);
lean_dec(v_mvarId_4995_);
v_a_5093_ = lean_ctor_get(v___x_5070_, 0);
v_isSharedCheck_5100_ = !lean_is_exclusive(v___x_5070_);
if (v_isSharedCheck_5100_ == 0)
{
v___x_5095_ = v___x_5070_;
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
else
{
lean_inc(v_a_5093_);
lean_dec(v___x_5070_);
v___x_5095_ = lean_box(0);
v_isShared_5096_ = v_isSharedCheck_5100_;
goto v_resetjp_5094_;
}
v_resetjp_5094_:
{
lean_object* v___x_5098_; 
if (v_isShared_5096_ == 0)
{
v___x_5098_ = v___x_5095_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5099_; 
v_reuseFailAlloc_5099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5099_, 0, v_a_5093_);
v___x_5098_ = v_reuseFailAlloc_5099_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
return v___x_5098_;
}
}
}
}
else
{
lean_object* v_a_5101_; lean_object* v___x_5103_; uint8_t v_isShared_5104_; uint8_t v_isSharedCheck_5108_; 
lean_dec(v_a_5061_);
lean_dec_ref(v_proof_5034_);
lean_dec_ref(v_e_x27_5033_);
lean_dec_ref(v___x_5026_);
lean_del_object(v___x_5021_);
lean_dec(v_snd_5019_);
lean_dec(v_mvarId_4995_);
v_a_5101_ = lean_ctor_get(v___x_5062_, 0);
v_isSharedCheck_5108_ = !lean_is_exclusive(v___x_5062_);
if (v_isSharedCheck_5108_ == 0)
{
v___x_5103_ = v___x_5062_;
v_isShared_5104_ = v_isSharedCheck_5108_;
goto v_resetjp_5102_;
}
else
{
lean_inc(v_a_5101_);
lean_dec(v___x_5062_);
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
lean_object* v_a_5109_; lean_object* v___x_5111_; uint8_t v_isShared_5112_; uint8_t v_isSharedCheck_5116_; 
lean_dec_ref(v_proof_5034_);
lean_dec_ref(v_e_x27_5033_);
lean_dec_ref(v___x_5026_);
lean_del_object(v___x_5021_);
lean_dec(v_snd_5019_);
lean_dec(v_mvarId_4995_);
v_a_5109_ = lean_ctor_get(v___x_5060_, 0);
v_isSharedCheck_5116_ = !lean_is_exclusive(v___x_5060_);
if (v_isSharedCheck_5116_ == 0)
{
v___x_5111_ = v___x_5060_;
v_isShared_5112_ = v_isSharedCheck_5116_;
goto v_resetjp_5110_;
}
else
{
lean_inc(v_a_5109_);
lean_dec(v___x_5060_);
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
}
}
else
{
lean_object* v_a_5117_; lean_object* v___x_5119_; uint8_t v_isShared_5120_; uint8_t v_isSharedCheck_5124_; 
lean_dec_ref(v___x_5026_);
lean_del_object(v___x_5021_);
lean_dec(v_snd_5019_);
lean_dec(v_a_5018_);
lean_dec_ref(v___x_4996_);
lean_dec(v_mvarId_4995_);
v_a_5117_ = lean_ctor_get(v___y_5028_, 0);
v_isSharedCheck_5124_ = !lean_is_exclusive(v___y_5028_);
if (v_isSharedCheck_5124_ == 0)
{
v___x_5119_ = v___y_5028_;
v_isShared_5120_ = v_isSharedCheck_5124_;
goto v_resetjp_5118_;
}
else
{
lean_inc(v_a_5117_);
lean_dec(v___y_5028_);
v___x_5119_ = lean_box(0);
v_isShared_5120_ = v_isSharedCheck_5124_;
goto v_resetjp_5118_;
}
v_resetjp_5118_:
{
lean_object* v___x_5122_; 
if (v_isShared_5120_ == 0)
{
v___x_5122_ = v___x_5119_;
goto v_reusejp_5121_;
}
else
{
lean_object* v_reuseFailAlloc_5123_; 
v_reuseFailAlloc_5123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5123_, 0, v_a_5117_);
v___x_5122_ = v_reuseFailAlloc_5123_;
goto v_reusejp_5121_;
}
v_reusejp_5121_:
{
return v___x_5122_;
}
}
}
}
}
}
else
{
lean_object* v_a_5212_; lean_object* v___x_5214_; uint8_t v_isShared_5215_; uint8_t v_isSharedCheck_5219_; 
lean_dec_ref(v_b_5000_);
lean_dec_ref(v___x_4996_);
lean_dec(v_mvarId_4995_);
v_a_5212_ = lean_ctor_get(v___x_5016_, 0);
v_isSharedCheck_5219_ = !lean_is_exclusive(v___x_5016_);
if (v_isSharedCheck_5219_ == 0)
{
v___x_5214_ = v___x_5016_;
v_isShared_5215_ = v_isSharedCheck_5219_;
goto v_resetjp_5213_;
}
else
{
lean_inc(v_a_5212_);
lean_dec(v___x_5016_);
v___x_5214_ = lean_box(0);
v_isShared_5215_ = v_isSharedCheck_5219_;
goto v_resetjp_5213_;
}
v_resetjp_5213_:
{
lean_object* v___x_5217_; 
if (v_isShared_5215_ == 0)
{
v___x_5217_ = v___x_5214_;
goto v_reusejp_5216_;
}
else
{
lean_object* v_reuseFailAlloc_5218_; 
v_reuseFailAlloc_5218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5218_, 0, v_a_5212_);
v___x_5217_ = v_reuseFailAlloc_5218_;
goto v_reusejp_5216_;
}
v_reusejp_5216_:
{
return v___x_5217_;
}
}
}
}
v___jp_5008_:
{
size_t v___x_5010_; size_t v___x_5011_; 
v___x_5010_ = ((size_t)1ULL);
v___x_5011_ = lean_usize_add(v_i_4999_, v___x_5010_);
v_i_4999_ = v___x_5011_;
v_b_5000_ = v_a_5009_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___boxed(lean_object* v_mvarId_5220_, lean_object* v___x_5221_, lean_object* v_as_5222_, lean_object* v_sz_5223_, lean_object* v_i_5224_, lean_object* v_b_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_, lean_object* v___y_5230_, lean_object* v___y_5231_, lean_object* v___y_5232_){
_start:
{
size_t v_sz_boxed_5233_; size_t v_i_boxed_5234_; lean_object* v_res_5235_; 
v_sz_boxed_5233_ = lean_unbox_usize(v_sz_5223_);
lean_dec(v_sz_5223_);
v_i_boxed_5234_ = lean_unbox_usize(v_i_5224_);
lean_dec(v_i_5224_);
v_res_5235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3(v_mvarId_5220_, v___x_5221_, v_as_5222_, v_sz_boxed_5233_, v_i_boxed_5234_, v_b_5225_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_, v___y_5230_, v___y_5231_);
lean_dec(v___y_5231_);
lean_dec_ref(v___y_5230_);
lean_dec(v___y_5229_);
lean_dec_ref(v___y_5228_);
lean_dec(v___y_5227_);
lean_dec_ref(v___y_5226_);
lean_dec_ref(v_as_5222_);
return v_res_5235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1(lean_object* v_mvarId_5236_, lean_object* v___x_5237_, lean_object* v_fvarIdsToSimp_5238_, size_t v_sz_5239_, size_t v___x_5240_, lean_object* v___x_5241_, uint8_t v_simplifyTarget_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_, lean_object* v___y_5245_, lean_object* v___y_5246_, lean_object* v___y_5247_, lean_object* v___y_5248_){
_start:
{
lean_object* v___y_5251_; lean_object* v___y_5252_; lean_object* v___y_5253_; lean_object* v___y_5254_; lean_object* v___y_5255_; uint8_t v___y_5256_; lean_object* v___x_5276_; 
lean_inc_ref(v___x_5237_);
lean_inc(v_mvarId_5236_);
v___x_5276_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3(v_mvarId_5236_, v___x_5237_, v_fvarIdsToSimp_5238_, v_sz_5239_, v___x_5240_, v___x_5241_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_);
if (lean_obj_tag(v___x_5276_) == 0)
{
lean_object* v_a_5277_; lean_object* v___x_5279_; uint8_t v_isShared_5280_; uint8_t v_isSharedCheck_5479_; 
v_a_5277_ = lean_ctor_get(v___x_5276_, 0);
v_isSharedCheck_5479_ = !lean_is_exclusive(v___x_5276_);
if (v_isSharedCheck_5479_ == 0)
{
v___x_5279_ = v___x_5276_;
v_isShared_5280_ = v_isSharedCheck_5479_;
goto v_resetjp_5278_;
}
else
{
lean_inc(v_a_5277_);
lean_dec(v___x_5276_);
v___x_5279_ = lean_box(0);
v_isShared_5280_ = v_isSharedCheck_5479_;
goto v_resetjp_5278_;
}
v_resetjp_5278_:
{
lean_object* v_fst_5281_; lean_object* v_snd_5282_; lean_object* v___x_5284_; uint8_t v_isShared_5285_; uint8_t v_isSharedCheck_5478_; 
v_fst_5281_ = lean_ctor_get(v_a_5277_, 0);
v_snd_5282_ = lean_ctor_get(v_a_5277_, 1);
v_isSharedCheck_5478_ = !lean_is_exclusive(v_a_5277_);
if (v_isSharedCheck_5478_ == 0)
{
v___x_5284_ = v_a_5277_;
v_isShared_5285_ = v_isSharedCheck_5478_;
goto v_resetjp_5283_;
}
else
{
lean_inc(v_snd_5282_);
lean_inc(v_fst_5281_);
lean_dec(v_a_5277_);
v___x_5284_ = lean_box(0);
v_isShared_5285_ = v_isSharedCheck_5478_;
goto v_resetjp_5283_;
}
v_resetjp_5283_:
{
lean_object* v_mvarIdNew_5287_; lean_object* v___y_5288_; lean_object* v___y_5289_; lean_object* v___y_5290_; lean_object* v___y_5291_; lean_object* v___y_5338_; 
if (lean_obj_tag(v_fst_5281_) == 0)
{
lean_del_object(v___x_5279_);
if (v_simplifyTarget_5242_ == 0)
{
lean_del_object(v___x_5284_);
lean_dec_ref(v___x_5237_);
v_mvarIdNew_5287_ = v_mvarId_5236_;
v___y_5288_ = v___y_5245_;
v___y_5289_ = v___y_5246_;
v___y_5290_ = v___y_5247_;
v___y_5291_ = v___y_5248_;
goto v___jp_5286_;
}
else
{
lean_object* v___x_5381_; 
lean_inc(v_mvarId_5236_);
v___x_5381_ = l_Lean_MVarId_getType(v_mvarId_5236_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_);
if (lean_obj_tag(v___x_5381_) == 0)
{
lean_object* v_options_5382_; uint8_t v_hasTrace_5383_; 
v_options_5382_ = lean_ctor_get(v___y_5247_, 2);
v_hasTrace_5383_ = lean_ctor_get_uint8(v_options_5382_, sizeof(void*)*1);
if (v_hasTrace_5383_ == 0)
{
lean_object* v_a_5384_; lean_object* v___x_5385_; 
lean_del_object(v___x_5284_);
v_a_5384_ = lean_ctor_get(v___x_5381_, 0);
lean_inc(v_a_5384_);
lean_dec_ref_known(v___x_5381_, 1);
v___x_5385_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5384_, v___x_5237_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_);
v___y_5338_ = v___x_5385_;
goto v___jp_5337_;
}
else
{
lean_object* v_a_5386_; lean_object* v_inheritedTraceOptions_5387_; lean_object* v___f_5388_; lean_object* v___x_5389_; lean_object* v___x_5390_; lean_object* v___x_5391_; uint8_t v___x_5392_; lean_object* v___y_5394_; lean_object* v___y_5395_; lean_object* v_a_5396_; lean_object* v___y_5411_; lean_object* v___y_5412_; lean_object* v_a_5413_; 
v_a_5386_ = lean_ctor_get(v___x_5381_, 0);
lean_inc_n(v_a_5386_, 2);
lean_dec_ref_known(v___x_5381_, 1);
v_inheritedTraceOptions_5387_ = lean_ctor_get(v___y_5247_, 13);
v___f_5388_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___boxed), 9, 1);
lean_closure_set(v___f_5388_, 0, v_a_5386_);
v___x_5389_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_5390_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_5391_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_5392_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5387_, v_options_5382_, v___x_5391_);
if (v___x_5392_ == 0)
{
lean_object* v___x_5463_; uint8_t v___x_5464_; 
v___x_5463_ = l_Lean_trace_profiler;
v___x_5464_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5382_, v___x_5463_);
if (v___x_5464_ == 0)
{
lean_object* v___x_5465_; 
lean_dec_ref(v___f_5388_);
lean_del_object(v___x_5284_);
v___x_5465_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5386_, v___x_5237_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_);
v___y_5338_ = v___x_5465_;
goto v___jp_5337_;
}
else
{
goto v___jp_5422_;
}
}
else
{
goto v___jp_5422_;
}
v___jp_5393_:
{
lean_object* v___x_5397_; double v___x_5398_; double v___x_5399_; double v___x_5400_; double v___x_5401_; double v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5406_; 
v___x_5397_ = lean_io_mono_nanos_now();
v___x_5398_ = lean_float_of_nat(v___y_5394_);
v___x_5399_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_5400_ = lean_float_div(v___x_5398_, v___x_5399_);
v___x_5401_ = lean_float_of_nat(v___x_5397_);
v___x_5402_ = lean_float_div(v___x_5401_, v___x_5399_);
v___x_5403_ = lean_box_float(v___x_5400_);
v___x_5404_ = lean_box_float(v___x_5402_);
if (v_isShared_5285_ == 0)
{
lean_ctor_set(v___x_5284_, 1, v___x_5404_);
lean_ctor_set(v___x_5284_, 0, v___x_5403_);
v___x_5406_ = v___x_5284_;
goto v_reusejp_5405_;
}
else
{
lean_object* v_reuseFailAlloc_5409_; 
v_reuseFailAlloc_5409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5409_, 0, v___x_5403_);
lean_ctor_set(v_reuseFailAlloc_5409_, 1, v___x_5404_);
v___x_5406_ = v_reuseFailAlloc_5409_;
goto v_reusejp_5405_;
}
v_reusejp_5405_:
{
lean_object* v___x_5407_; lean_object* v___x_5408_; 
v___x_5407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5407_, 0, v_a_5396_);
lean_ctor_set(v___x_5407_, 1, v___x_5406_);
v___x_5408_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v___x_5389_, v_hasTrace_5383_, v___x_5390_, v_options_5382_, v___x_5392_, v___y_5395_, v___f_5388_, v___x_5407_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_);
v___y_5338_ = v___x_5408_;
goto v___jp_5337_;
}
}
v___jp_5410_:
{
lean_object* v___x_5414_; double v___x_5415_; double v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; 
v___x_5414_ = lean_io_get_num_heartbeats();
v___x_5415_ = lean_float_of_nat(v___y_5411_);
v___x_5416_ = lean_float_of_nat(v___x_5414_);
v___x_5417_ = lean_box_float(v___x_5415_);
v___x_5418_ = lean_box_float(v___x_5416_);
v___x_5419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5419_, 0, v___x_5417_);
lean_ctor_set(v___x_5419_, 1, v___x_5418_);
v___x_5420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5420_, 0, v_a_5413_);
lean_ctor_set(v___x_5420_, 1, v___x_5419_);
v___x_5421_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v___x_5389_, v_hasTrace_5383_, v___x_5390_, v_options_5382_, v___x_5392_, v___y_5412_, v___f_5388_, v___x_5420_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_);
v___y_5338_ = v___x_5421_;
goto v___jp_5337_;
}
v___jp_5422_:
{
lean_object* v___x_5423_; lean_object* v_a_5424_; lean_object* v___x_5425_; uint8_t v___x_5426_; 
v___x_5423_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(v___y_5248_);
v_a_5424_ = lean_ctor_get(v___x_5423_, 0);
lean_inc(v_a_5424_);
lean_dec_ref(v___x_5423_);
v___x_5425_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5426_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5382_, v___x_5425_);
if (v___x_5426_ == 0)
{
lean_object* v___x_5427_; lean_object* v___x_5428_; 
v___x_5427_ = lean_io_mono_nanos_now();
v___x_5428_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5386_, v___x_5237_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_);
if (lean_obj_tag(v___x_5428_) == 0)
{
lean_object* v_a_5429_; lean_object* v___x_5431_; uint8_t v_isShared_5432_; uint8_t v_isSharedCheck_5436_; 
v_a_5429_ = lean_ctor_get(v___x_5428_, 0);
v_isSharedCheck_5436_ = !lean_is_exclusive(v___x_5428_);
if (v_isSharedCheck_5436_ == 0)
{
v___x_5431_ = v___x_5428_;
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
else
{
lean_inc(v_a_5429_);
lean_dec(v___x_5428_);
v___x_5431_ = lean_box(0);
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
v_resetjp_5430_:
{
lean_object* v___x_5434_; 
if (v_isShared_5432_ == 0)
{
lean_ctor_set_tag(v___x_5431_, 1);
v___x_5434_ = v___x_5431_;
goto v_reusejp_5433_;
}
else
{
lean_object* v_reuseFailAlloc_5435_; 
v_reuseFailAlloc_5435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_a_5429_);
v___x_5434_ = v_reuseFailAlloc_5435_;
goto v_reusejp_5433_;
}
v_reusejp_5433_:
{
v___y_5394_ = v___x_5427_;
v___y_5395_ = v_a_5424_;
v_a_5396_ = v___x_5434_;
goto v___jp_5393_;
}
}
}
else
{
lean_object* v_a_5437_; lean_object* v___x_5439_; uint8_t v_isShared_5440_; uint8_t v_isSharedCheck_5444_; 
v_a_5437_ = lean_ctor_get(v___x_5428_, 0);
v_isSharedCheck_5444_ = !lean_is_exclusive(v___x_5428_);
if (v_isSharedCheck_5444_ == 0)
{
v___x_5439_ = v___x_5428_;
v_isShared_5440_ = v_isSharedCheck_5444_;
goto v_resetjp_5438_;
}
else
{
lean_inc(v_a_5437_);
lean_dec(v___x_5428_);
v___x_5439_ = lean_box(0);
v_isShared_5440_ = v_isSharedCheck_5444_;
goto v_resetjp_5438_;
}
v_resetjp_5438_:
{
lean_object* v___x_5442_; 
if (v_isShared_5440_ == 0)
{
lean_ctor_set_tag(v___x_5439_, 0);
v___x_5442_ = v___x_5439_;
goto v_reusejp_5441_;
}
else
{
lean_object* v_reuseFailAlloc_5443_; 
v_reuseFailAlloc_5443_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5443_, 0, v_a_5437_);
v___x_5442_ = v_reuseFailAlloc_5443_;
goto v_reusejp_5441_;
}
v_reusejp_5441_:
{
v___y_5394_ = v___x_5427_;
v___y_5395_ = v_a_5424_;
v_a_5396_ = v___x_5442_;
goto v___jp_5393_;
}
}
}
}
else
{
lean_object* v___x_5445_; lean_object* v___x_5446_; 
lean_del_object(v___x_5284_);
v___x_5445_ = lean_io_get_num_heartbeats();
v___x_5446_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5386_, v___x_5237_, v___y_5243_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_);
if (lean_obj_tag(v___x_5446_) == 0)
{
lean_object* v_a_5447_; lean_object* v___x_5449_; uint8_t v_isShared_5450_; uint8_t v_isSharedCheck_5454_; 
v_a_5447_ = lean_ctor_get(v___x_5446_, 0);
v_isSharedCheck_5454_ = !lean_is_exclusive(v___x_5446_);
if (v_isSharedCheck_5454_ == 0)
{
v___x_5449_ = v___x_5446_;
v_isShared_5450_ = v_isSharedCheck_5454_;
goto v_resetjp_5448_;
}
else
{
lean_inc(v_a_5447_);
lean_dec(v___x_5446_);
v___x_5449_ = lean_box(0);
v_isShared_5450_ = v_isSharedCheck_5454_;
goto v_resetjp_5448_;
}
v_resetjp_5448_:
{
lean_object* v___x_5452_; 
if (v_isShared_5450_ == 0)
{
lean_ctor_set_tag(v___x_5449_, 1);
v___x_5452_ = v___x_5449_;
goto v_reusejp_5451_;
}
else
{
lean_object* v_reuseFailAlloc_5453_; 
v_reuseFailAlloc_5453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5453_, 0, v_a_5447_);
v___x_5452_ = v_reuseFailAlloc_5453_;
goto v_reusejp_5451_;
}
v_reusejp_5451_:
{
v___y_5411_ = v___x_5445_;
v___y_5412_ = v_a_5424_;
v_a_5413_ = v___x_5452_;
goto v___jp_5410_;
}
}
}
else
{
lean_object* v_a_5455_; lean_object* v___x_5457_; uint8_t v_isShared_5458_; uint8_t v_isSharedCheck_5462_; 
v_a_5455_ = lean_ctor_get(v___x_5446_, 0);
v_isSharedCheck_5462_ = !lean_is_exclusive(v___x_5446_);
if (v_isSharedCheck_5462_ == 0)
{
v___x_5457_ = v___x_5446_;
v_isShared_5458_ = v_isSharedCheck_5462_;
goto v_resetjp_5456_;
}
else
{
lean_inc(v_a_5455_);
lean_dec(v___x_5446_);
v___x_5457_ = lean_box(0);
v_isShared_5458_ = v_isSharedCheck_5462_;
goto v_resetjp_5456_;
}
v_resetjp_5456_:
{
lean_object* v___x_5460_; 
if (v_isShared_5458_ == 0)
{
lean_ctor_set_tag(v___x_5457_, 0);
v___x_5460_ = v___x_5457_;
goto v_reusejp_5459_;
}
else
{
lean_object* v_reuseFailAlloc_5461_; 
v_reuseFailAlloc_5461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5461_, 0, v_a_5455_);
v___x_5460_ = v_reuseFailAlloc_5461_;
goto v_reusejp_5459_;
}
v_reusejp_5459_:
{
v___y_5411_ = v___x_5445_;
v___y_5412_ = v_a_5424_;
v_a_5413_ = v___x_5460_;
goto v___jp_5410_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5466_; lean_object* v___x_5468_; uint8_t v_isShared_5469_; uint8_t v_isSharedCheck_5473_; 
lean_del_object(v___x_5284_);
lean_dec(v_snd_5282_);
lean_dec_ref(v___x_5237_);
lean_dec(v_mvarId_5236_);
v_a_5466_ = lean_ctor_get(v___x_5381_, 0);
v_isSharedCheck_5473_ = !lean_is_exclusive(v___x_5381_);
if (v_isSharedCheck_5473_ == 0)
{
v___x_5468_ = v___x_5381_;
v_isShared_5469_ = v_isSharedCheck_5473_;
goto v_resetjp_5467_;
}
else
{
lean_inc(v_a_5466_);
lean_dec(v___x_5381_);
v___x_5468_ = lean_box(0);
v_isShared_5469_ = v_isSharedCheck_5473_;
goto v_resetjp_5467_;
}
v_resetjp_5467_:
{
lean_object* v___x_5471_; 
if (v_isShared_5469_ == 0)
{
v___x_5471_ = v___x_5468_;
goto v_reusejp_5470_;
}
else
{
lean_object* v_reuseFailAlloc_5472_; 
v_reuseFailAlloc_5472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5472_, 0, v_a_5466_);
v___x_5471_ = v_reuseFailAlloc_5472_;
goto v_reusejp_5470_;
}
v_reusejp_5470_:
{
return v___x_5471_;
}
}
}
}
}
else
{
lean_object* v_val_5474_; lean_object* v___x_5476_; 
lean_del_object(v___x_5284_);
lean_dec(v_snd_5282_);
lean_dec_ref(v___x_5237_);
lean_dec(v_mvarId_5236_);
v_val_5474_ = lean_ctor_get(v_fst_5281_, 0);
lean_inc(v_val_5474_);
lean_dec_ref_known(v_fst_5281_, 1);
if (v_isShared_5280_ == 0)
{
lean_ctor_set(v___x_5279_, 0, v_val_5474_);
v___x_5476_ = v___x_5279_;
goto v_reusejp_5475_;
}
else
{
lean_object* v_reuseFailAlloc_5477_; 
v_reuseFailAlloc_5477_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5477_, 0, v_val_5474_);
v___x_5476_ = v_reuseFailAlloc_5477_;
goto v_reusejp_5475_;
}
v_reusejp_5475_:
{
return v___x_5476_;
}
}
v___jp_5286_:
{
lean_object* v___x_5292_; 
v___x_5292_ = l_Lean_MVarId_assertHypotheses(v_mvarIdNew_5287_, v_snd_5282_, v___y_5288_, v___y_5289_, v___y_5290_, v___y_5291_);
if (lean_obj_tag(v___x_5292_) == 0)
{
lean_object* v_a_5293_; lean_object* v_snd_5294_; lean_object* v___x_5295_; 
v_a_5293_ = lean_ctor_get(v___x_5292_, 0);
lean_inc(v_a_5293_);
lean_dec_ref_known(v___x_5292_, 1);
v_snd_5294_ = lean_ctor_get(v_a_5293_, 1);
lean_inc(v_snd_5294_);
lean_dec(v_a_5293_);
v___x_5295_ = l_Lean_MVarId_tryClearMany(v_snd_5294_, v_fvarIdsToSimp_5238_, v___y_5288_, v___y_5289_, v___y_5290_, v___y_5291_);
if (lean_obj_tag(v___x_5295_) == 0)
{
lean_object* v_a_5296_; lean_object* v___x_5297_; 
v_a_5296_ = lean_ctor_get(v___x_5295_, 0);
lean_inc(v_a_5296_);
lean_dec_ref_known(v___x_5295_, 1);
v___x_5297_ = l_Lean_Meta_saveState___redArg(v___y_5289_, v___y_5291_);
if (lean_obj_tag(v___x_5297_) == 0)
{
lean_object* v_a_5298_; uint8_t v___x_5299_; lean_object* v___x_5300_; 
v_a_5298_ = lean_ctor_get(v___x_5297_, 0);
lean_inc(v_a_5298_);
lean_dec_ref_known(v___x_5297_, 1);
v___x_5299_ = 1;
lean_inc(v_a_5296_);
v___x_5300_ = l_Lean_MVarId_refl(v_a_5296_, v___x_5299_, v___y_5288_, v___y_5289_, v___y_5290_, v___y_5291_);
if (lean_obj_tag(v___x_5300_) == 0)
{
lean_object* v___x_5302_; uint8_t v_isShared_5303_; uint8_t v_isSharedCheck_5308_; 
lean_dec(v_a_5298_);
lean_dec(v_a_5296_);
v_isSharedCheck_5308_ = !lean_is_exclusive(v___x_5300_);
if (v_isSharedCheck_5308_ == 0)
{
lean_object* v_unused_5309_; 
v_unused_5309_ = lean_ctor_get(v___x_5300_, 0);
lean_dec(v_unused_5309_);
v___x_5302_ = v___x_5300_;
v_isShared_5303_ = v_isSharedCheck_5308_;
goto v_resetjp_5301_;
}
else
{
lean_dec(v___x_5300_);
v___x_5302_ = lean_box(0);
v_isShared_5303_ = v_isSharedCheck_5308_;
goto v_resetjp_5301_;
}
v_resetjp_5301_:
{
lean_object* v___x_5304_; lean_object* v___x_5306_; 
v___x_5304_ = lean_box(0);
if (v_isShared_5303_ == 0)
{
lean_ctor_set(v___x_5302_, 0, v___x_5304_);
v___x_5306_ = v___x_5302_;
goto v_reusejp_5305_;
}
else
{
lean_object* v_reuseFailAlloc_5307_; 
v_reuseFailAlloc_5307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5307_, 0, v___x_5304_);
v___x_5306_ = v_reuseFailAlloc_5307_;
goto v_reusejp_5305_;
}
v_reusejp_5305_:
{
return v___x_5306_;
}
}
}
else
{
lean_object* v_a_5310_; uint8_t v___x_5311_; 
v_a_5310_ = lean_ctor_get(v___x_5300_, 0);
lean_inc(v_a_5310_);
lean_dec_ref_known(v___x_5300_, 1);
v___x_5311_ = l_Lean_Exception_isInterrupt(v_a_5310_);
if (v___x_5311_ == 0)
{
uint8_t v___x_5312_; 
lean_inc(v_a_5310_);
v___x_5312_ = l_Lean_Exception_isRuntime(v_a_5310_);
v___y_5251_ = v_a_5310_;
v___y_5252_ = v_a_5298_;
v___y_5253_ = v_a_5296_;
v___y_5254_ = v___y_5291_;
v___y_5255_ = v___y_5289_;
v___y_5256_ = v___x_5312_;
goto v___jp_5250_;
}
else
{
v___y_5251_ = v_a_5310_;
v___y_5252_ = v_a_5298_;
v___y_5253_ = v_a_5296_;
v___y_5254_ = v___y_5291_;
v___y_5255_ = v___y_5289_;
v___y_5256_ = v___x_5311_;
goto v___jp_5250_;
}
}
}
else
{
lean_object* v_a_5313_; lean_object* v___x_5315_; uint8_t v_isShared_5316_; uint8_t v_isSharedCheck_5320_; 
lean_dec(v_a_5296_);
v_a_5313_ = lean_ctor_get(v___x_5297_, 0);
v_isSharedCheck_5320_ = !lean_is_exclusive(v___x_5297_);
if (v_isSharedCheck_5320_ == 0)
{
v___x_5315_ = v___x_5297_;
v_isShared_5316_ = v_isSharedCheck_5320_;
goto v_resetjp_5314_;
}
else
{
lean_inc(v_a_5313_);
lean_dec(v___x_5297_);
v___x_5315_ = lean_box(0);
v_isShared_5316_ = v_isSharedCheck_5320_;
goto v_resetjp_5314_;
}
v_resetjp_5314_:
{
lean_object* v___x_5318_; 
if (v_isShared_5316_ == 0)
{
v___x_5318_ = v___x_5315_;
goto v_reusejp_5317_;
}
else
{
lean_object* v_reuseFailAlloc_5319_; 
v_reuseFailAlloc_5319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5319_, 0, v_a_5313_);
v___x_5318_ = v_reuseFailAlloc_5319_;
goto v_reusejp_5317_;
}
v_reusejp_5317_:
{
return v___x_5318_;
}
}
}
}
else
{
lean_object* v_a_5321_; lean_object* v___x_5323_; uint8_t v_isShared_5324_; uint8_t v_isSharedCheck_5328_; 
v_a_5321_ = lean_ctor_get(v___x_5295_, 0);
v_isSharedCheck_5328_ = !lean_is_exclusive(v___x_5295_);
if (v_isSharedCheck_5328_ == 0)
{
v___x_5323_ = v___x_5295_;
v_isShared_5324_ = v_isSharedCheck_5328_;
goto v_resetjp_5322_;
}
else
{
lean_inc(v_a_5321_);
lean_dec(v___x_5295_);
v___x_5323_ = lean_box(0);
v_isShared_5324_ = v_isSharedCheck_5328_;
goto v_resetjp_5322_;
}
v_resetjp_5322_:
{
lean_object* v___x_5326_; 
if (v_isShared_5324_ == 0)
{
v___x_5326_ = v___x_5323_;
goto v_reusejp_5325_;
}
else
{
lean_object* v_reuseFailAlloc_5327_; 
v_reuseFailAlloc_5327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5327_, 0, v_a_5321_);
v___x_5326_ = v_reuseFailAlloc_5327_;
goto v_reusejp_5325_;
}
v_reusejp_5325_:
{
return v___x_5326_;
}
}
}
}
else
{
lean_object* v_a_5329_; lean_object* v___x_5331_; uint8_t v_isShared_5332_; uint8_t v_isSharedCheck_5336_; 
v_a_5329_ = lean_ctor_get(v___x_5292_, 0);
v_isSharedCheck_5336_ = !lean_is_exclusive(v___x_5292_);
if (v_isSharedCheck_5336_ == 0)
{
v___x_5331_ = v___x_5292_;
v_isShared_5332_ = v_isSharedCheck_5336_;
goto v_resetjp_5330_;
}
else
{
lean_inc(v_a_5329_);
lean_dec(v___x_5292_);
v___x_5331_ = lean_box(0);
v_isShared_5332_ = v_isSharedCheck_5336_;
goto v_resetjp_5330_;
}
v_resetjp_5330_:
{
lean_object* v___x_5334_; 
if (v_isShared_5332_ == 0)
{
v___x_5334_ = v___x_5331_;
goto v_reusejp_5333_;
}
else
{
lean_object* v_reuseFailAlloc_5335_; 
v_reuseFailAlloc_5335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5335_, 0, v_a_5329_);
v___x_5334_ = v_reuseFailAlloc_5335_;
goto v_reusejp_5333_;
}
v_reusejp_5333_:
{
return v___x_5334_;
}
}
}
}
v___jp_5337_:
{
if (lean_obj_tag(v___y_5338_) == 0)
{
lean_object* v_a_5339_; 
v_a_5339_ = lean_ctor_get(v___y_5338_, 0);
lean_inc(v_a_5339_);
lean_dec_ref_known(v___y_5338_, 1);
if (lean_obj_tag(v_a_5339_) == 0)
{
lean_dec_ref_known(v_a_5339_, 0);
v_mvarIdNew_5287_ = v_mvarId_5236_;
v___y_5288_ = v___y_5245_;
v___y_5289_ = v___y_5246_;
v___y_5290_ = v___y_5247_;
v___y_5291_ = v___y_5248_;
goto v___jp_5286_;
}
else
{
lean_object* v_e_x27_5340_; lean_object* v_proof_5341_; uint8_t v___x_5342_; 
v_e_x27_5340_ = lean_ctor_get(v_a_5339_, 0);
lean_inc_ref_n(v_e_x27_5340_, 2);
v_proof_5341_ = lean_ctor_get(v_a_5339_, 1);
lean_inc_ref(v_proof_5341_);
lean_dec_ref_known(v_a_5339_, 2);
v___x_5342_ = l_Lean_Expr_isTrue(v_e_x27_5340_);
if (v___x_5342_ == 0)
{
lean_object* v___x_5343_; 
v___x_5343_ = l_Lean_MVarId_replaceTargetEq(v_mvarId_5236_, v_e_x27_5340_, v_proof_5341_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_);
if (lean_obj_tag(v___x_5343_) == 0)
{
lean_object* v_a_5344_; 
v_a_5344_ = lean_ctor_get(v___x_5343_, 0);
lean_inc(v_a_5344_);
lean_dec_ref_known(v___x_5343_, 1);
v_mvarIdNew_5287_ = v_a_5344_;
v___y_5288_ = v___y_5245_;
v___y_5289_ = v___y_5246_;
v___y_5290_ = v___y_5247_;
v___y_5291_ = v___y_5248_;
goto v___jp_5286_;
}
else
{
lean_object* v_a_5345_; lean_object* v___x_5347_; uint8_t v_isShared_5348_; uint8_t v_isSharedCheck_5352_; 
lean_dec(v_snd_5282_);
v_a_5345_ = lean_ctor_get(v___x_5343_, 0);
v_isSharedCheck_5352_ = !lean_is_exclusive(v___x_5343_);
if (v_isSharedCheck_5352_ == 0)
{
v___x_5347_ = v___x_5343_;
v_isShared_5348_ = v_isSharedCheck_5352_;
goto v_resetjp_5346_;
}
else
{
lean_inc(v_a_5345_);
lean_dec(v___x_5343_);
v___x_5347_ = lean_box(0);
v_isShared_5348_ = v_isSharedCheck_5352_;
goto v_resetjp_5346_;
}
v_resetjp_5346_:
{
lean_object* v___x_5350_; 
if (v_isShared_5348_ == 0)
{
v___x_5350_ = v___x_5347_;
goto v_reusejp_5349_;
}
else
{
lean_object* v_reuseFailAlloc_5351_; 
v_reuseFailAlloc_5351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5351_, 0, v_a_5345_);
v___x_5350_ = v_reuseFailAlloc_5351_;
goto v_reusejp_5349_;
}
v_reusejp_5349_:
{
return v___x_5350_;
}
}
}
}
else
{
lean_object* v___x_5353_; 
lean_dec_ref(v_e_x27_5340_);
lean_dec(v_snd_5282_);
v___x_5353_ = l_Lean_Meta_mkOfEqTrue(v_proof_5341_, v___y_5245_, v___y_5246_, v___y_5247_, v___y_5248_);
if (lean_obj_tag(v___x_5353_) == 0)
{
lean_object* v_a_5354_; lean_object* v___x_5355_; lean_object* v___x_5357_; uint8_t v_isShared_5358_; uint8_t v_isSharedCheck_5363_; 
v_a_5354_ = lean_ctor_get(v___x_5353_, 0);
lean_inc(v_a_5354_);
lean_dec_ref_known(v___x_5353_, 1);
v___x_5355_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(v_mvarId_5236_, v_a_5354_, v___y_5246_);
v_isSharedCheck_5363_ = !lean_is_exclusive(v___x_5355_);
if (v_isSharedCheck_5363_ == 0)
{
lean_object* v_unused_5364_; 
v_unused_5364_ = lean_ctor_get(v___x_5355_, 0);
lean_dec(v_unused_5364_);
v___x_5357_ = v___x_5355_;
v_isShared_5358_ = v_isSharedCheck_5363_;
goto v_resetjp_5356_;
}
else
{
lean_dec(v___x_5355_);
v___x_5357_ = lean_box(0);
v_isShared_5358_ = v_isSharedCheck_5363_;
goto v_resetjp_5356_;
}
v_resetjp_5356_:
{
lean_object* v___x_5359_; lean_object* v___x_5361_; 
v___x_5359_ = lean_box(0);
if (v_isShared_5358_ == 0)
{
lean_ctor_set(v___x_5357_, 0, v___x_5359_);
v___x_5361_ = v___x_5357_;
goto v_reusejp_5360_;
}
else
{
lean_object* v_reuseFailAlloc_5362_; 
v_reuseFailAlloc_5362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5362_, 0, v___x_5359_);
v___x_5361_ = v_reuseFailAlloc_5362_;
goto v_reusejp_5360_;
}
v_reusejp_5360_:
{
return v___x_5361_;
}
}
}
else
{
lean_object* v_a_5365_; lean_object* v___x_5367_; uint8_t v_isShared_5368_; uint8_t v_isSharedCheck_5372_; 
lean_dec(v_mvarId_5236_);
v_a_5365_ = lean_ctor_get(v___x_5353_, 0);
v_isSharedCheck_5372_ = !lean_is_exclusive(v___x_5353_);
if (v_isSharedCheck_5372_ == 0)
{
v___x_5367_ = v___x_5353_;
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
else
{
lean_inc(v_a_5365_);
lean_dec(v___x_5353_);
v___x_5367_ = lean_box(0);
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
v_resetjp_5366_:
{
lean_object* v___x_5370_; 
if (v_isShared_5368_ == 0)
{
v___x_5370_ = v___x_5367_;
goto v_reusejp_5369_;
}
else
{
lean_object* v_reuseFailAlloc_5371_; 
v_reuseFailAlloc_5371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5371_, 0, v_a_5365_);
v___x_5370_ = v_reuseFailAlloc_5371_;
goto v_reusejp_5369_;
}
v_reusejp_5369_:
{
return v___x_5370_;
}
}
}
}
}
}
else
{
lean_object* v_a_5373_; lean_object* v___x_5375_; uint8_t v_isShared_5376_; uint8_t v_isSharedCheck_5380_; 
lean_dec(v_snd_5282_);
lean_dec(v_mvarId_5236_);
v_a_5373_ = lean_ctor_get(v___y_5338_, 0);
v_isSharedCheck_5380_ = !lean_is_exclusive(v___y_5338_);
if (v_isSharedCheck_5380_ == 0)
{
v___x_5375_ = v___y_5338_;
v_isShared_5376_ = v_isSharedCheck_5380_;
goto v_resetjp_5374_;
}
else
{
lean_inc(v_a_5373_);
lean_dec(v___y_5338_);
v___x_5375_ = lean_box(0);
v_isShared_5376_ = v_isSharedCheck_5380_;
goto v_resetjp_5374_;
}
v_resetjp_5374_:
{
lean_object* v___x_5378_; 
if (v_isShared_5376_ == 0)
{
v___x_5378_ = v___x_5375_;
goto v_reusejp_5377_;
}
else
{
lean_object* v_reuseFailAlloc_5379_; 
v_reuseFailAlloc_5379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5379_, 0, v_a_5373_);
v___x_5378_ = v_reuseFailAlloc_5379_;
goto v_reusejp_5377_;
}
v_reusejp_5377_:
{
return v___x_5378_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5480_; lean_object* v___x_5482_; uint8_t v_isShared_5483_; uint8_t v_isSharedCheck_5487_; 
lean_dec_ref(v___x_5237_);
lean_dec(v_mvarId_5236_);
v_a_5480_ = lean_ctor_get(v___x_5276_, 0);
v_isSharedCheck_5487_ = !lean_is_exclusive(v___x_5276_);
if (v_isSharedCheck_5487_ == 0)
{
v___x_5482_ = v___x_5276_;
v_isShared_5483_ = v_isSharedCheck_5487_;
goto v_resetjp_5481_;
}
else
{
lean_inc(v_a_5480_);
lean_dec(v___x_5276_);
v___x_5482_ = lean_box(0);
v_isShared_5483_ = v_isSharedCheck_5487_;
goto v_resetjp_5481_;
}
v_resetjp_5481_:
{
lean_object* v___x_5485_; 
if (v_isShared_5483_ == 0)
{
v___x_5485_ = v___x_5482_;
goto v_reusejp_5484_;
}
else
{
lean_object* v_reuseFailAlloc_5486_; 
v_reuseFailAlloc_5486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5486_, 0, v_a_5480_);
v___x_5485_ = v_reuseFailAlloc_5486_;
goto v_reusejp_5484_;
}
v_reusejp_5484_:
{
return v___x_5485_;
}
}
}
v___jp_5250_:
{
if (v___y_5256_ == 0)
{
lean_object* v___x_5257_; 
lean_dec_ref(v___y_5251_);
v___x_5257_ = l_Lean_Meta_SavedState_restore___redArg(v___y_5252_, v___y_5255_, v___y_5254_);
lean_dec_ref(v___y_5252_);
if (lean_obj_tag(v___x_5257_) == 0)
{
lean_object* v___x_5259_; uint8_t v_isShared_5260_; uint8_t v_isSharedCheck_5265_; 
v_isSharedCheck_5265_ = !lean_is_exclusive(v___x_5257_);
if (v_isSharedCheck_5265_ == 0)
{
lean_object* v_unused_5266_; 
v_unused_5266_ = lean_ctor_get(v___x_5257_, 0);
lean_dec(v_unused_5266_);
v___x_5259_ = v___x_5257_;
v_isShared_5260_ = v_isSharedCheck_5265_;
goto v_resetjp_5258_;
}
else
{
lean_dec(v___x_5257_);
v___x_5259_ = lean_box(0);
v_isShared_5260_ = v_isSharedCheck_5265_;
goto v_resetjp_5258_;
}
v_resetjp_5258_:
{
lean_object* v___x_5261_; lean_object* v___x_5263_; 
v___x_5261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5261_, 0, v___y_5253_);
if (v_isShared_5260_ == 0)
{
lean_ctor_set(v___x_5259_, 0, v___x_5261_);
v___x_5263_ = v___x_5259_;
goto v_reusejp_5262_;
}
else
{
lean_object* v_reuseFailAlloc_5264_; 
v_reuseFailAlloc_5264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5264_, 0, v___x_5261_);
v___x_5263_ = v_reuseFailAlloc_5264_;
goto v_reusejp_5262_;
}
v_reusejp_5262_:
{
return v___x_5263_;
}
}
}
else
{
lean_object* v_a_5267_; lean_object* v___x_5269_; uint8_t v_isShared_5270_; uint8_t v_isSharedCheck_5274_; 
lean_dec(v___y_5253_);
v_a_5267_ = lean_ctor_get(v___x_5257_, 0);
v_isSharedCheck_5274_ = !lean_is_exclusive(v___x_5257_);
if (v_isSharedCheck_5274_ == 0)
{
v___x_5269_ = v___x_5257_;
v_isShared_5270_ = v_isSharedCheck_5274_;
goto v_resetjp_5268_;
}
else
{
lean_inc(v_a_5267_);
lean_dec(v___x_5257_);
v___x_5269_ = lean_box(0);
v_isShared_5270_ = v_isSharedCheck_5274_;
goto v_resetjp_5268_;
}
v_resetjp_5268_:
{
lean_object* v___x_5272_; 
if (v_isShared_5270_ == 0)
{
v___x_5272_ = v___x_5269_;
goto v_reusejp_5271_;
}
else
{
lean_object* v_reuseFailAlloc_5273_; 
v_reuseFailAlloc_5273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5273_, 0, v_a_5267_);
v___x_5272_ = v_reuseFailAlloc_5273_;
goto v_reusejp_5271_;
}
v_reusejp_5271_:
{
return v___x_5272_;
}
}
}
}
else
{
lean_object* v___x_5275_; 
lean_dec(v___y_5253_);
lean_dec_ref(v___y_5252_);
v___x_5275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5275_, 0, v___y_5251_);
return v___x_5275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1___boxed(lean_object* v_mvarId_5488_, lean_object* v___x_5489_, lean_object* v_fvarIdsToSimp_5490_, lean_object* v_sz_5491_, lean_object* v___x_5492_, lean_object* v___x_5493_, lean_object* v_simplifyTarget_5494_, lean_object* v___y_5495_, lean_object* v___y_5496_, lean_object* v___y_5497_, lean_object* v___y_5498_, lean_object* v___y_5499_, lean_object* v___y_5500_, lean_object* v___y_5501_){
_start:
{
size_t v_sz_boxed_5502_; size_t v___x_53511__boxed_5503_; uint8_t v_simplifyTarget_boxed_5504_; lean_object* v_res_5505_; 
v_sz_boxed_5502_ = lean_unbox_usize(v_sz_5491_);
lean_dec(v_sz_5491_);
v___x_53511__boxed_5503_ = lean_unbox_usize(v___x_5492_);
lean_dec(v___x_5492_);
v_simplifyTarget_boxed_5504_ = lean_unbox(v_simplifyTarget_5494_);
v_res_5505_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1(v_mvarId_5488_, v___x_5489_, v_fvarIdsToSimp_5490_, v_sz_boxed_5502_, v___x_53511__boxed_5503_, v___x_5493_, v_simplifyTarget_boxed_5504_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_, v___y_5499_, v___y_5500_);
lean_dec(v___y_5500_);
lean_dec_ref(v___y_5499_);
lean_dec(v___y_5498_);
lean_dec_ref(v___y_5497_);
lean_dec(v___y_5496_);
lean_dec_ref(v___y_5495_);
lean_dec_ref(v_fvarIdsToSimp_5490_);
return v_res_5505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore(lean_object* v_mvarId_5513_, uint8_t v_simplifyTarget_5514_, lean_object* v_fvarIdsToSimp_5515_, lean_object* v_a_5516_, lean_object* v_a_5517_, lean_object* v_a_5518_, lean_object* v_a_5519_, lean_object* v_a_5520_, lean_object* v_a_5521_){
_start:
{
lean_object* v_options_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; size_t v_sz_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___f_5533_; lean_object* v___x_5534_; 
v_options_5523_ = lean_ctor_get(v_a_5520_, 2);
v___x_5524_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_5525_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_5523_, v___x_5524_);
v___x_5526_ = lean_unsigned_to_nat(2u);
v___x_5527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5527_, 0, v___x_5525_);
lean_ctor_set(v___x_5527_, 1, v___x_5526_);
v___x_5528_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___closed__1));
v_sz_5529_ = lean_array_size(v_fvarIdsToSimp_5515_);
v___x_5530_ = lean_box_usize(v_sz_5529_);
v___x_5531_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___boxed__const__1));
v___x_5532_ = lean_box(v_simplifyTarget_5514_);
lean_inc(v_mvarId_5513_);
v___f_5533_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1___boxed), 14, 7);
lean_closure_set(v___f_5533_, 0, v_mvarId_5513_);
lean_closure_set(v___f_5533_, 1, v___x_5527_);
lean_closure_set(v___f_5533_, 2, v_fvarIdsToSimp_5515_);
lean_closure_set(v___f_5533_, 3, v___x_5530_);
lean_closure_set(v___f_5533_, 4, v___x_5531_);
lean_closure_set(v___f_5533_, 5, v___x_5528_);
lean_closure_set(v___f_5533_, 6, v___x_5532_);
v___x_5534_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg(v_mvarId_5513_, v___f_5533_, v_a_5516_, v_a_5517_, v_a_5518_, v_a_5519_, v_a_5520_, v_a_5521_);
return v___x_5534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___boxed(lean_object* v_mvarId_5535_, lean_object* v_simplifyTarget_5536_, lean_object* v_fvarIdsToSimp_5537_, lean_object* v_a_5538_, lean_object* v_a_5539_, lean_object* v_a_5540_, lean_object* v_a_5541_, lean_object* v_a_5542_, lean_object* v_a_5543_, lean_object* v_a_5544_){
_start:
{
uint8_t v_simplifyTarget_boxed_5545_; lean_object* v_res_5546_; 
v_simplifyTarget_boxed_5545_ = lean_unbox(v_simplifyTarget_5536_);
v_res_5546_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore(v_mvarId_5535_, v_simplifyTarget_boxed_5545_, v_fvarIdsToSimp_5537_, v_a_5538_, v_a_5539_, v_a_5540_, v_a_5541_, v_a_5542_, v_a_5543_);
lean_dec(v_a_5543_);
lean_dec_ref(v_a_5542_);
lean_dec(v_a_5541_);
lean_dec_ref(v_a_5540_);
lean_dec(v_a_5539_);
lean_dec_ref(v_a_5538_);
return v_res_5546_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0(lean_object* v_mvarId_5547_, lean_object* v_val_5548_, lean_object* v___y_5549_, lean_object* v___y_5550_, lean_object* v___y_5551_, lean_object* v___y_5552_, lean_object* v___y_5553_, lean_object* v___y_5554_){
_start:
{
lean_object* v___x_5556_; 
v___x_5556_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(v_mvarId_5547_, v_val_5548_, v___y_5552_);
return v___x_5556_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___boxed(lean_object* v_mvarId_5557_, lean_object* v_val_5558_, lean_object* v___y_5559_, lean_object* v___y_5560_, lean_object* v___y_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_){
_start:
{
lean_object* v_res_5566_; 
v_res_5566_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0(v_mvarId_5557_, v_val_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_);
lean_dec(v___y_5564_);
lean_dec_ref(v___y_5563_);
lean_dec(v___y_5562_);
lean_dec_ref(v___y_5561_);
lean_dec(v___y_5560_);
lean_dec_ref(v___y_5559_);
return v_res_5566_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4(lean_object* v_00_u03b1_5567_, lean_object* v_x_5568_, lean_object* v___y_5569_, lean_object* v___y_5570_, lean_object* v___y_5571_, lean_object* v___y_5572_, lean_object* v___y_5573_, lean_object* v___y_5574_){
_start:
{
lean_object* v___x_5576_; 
v___x_5576_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(v_x_5568_);
return v___x_5576_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___boxed(lean_object* v_00_u03b1_5577_, lean_object* v_x_5578_, lean_object* v___y_5579_, lean_object* v___y_5580_, lean_object* v___y_5581_, lean_object* v___y_5582_, lean_object* v___y_5583_, lean_object* v___y_5584_, lean_object* v___y_5585_){
_start:
{
lean_object* v_res_5586_; 
v_res_5586_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4(v_00_u03b1_5577_, v_x_5578_, v___y_5579_, v___y_5580_, v___y_5581_, v___y_5582_, v___y_5583_, v___y_5584_);
lean_dec(v___y_5584_);
lean_dec_ref(v___y_5583_);
lean_dec(v___y_5582_);
lean_dec_ref(v___y_5581_);
lean_dec(v___y_5580_);
lean_dec_ref(v___y_5579_);
return v_res_5586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0(lean_object* v_00_u03b2_5587_, lean_object* v_x_5588_, lean_object* v_x_5589_, lean_object* v_x_5590_){
_start:
{
lean_object* v___x_5591_; 
v___x_5591_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0___redArg(v_x_5588_, v_x_5589_, v_x_5590_);
return v___x_5591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3(lean_object* v_oldTraces_5592_, lean_object* v_data_5593_, lean_object* v_ref_5594_, lean_object* v_msg_5595_, lean_object* v___y_5596_, lean_object* v___y_5597_, lean_object* v___y_5598_, lean_object* v___y_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_){
_start:
{
lean_object* v___x_5603_; 
v___x_5603_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg(v_oldTraces_5592_, v_data_5593_, v_ref_5594_, v_msg_5595_, v___y_5598_, v___y_5599_, v___y_5600_, v___y_5601_);
return v___x_5603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___boxed(lean_object* v_oldTraces_5604_, lean_object* v_data_5605_, lean_object* v_ref_5606_, lean_object* v_msg_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_, lean_object* v___y_5610_, lean_object* v___y_5611_, lean_object* v___y_5612_, lean_object* v___y_5613_, lean_object* v___y_5614_){
_start:
{
lean_object* v_res_5615_; 
v_res_5615_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3(v_oldTraces_5604_, v_data_5605_, v_ref_5606_, v_msg_5607_, v___y_5608_, v___y_5609_, v___y_5610_, v___y_5611_, v___y_5612_, v___y_5613_);
lean_dec(v___y_5613_);
lean_dec_ref(v___y_5612_);
lean_dec(v___y_5611_);
lean_dec_ref(v___y_5610_);
lean_dec(v___y_5609_);
lean_dec_ref(v___y_5608_);
return v_res_5615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_5616_, lean_object* v_x_5617_, size_t v_x_5618_, size_t v_x_5619_, lean_object* v_x_5620_, lean_object* v_x_5621_){
_start:
{
lean_object* v___x_5622_; 
v___x_5622_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_x_5617_, v_x_5618_, v_x_5619_, v_x_5620_, v_x_5621_);
return v___x_5622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_5623_, lean_object* v_x_5624_, lean_object* v_x_5625_, lean_object* v_x_5626_, lean_object* v_x_5627_, lean_object* v_x_5628_){
_start:
{
size_t v_x_54144__boxed_5629_; size_t v_x_54145__boxed_5630_; lean_object* v_res_5631_; 
v_x_54144__boxed_5629_ = lean_unbox_usize(v_x_5625_);
lean_dec(v_x_5625_);
v_x_54145__boxed_5630_ = lean_unbox_usize(v_x_5626_);
lean_dec(v_x_5626_);
v_res_5631_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3(v_00_u03b2_5623_, v_x_5624_, v_x_54144__boxed_5629_, v_x_54145__boxed_5630_, v_x_5627_, v_x_5628_);
return v_res_5631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7(lean_object* v_00_u03b2_5632_, lean_object* v_n_5633_, lean_object* v_k_5634_, lean_object* v_v_5635_){
_start:
{
lean_object* v___x_5636_; 
v___x_5636_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7___redArg(v_n_5633_, v_k_5634_, v_v_5635_);
return v___x_5636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8(lean_object* v_00_u03b2_5637_, size_t v_depth_5638_, lean_object* v_keys_5639_, lean_object* v_vals_5640_, lean_object* v_heq_5641_, lean_object* v_i_5642_, lean_object* v_entries_5643_){
_start:
{
lean_object* v___x_5644_; 
v___x_5644_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg(v_depth_5638_, v_keys_5639_, v_vals_5640_, v_i_5642_, v_entries_5643_);
return v___x_5644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___boxed(lean_object* v_00_u03b2_5645_, lean_object* v_depth_5646_, lean_object* v_keys_5647_, lean_object* v_vals_5648_, lean_object* v_heq_5649_, lean_object* v_i_5650_, lean_object* v_entries_5651_){
_start:
{
size_t v_depth_boxed_5652_; lean_object* v_res_5653_; 
v_depth_boxed_5652_ = lean_unbox_usize(v_depth_5646_);
lean_dec(v_depth_5646_);
v_res_5653_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8(v_00_u03b2_5645_, v_depth_boxed_5652_, v_keys_5647_, v_vals_5648_, v_heq_5649_, v_i_5650_, v_entries_5651_);
lean_dec_ref(v_vals_5648_);
lean_dec_ref(v_keys_5647_);
return v_res_5653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9(lean_object* v_00_u03b2_5654_, lean_object* v_x_5655_, lean_object* v_x_5656_, lean_object* v_x_5657_, lean_object* v_x_5658_){
_start:
{
lean_object* v___x_5659_; 
v___x_5659_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_x_5655_, v_x_5656_, v_x_5657_, v_x_5658_);
return v___x_5659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0(lean_object* v_mvarId_5660_, uint8_t v_simplifyTarget_5661_, lean_object* v_fvarIdsToSimp_5662_, lean_object* v___y_5663_, lean_object* v___y_5664_, lean_object* v___y_5665_, lean_object* v___y_5666_, lean_object* v___y_5667_, lean_object* v___y_5668_){
_start:
{
lean_object* v___x_5670_; 
v___x_5670_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_5660_, v___y_5663_, v___y_5664_, v___y_5665_, v___y_5666_, v___y_5667_, v___y_5668_);
if (lean_obj_tag(v___x_5670_) == 0)
{
lean_object* v_a_5671_; lean_object* v___x_5672_; 
v_a_5671_ = lean_ctor_get(v___x_5670_, 0);
lean_inc(v_a_5671_);
lean_dec_ref_known(v___x_5670_, 1);
v___x_5672_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore(v_a_5671_, v_simplifyTarget_5661_, v_fvarIdsToSimp_5662_, v___y_5663_, v___y_5664_, v___y_5665_, v___y_5666_, v___y_5667_, v___y_5668_);
return v___x_5672_;
}
else
{
lean_object* v_a_5673_; lean_object* v___x_5675_; uint8_t v_isShared_5676_; uint8_t v_isSharedCheck_5680_; 
lean_dec_ref(v_fvarIdsToSimp_5662_);
v_a_5673_ = lean_ctor_get(v___x_5670_, 0);
v_isSharedCheck_5680_ = !lean_is_exclusive(v___x_5670_);
if (v_isSharedCheck_5680_ == 0)
{
v___x_5675_ = v___x_5670_;
v_isShared_5676_ = v_isSharedCheck_5680_;
goto v_resetjp_5674_;
}
else
{
lean_inc(v_a_5673_);
lean_dec(v___x_5670_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___boxed(lean_object* v_mvarId_5681_, lean_object* v_simplifyTarget_5682_, lean_object* v_fvarIdsToSimp_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_, lean_object* v___y_5686_, lean_object* v___y_5687_, lean_object* v___y_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_){
_start:
{
uint8_t v_simplifyTarget_boxed_5691_; lean_object* v_res_5692_; 
v_simplifyTarget_boxed_5691_ = lean_unbox(v_simplifyTarget_5682_);
v_res_5692_ = l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0(v_mvarId_5681_, v_simplifyTarget_boxed_5691_, v_fvarIdsToSimp_5683_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_);
lean_dec(v___y_5689_);
lean_dec_ref(v___y_5688_);
lean_dec(v___y_5687_);
lean_dec_ref(v___y_5686_);
lean_dec(v___y_5685_);
lean_dec_ref(v___y_5684_);
return v_res_5692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal(lean_object* v_mvarId_5693_, uint8_t v_simplifyTarget_5694_, lean_object* v_fvarIdsToSimp_5695_, lean_object* v_a_5696_, lean_object* v_a_5697_, lean_object* v_a_5698_, lean_object* v_a_5699_){
_start:
{
lean_object* v___x_5701_; lean_object* v___f_5702_; lean_object* v___x_5703_; 
v___x_5701_ = lean_box(v_simplifyTarget_5694_);
v___f_5702_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5702_, 0, v_mvarId_5693_);
lean_closure_set(v___f_5702_, 1, v___x_5701_);
lean_closure_set(v___f_5702_, 2, v_fvarIdsToSimp_5695_);
v___x_5703_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_5702_, v_a_5696_, v_a_5697_, v_a_5698_, v_a_5699_);
return v___x_5703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___boxed(lean_object* v_mvarId_5704_, lean_object* v_simplifyTarget_5705_, lean_object* v_fvarIdsToSimp_5706_, lean_object* v_a_5707_, lean_object* v_a_5708_, lean_object* v_a_5709_, lean_object* v_a_5710_, lean_object* v_a_5711_){
_start:
{
uint8_t v_simplifyTarget_boxed_5712_; lean_object* v_res_5713_; 
v_simplifyTarget_boxed_5712_ = lean_unbox(v_simplifyTarget_5705_);
v_res_5713_ = l_Lean_Meta_Tactic_Cbv_cbvGoal(v_mvarId_5704_, v_simplifyTarget_boxed_5712_, v_fvarIdsToSimp_5706_, v_a_5707_, v_a_5708_, v_a_5709_, v_a_5710_);
lean_dec(v_a_5710_);
lean_dec_ref(v_a_5709_);
lean_dec(v_a_5708_);
lean_dec_ref(v_a_5707_);
return v_res_5713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0(lean_object* v_a_5714_, uint8_t v___x_5715_, lean_object* v___y_5716_, lean_object* v___y_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_){
_start:
{
lean_object* v___x_5723_; 
v___x_5723_ = l_Lean_MVarId_refl(v_a_5714_, v___x_5715_, v___y_5718_, v___y_5719_, v___y_5720_, v___y_5721_);
return v___x_5723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed(lean_object* v_a_5724_, lean_object* v___x_5725_, lean_object* v___y_5726_, lean_object* v___y_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_, lean_object* v___y_5730_, lean_object* v___y_5731_, lean_object* v___y_5732_){
_start:
{
uint8_t v___x_25154__boxed_5733_; lean_object* v_res_5734_; 
v___x_25154__boxed_5733_ = lean_unbox(v___x_5725_);
v_res_5734_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0(v_a_5724_, v___x_25154__boxed_5733_, v___y_5726_, v___y_5727_, v___y_5728_, v___y_5729_, v___y_5730_, v___y_5731_);
lean_dec(v___y_5731_);
lean_dec_ref(v___y_5730_);
lean_dec(v___y_5729_);
lean_dec_ref(v___y_5728_);
lean_dec(v___y_5727_);
lean_dec_ref(v___y_5726_);
return v_res_5734_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(lean_object* v_cls_5735_, lean_object* v_msg_5736_, lean_object* v___y_5737_, lean_object* v___y_5738_, lean_object* v___y_5739_, lean_object* v___y_5740_){
_start:
{
lean_object* v_ref_5742_; lean_object* v___x_5743_; lean_object* v_a_5744_; lean_object* v___x_5746_; uint8_t v_isShared_5747_; uint8_t v_isSharedCheck_5788_; 
v_ref_5742_ = lean_ctor_get(v___y_5739_, 5);
v___x_5743_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_);
v_a_5744_ = lean_ctor_get(v___x_5743_, 0);
v_isSharedCheck_5788_ = !lean_is_exclusive(v___x_5743_);
if (v_isSharedCheck_5788_ == 0)
{
v___x_5746_ = v___x_5743_;
v_isShared_5747_ = v_isSharedCheck_5788_;
goto v_resetjp_5745_;
}
else
{
lean_inc(v_a_5744_);
lean_dec(v___x_5743_);
v___x_5746_ = lean_box(0);
v_isShared_5747_ = v_isSharedCheck_5788_;
goto v_resetjp_5745_;
}
v_resetjp_5745_:
{
lean_object* v___x_5748_; lean_object* v_traceState_5749_; lean_object* v_env_5750_; lean_object* v_nextMacroScope_5751_; lean_object* v_ngen_5752_; lean_object* v_auxDeclNGen_5753_; lean_object* v_cache_5754_; lean_object* v_messages_5755_; lean_object* v_infoState_5756_; lean_object* v_snapshotTasks_5757_; lean_object* v___x_5759_; uint8_t v_isShared_5760_; uint8_t v_isSharedCheck_5787_; 
v___x_5748_ = lean_st_ref_take(v___y_5740_);
v_traceState_5749_ = lean_ctor_get(v___x_5748_, 4);
v_env_5750_ = lean_ctor_get(v___x_5748_, 0);
v_nextMacroScope_5751_ = lean_ctor_get(v___x_5748_, 1);
v_ngen_5752_ = lean_ctor_get(v___x_5748_, 2);
v_auxDeclNGen_5753_ = lean_ctor_get(v___x_5748_, 3);
v_cache_5754_ = lean_ctor_get(v___x_5748_, 5);
v_messages_5755_ = lean_ctor_get(v___x_5748_, 6);
v_infoState_5756_ = lean_ctor_get(v___x_5748_, 7);
v_snapshotTasks_5757_ = lean_ctor_get(v___x_5748_, 8);
v_isSharedCheck_5787_ = !lean_is_exclusive(v___x_5748_);
if (v_isSharedCheck_5787_ == 0)
{
v___x_5759_ = v___x_5748_;
v_isShared_5760_ = v_isSharedCheck_5787_;
goto v_resetjp_5758_;
}
else
{
lean_inc(v_snapshotTasks_5757_);
lean_inc(v_infoState_5756_);
lean_inc(v_messages_5755_);
lean_inc(v_cache_5754_);
lean_inc(v_traceState_5749_);
lean_inc(v_auxDeclNGen_5753_);
lean_inc(v_ngen_5752_);
lean_inc(v_nextMacroScope_5751_);
lean_inc(v_env_5750_);
lean_dec(v___x_5748_);
v___x_5759_ = lean_box(0);
v_isShared_5760_ = v_isSharedCheck_5787_;
goto v_resetjp_5758_;
}
v_resetjp_5758_:
{
uint64_t v_tid_5761_; lean_object* v_traces_5762_; lean_object* v___x_5764_; uint8_t v_isShared_5765_; uint8_t v_isSharedCheck_5786_; 
v_tid_5761_ = lean_ctor_get_uint64(v_traceState_5749_, sizeof(void*)*1);
v_traces_5762_ = lean_ctor_get(v_traceState_5749_, 0);
v_isSharedCheck_5786_ = !lean_is_exclusive(v_traceState_5749_);
if (v_isSharedCheck_5786_ == 0)
{
v___x_5764_ = v_traceState_5749_;
v_isShared_5765_ = v_isSharedCheck_5786_;
goto v_resetjp_5763_;
}
else
{
lean_inc(v_traces_5762_);
lean_dec(v_traceState_5749_);
v___x_5764_ = lean_box(0);
v_isShared_5765_ = v_isSharedCheck_5786_;
goto v_resetjp_5763_;
}
v_resetjp_5763_:
{
lean_object* v___x_5766_; double v___x_5767_; uint8_t v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; lean_object* v___x_5771_; lean_object* v___x_5772_; lean_object* v___x_5773_; lean_object* v___x_5774_; lean_object* v___x_5776_; 
v___x_5766_ = lean_box(0);
v___x_5767_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
v___x_5768_ = 0;
v___x_5769_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_5770_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5770_, 0, v_cls_5735_);
lean_ctor_set(v___x_5770_, 1, v___x_5766_);
lean_ctor_set(v___x_5770_, 2, v___x_5769_);
lean_ctor_set_float(v___x_5770_, sizeof(void*)*3, v___x_5767_);
lean_ctor_set_float(v___x_5770_, sizeof(void*)*3 + 8, v___x_5767_);
lean_ctor_set_uint8(v___x_5770_, sizeof(void*)*3 + 16, v___x_5768_);
v___x_5771_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__2));
v___x_5772_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5772_, 0, v___x_5770_);
lean_ctor_set(v___x_5772_, 1, v_a_5744_);
lean_ctor_set(v___x_5772_, 2, v___x_5771_);
lean_inc(v_ref_5742_);
v___x_5773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5773_, 0, v_ref_5742_);
lean_ctor_set(v___x_5773_, 1, v___x_5772_);
v___x_5774_ = l_Lean_PersistentArray_push___redArg(v_traces_5762_, v___x_5773_);
if (v_isShared_5765_ == 0)
{
lean_ctor_set(v___x_5764_, 0, v___x_5774_);
v___x_5776_ = v___x_5764_;
goto v_reusejp_5775_;
}
else
{
lean_object* v_reuseFailAlloc_5785_; 
v_reuseFailAlloc_5785_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5785_, 0, v___x_5774_);
lean_ctor_set_uint64(v_reuseFailAlloc_5785_, sizeof(void*)*1, v_tid_5761_);
v___x_5776_ = v_reuseFailAlloc_5785_;
goto v_reusejp_5775_;
}
v_reusejp_5775_:
{
lean_object* v___x_5778_; 
if (v_isShared_5760_ == 0)
{
lean_ctor_set(v___x_5759_, 4, v___x_5776_);
v___x_5778_ = v___x_5759_;
goto v_reusejp_5777_;
}
else
{
lean_object* v_reuseFailAlloc_5784_; 
v_reuseFailAlloc_5784_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5784_, 0, v_env_5750_);
lean_ctor_set(v_reuseFailAlloc_5784_, 1, v_nextMacroScope_5751_);
lean_ctor_set(v_reuseFailAlloc_5784_, 2, v_ngen_5752_);
lean_ctor_set(v_reuseFailAlloc_5784_, 3, v_auxDeclNGen_5753_);
lean_ctor_set(v_reuseFailAlloc_5784_, 4, v___x_5776_);
lean_ctor_set(v_reuseFailAlloc_5784_, 5, v_cache_5754_);
lean_ctor_set(v_reuseFailAlloc_5784_, 6, v_messages_5755_);
lean_ctor_set(v_reuseFailAlloc_5784_, 7, v_infoState_5756_);
lean_ctor_set(v_reuseFailAlloc_5784_, 8, v_snapshotTasks_5757_);
v___x_5778_ = v_reuseFailAlloc_5784_;
goto v_reusejp_5777_;
}
v_reusejp_5777_:
{
lean_object* v___x_5779_; lean_object* v___x_5780_; lean_object* v___x_5782_; 
v___x_5779_ = lean_st_ref_set(v___y_5740_, v___x_5778_);
v___x_5780_ = lean_box(0);
if (v_isShared_5747_ == 0)
{
lean_ctor_set(v___x_5746_, 0, v___x_5780_);
v___x_5782_ = v___x_5746_;
goto v_reusejp_5781_;
}
else
{
lean_object* v_reuseFailAlloc_5783_; 
v_reuseFailAlloc_5783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5783_, 0, v___x_5780_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg___boxed(lean_object* v_cls_5789_, lean_object* v_msg_5790_, lean_object* v___y_5791_, lean_object* v___y_5792_, lean_object* v___y_5793_, lean_object* v___y_5794_, lean_object* v___y_5795_){
_start:
{
lean_object* v_res_5796_; 
v_res_5796_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_5789_, v_msg_5790_, v___y_5791_, v___y_5792_, v___y_5793_, v___y_5794_);
lean_dec(v___y_5794_);
lean_dec_ref(v___y_5793_);
lean_dec(v___y_5792_);
lean_dec_ref(v___y_5791_);
return v_res_5796_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(lean_object* v_msg_5797_, lean_object* v___y_5798_, lean_object* v___y_5799_, lean_object* v___y_5800_, lean_object* v___y_5801_){
_start:
{
lean_object* v_ref_5803_; lean_object* v___x_5804_; lean_object* v_a_5805_; lean_object* v___x_5807_; uint8_t v_isShared_5808_; uint8_t v_isSharedCheck_5813_; 
v_ref_5803_ = lean_ctor_get(v___y_5800_, 5);
v___x_5804_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_5797_, v___y_5798_, v___y_5799_, v___y_5800_, v___y_5801_);
v_a_5805_ = lean_ctor_get(v___x_5804_, 0);
v_isSharedCheck_5813_ = !lean_is_exclusive(v___x_5804_);
if (v_isSharedCheck_5813_ == 0)
{
v___x_5807_ = v___x_5804_;
v_isShared_5808_ = v_isSharedCheck_5813_;
goto v_resetjp_5806_;
}
else
{
lean_inc(v_a_5805_);
lean_dec(v___x_5804_);
v___x_5807_ = lean_box(0);
v_isShared_5808_ = v_isSharedCheck_5813_;
goto v_resetjp_5806_;
}
v_resetjp_5806_:
{
lean_object* v___x_5809_; lean_object* v___x_5811_; 
lean_inc(v_ref_5803_);
v___x_5809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5809_, 0, v_ref_5803_);
lean_ctor_set(v___x_5809_, 1, v_a_5805_);
if (v_isShared_5808_ == 0)
{
lean_ctor_set_tag(v___x_5807_, 1);
lean_ctor_set(v___x_5807_, 0, v___x_5809_);
v___x_5811_ = v___x_5807_;
goto v_reusejp_5810_;
}
else
{
lean_object* v_reuseFailAlloc_5812_; 
v_reuseFailAlloc_5812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5812_, 0, v___x_5809_);
v___x_5811_ = v_reuseFailAlloc_5812_;
goto v_reusejp_5810_;
}
v_reusejp_5810_:
{
return v___x_5811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg___boxed(lean_object* v_msg_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_){
_start:
{
lean_object* v_res_5820_; 
v_res_5820_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v_msg_5814_, v___y_5815_, v___y_5816_, v___y_5817_, v___y_5818_);
lean_dec(v___y_5818_);
lean_dec_ref(v___y_5817_);
lean_dec(v___y_5816_);
lean_dec_ref(v___y_5815_);
return v_res_5820_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5822_; lean_object* v___x_5823_; 
v___x_5822_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__0));
v___x_5823_ = l_Lean_stringToMessageData(v___x_5822_);
return v___x_5823_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3(void){
_start:
{
lean_object* v___x_5825_; lean_object* v___x_5826_; 
v___x_5825_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__2));
v___x_5826_ = l_Lean_stringToMessageData(v___x_5825_);
return v___x_5826_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6(void){
_start:
{
lean_object* v___x_5830_; lean_object* v___x_5831_; 
v___x_5830_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__5));
v___x_5831_ = l_Lean_stringToMessageData(v___x_5830_);
return v___x_5831_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8(void){
_start:
{
lean_object* v___x_5833_; lean_object* v___x_5834_; 
v___x_5833_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__7));
v___x_5834_ = l_Lean_stringToMessageData(v___x_5833_);
return v___x_5834_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1(lean_object* v_m_5835_, lean_object* v___x_5836_, lean_object* v_cls_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_, lean_object* v___y_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_){
_start:
{
lean_object* v_e_5846_; lean_object* v_onTrue_5847_; lean_object* v___y_5848_; lean_object* v___y_5849_; lean_object* v___y_5850_; lean_object* v___y_5851_; lean_object* v___y_5852_; lean_object* v___y_5853_; lean_object* v___x_5883_; 
v___x_5883_ = l_Lean_Meta_Sym_preprocessMVar(v_m_5835_, v___y_5838_, v___y_5839_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_);
if (lean_obj_tag(v___x_5883_) == 0)
{
lean_object* v_a_5884_; lean_object* v___x_5885_; 
v_a_5884_ = lean_ctor_get(v___x_5883_, 0);
lean_inc_n(v_a_5884_, 2);
lean_dec_ref_known(v___x_5883_, 1);
v___x_5885_ = l_Lean_MVarId_getType(v_a_5884_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_);
if (lean_obj_tag(v___x_5885_) == 0)
{
lean_object* v_a_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; uint8_t v___x_5889_; 
v_a_5886_ = lean_ctor_get(v___x_5885_, 0);
lean_inc(v_a_5886_);
lean_dec_ref_known(v___x_5885_, 1);
v___x_5887_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4));
v___x_5888_ = lean_unsigned_to_nat(3u);
v___x_5889_ = l_Lean_Expr_isAppOfArity(v_a_5886_, v___x_5887_, v___x_5888_);
if (v___x_5889_ == 0)
{
lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; 
lean_dec(v_a_5884_);
lean_dec(v_cls_5837_);
lean_dec_ref(v___x_5836_);
v___x_5890_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6);
v___x_5891_ = l_Lean_indentExpr(v_a_5886_);
v___x_5892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5892_, 0, v___x_5890_);
lean_ctor_set(v___x_5892_, 1, v___x_5891_);
v___x_5893_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5892_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_);
return v___x_5893_;
}
else
{
lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; 
v___x_5894_ = l_Lean_Expr_appFn_x21(v_a_5886_);
lean_dec(v_a_5886_);
v___x_5895_ = l_Lean_Expr_appArg_x21(v___x_5894_);
lean_dec_ref(v___x_5894_);
lean_inc_ref(v___x_5895_);
v___x_5896_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5895_, v___x_5836_, v___y_5838_, v___y_5839_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_);
if (lean_obj_tag(v___x_5896_) == 0)
{
lean_object* v_options_5897_; lean_object* v_a_5898_; lean_object* v_inheritedTraceOptions_5899_; uint8_t v_hasTrace_5900_; lean_object* v___x_5901_; lean_object* v___f_5902_; lean_object* v___y_5904_; lean_object* v___y_5905_; lean_object* v___y_5906_; lean_object* v___y_5907_; lean_object* v___y_5908_; lean_object* v___y_5909_; 
v_options_5897_ = lean_ctor_get(v___y_5842_, 2);
v_a_5898_ = lean_ctor_get(v___x_5896_, 0);
lean_inc(v_a_5898_);
lean_dec_ref_known(v___x_5896_, 1);
v_inheritedTraceOptions_5899_ = lean_ctor_get(v___y_5842_, 13);
v_hasTrace_5900_ = lean_ctor_get_uint8(v_options_5897_, sizeof(void*)*1);
v___x_5901_ = lean_box(v___x_5889_);
lean_inc(v_a_5884_);
v___f_5902_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5902_, 0, v_a_5884_);
lean_closure_set(v___f_5902_, 1, v___x_5901_);
if (v_hasTrace_5900_ == 0)
{
lean_dec(v_cls_5837_);
v___y_5904_ = v___y_5838_;
v___y_5905_ = v___y_5839_;
v___y_5906_ = v___y_5840_;
v___y_5907_ = v___y_5841_;
v___y_5908_ = v___y_5842_;
v___y_5909_ = v___y_5843_;
goto v___jp_5903_;
}
else
{
lean_object* v___x_5913_; lean_object* v___x_5914_; uint8_t v___x_5915_; 
v___x_5913_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
lean_inc(v_cls_5837_);
v___x_5914_ = l_Lean_Name_append(v___x_5913_, v_cls_5837_);
v___x_5915_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5899_, v_options_5897_, v___x_5914_);
lean_dec(v___x_5914_);
if (v___x_5915_ == 0)
{
lean_dec(v_cls_5837_);
v___y_5904_ = v___y_5838_;
v___y_5905_ = v___y_5839_;
v___y_5906_ = v___y_5840_;
v___y_5907_ = v___y_5841_;
v___y_5908_ = v___y_5842_;
v___y_5909_ = v___y_5843_;
goto v___jp_5903_;
}
else
{
lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; 
v___x_5916_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8);
lean_inc_ref(v___x_5895_);
v___x_5917_ = l_Lean_indentExpr(v___x_5895_);
v___x_5918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5918_, 0, v___x_5916_);
lean_ctor_set(v___x_5918_, 1, v___x_5917_);
v___x_5919_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_5920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5920_, 0, v___x_5918_);
lean_ctor_set(v___x_5920_, 1, v___x_5919_);
v___x_5921_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_5895_, v_a_5898_);
v___x_5922_ = l_Lean_indentExpr(v___x_5921_);
v___x_5923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5923_, 0, v___x_5920_);
lean_ctor_set(v___x_5923_, 1, v___x_5922_);
v___x_5924_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_5837_, v___x_5923_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_);
if (lean_obj_tag(v___x_5924_) == 0)
{
lean_dec_ref_known(v___x_5924_, 1);
v___y_5904_ = v___y_5838_;
v___y_5905_ = v___y_5839_;
v___y_5906_ = v___y_5840_;
v___y_5907_ = v___y_5841_;
v___y_5908_ = v___y_5842_;
v___y_5909_ = v___y_5843_;
goto v___jp_5903_;
}
else
{
lean_dec_ref(v___f_5902_);
lean_dec(v_a_5898_);
lean_dec_ref(v___x_5895_);
lean_dec(v_a_5884_);
return v___x_5924_;
}
}
}
v___jp_5903_:
{
if (lean_obj_tag(v_a_5898_) == 0)
{
lean_dec_ref_known(v_a_5898_, 0);
lean_dec(v_a_5884_);
v_e_5846_ = v___x_5895_;
v_onTrue_5847_ = v___f_5902_;
v___y_5848_ = v___y_5904_;
v___y_5849_ = v___y_5905_;
v___y_5850_ = v___y_5906_;
v___y_5851_ = v___y_5907_;
v___y_5852_ = v___y_5908_;
v___y_5853_ = v___y_5909_;
goto v___jp_5845_;
}
else
{
lean_object* v_e_x27_5910_; lean_object* v_proof_5911_; lean_object* v___x_5912_; 
lean_dec_ref(v___f_5902_);
lean_dec_ref(v___x_5895_);
v_e_x27_5910_ = lean_ctor_get(v_a_5898_, 0);
lean_inc_ref(v_e_x27_5910_);
v_proof_5911_ = lean_ctor_get(v_a_5898_, 1);
lean_inc_ref(v_proof_5911_);
lean_dec_ref_known(v_a_5898_, 2);
v___x_5912_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_5912_, 0, v_a_5884_);
lean_closure_set(v___x_5912_, 1, v_proof_5911_);
v_e_5846_ = v_e_x27_5910_;
v_onTrue_5847_ = v___x_5912_;
v___y_5848_ = v___y_5904_;
v___y_5849_ = v___y_5905_;
v___y_5850_ = v___y_5906_;
v___y_5851_ = v___y_5907_;
v___y_5852_ = v___y_5908_;
v___y_5853_ = v___y_5909_;
goto v___jp_5845_;
}
}
}
else
{
lean_object* v_a_5925_; lean_object* v___x_5927_; uint8_t v_isShared_5928_; uint8_t v_isSharedCheck_5932_; 
lean_dec_ref(v___x_5895_);
lean_dec(v_a_5884_);
lean_dec(v_cls_5837_);
v_a_5925_ = lean_ctor_get(v___x_5896_, 0);
v_isSharedCheck_5932_ = !lean_is_exclusive(v___x_5896_);
if (v_isSharedCheck_5932_ == 0)
{
v___x_5927_ = v___x_5896_;
v_isShared_5928_ = v_isSharedCheck_5932_;
goto v_resetjp_5926_;
}
else
{
lean_inc(v_a_5925_);
lean_dec(v___x_5896_);
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
}
else
{
lean_object* v_a_5933_; lean_object* v___x_5935_; uint8_t v_isShared_5936_; uint8_t v_isSharedCheck_5940_; 
lean_dec(v_a_5884_);
lean_dec(v_cls_5837_);
lean_dec_ref(v___x_5836_);
v_a_5933_ = lean_ctor_get(v___x_5885_, 0);
v_isSharedCheck_5940_ = !lean_is_exclusive(v___x_5885_);
if (v_isSharedCheck_5940_ == 0)
{
v___x_5935_ = v___x_5885_;
v_isShared_5936_ = v_isSharedCheck_5940_;
goto v_resetjp_5934_;
}
else
{
lean_inc(v_a_5933_);
lean_dec(v___x_5885_);
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
lean_object* v_a_5941_; lean_object* v___x_5943_; uint8_t v_isShared_5944_; uint8_t v_isSharedCheck_5948_; 
lean_dec(v_cls_5837_);
lean_dec_ref(v___x_5836_);
v_a_5941_ = lean_ctor_get(v___x_5883_, 0);
v_isSharedCheck_5948_ = !lean_is_exclusive(v___x_5883_);
if (v_isSharedCheck_5948_ == 0)
{
v___x_5943_ = v___x_5883_;
v_isShared_5944_ = v_isSharedCheck_5948_;
goto v_resetjp_5942_;
}
else
{
lean_inc(v_a_5941_);
lean_dec(v___x_5883_);
v___x_5943_ = lean_box(0);
v_isShared_5944_ = v_isSharedCheck_5948_;
goto v_resetjp_5942_;
}
v_resetjp_5942_:
{
lean_object* v___x_5946_; 
if (v_isShared_5944_ == 0)
{
v___x_5946_ = v___x_5943_;
goto v_reusejp_5945_;
}
else
{
lean_object* v_reuseFailAlloc_5947_; 
v_reuseFailAlloc_5947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5947_, 0, v_a_5941_);
v___x_5946_ = v_reuseFailAlloc_5947_;
goto v_reusejp_5945_;
}
v_reusejp_5945_:
{
return v___x_5946_;
}
}
}
v___jp_5845_:
{
lean_object* v___x_5854_; 
v___x_5854_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_5846_, v___y_5848_);
if (lean_obj_tag(v___x_5854_) == 0)
{
lean_object* v_a_5855_; uint8_t v___x_5856_; 
v_a_5855_ = lean_ctor_get(v___x_5854_, 0);
lean_inc(v_a_5855_);
lean_dec_ref_known(v___x_5854_, 1);
v___x_5856_ = lean_unbox(v_a_5855_);
lean_dec(v_a_5855_);
if (v___x_5856_ == 0)
{
lean_object* v___x_5857_; 
lean_dec_ref(v_onTrue_5847_);
v___x_5857_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_5846_, v___y_5848_);
if (lean_obj_tag(v___x_5857_) == 0)
{
lean_object* v_a_5858_; uint8_t v___x_5859_; 
v_a_5858_ = lean_ctor_get(v___x_5857_, 0);
lean_inc(v_a_5858_);
lean_dec_ref_known(v___x_5857_, 1);
v___x_5859_ = lean_unbox(v_a_5858_);
lean_dec(v_a_5858_);
if (v___x_5859_ == 0)
{
lean_object* v___x_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; 
v___x_5860_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1);
v___x_5861_ = l_Lean_indentExpr(v_e_5846_);
v___x_5862_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5862_, 0, v___x_5860_);
lean_ctor_set(v___x_5862_, 1, v___x_5861_);
v___x_5863_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5862_, v___y_5850_, v___y_5851_, v___y_5852_, v___y_5853_);
return v___x_5863_;
}
else
{
lean_object* v___x_5864_; lean_object* v___x_5865_; 
lean_dec_ref(v_e_5846_);
v___x_5864_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3);
v___x_5865_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5864_, v___y_5850_, v___y_5851_, v___y_5852_, v___y_5853_);
return v___x_5865_;
}
}
else
{
lean_object* v_a_5866_; lean_object* v___x_5868_; uint8_t v_isShared_5869_; uint8_t v_isSharedCheck_5873_; 
lean_dec_ref(v_e_5846_);
v_a_5866_ = lean_ctor_get(v___x_5857_, 0);
v_isSharedCheck_5873_ = !lean_is_exclusive(v___x_5857_);
if (v_isSharedCheck_5873_ == 0)
{
v___x_5868_ = v___x_5857_;
v_isShared_5869_ = v_isSharedCheck_5873_;
goto v_resetjp_5867_;
}
else
{
lean_inc(v_a_5866_);
lean_dec(v___x_5857_);
v___x_5868_ = lean_box(0);
v_isShared_5869_ = v_isSharedCheck_5873_;
goto v_resetjp_5867_;
}
v_resetjp_5867_:
{
lean_object* v___x_5871_; 
if (v_isShared_5869_ == 0)
{
v___x_5871_ = v___x_5868_;
goto v_reusejp_5870_;
}
else
{
lean_object* v_reuseFailAlloc_5872_; 
v_reuseFailAlloc_5872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5872_, 0, v_a_5866_);
v___x_5871_ = v_reuseFailAlloc_5872_;
goto v_reusejp_5870_;
}
v_reusejp_5870_:
{
return v___x_5871_;
}
}
}
}
else
{
lean_object* v___x_5874_; 
lean_dec_ref(v_e_5846_);
lean_inc(v___y_5853_);
lean_inc_ref(v___y_5852_);
lean_inc(v___y_5851_);
lean_inc_ref(v___y_5850_);
lean_inc(v___y_5849_);
lean_inc_ref(v___y_5848_);
v___x_5874_ = lean_apply_7(v_onTrue_5847_, v___y_5848_, v___y_5849_, v___y_5850_, v___y_5851_, v___y_5852_, v___y_5853_, lean_box(0));
return v___x_5874_;
}
}
else
{
lean_object* v_a_5875_; lean_object* v___x_5877_; uint8_t v_isShared_5878_; uint8_t v_isSharedCheck_5882_; 
lean_dec_ref(v_onTrue_5847_);
lean_dec_ref(v_e_5846_);
v_a_5875_ = lean_ctor_get(v___x_5854_, 0);
v_isSharedCheck_5882_ = !lean_is_exclusive(v___x_5854_);
if (v_isSharedCheck_5882_ == 0)
{
v___x_5877_ = v___x_5854_;
v_isShared_5878_ = v_isSharedCheck_5882_;
goto v_resetjp_5876_;
}
else
{
lean_inc(v_a_5875_);
lean_dec(v___x_5854_);
v___x_5877_ = lean_box(0);
v_isShared_5878_ = v_isSharedCheck_5882_;
goto v_resetjp_5876_;
}
v_resetjp_5876_:
{
lean_object* v___x_5880_; 
if (v_isShared_5878_ == 0)
{
v___x_5880_ = v___x_5877_;
goto v_reusejp_5879_;
}
else
{
lean_object* v_reuseFailAlloc_5881_; 
v_reuseFailAlloc_5881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5881_, 0, v_a_5875_);
v___x_5880_ = v_reuseFailAlloc_5881_;
goto v_reusejp_5879_;
}
v_reusejp_5879_:
{
return v___x_5880_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___boxed(lean_object* v_m_5949_, lean_object* v___x_5950_, lean_object* v_cls_5951_, lean_object* v___y_5952_, lean_object* v___y_5953_, lean_object* v___y_5954_, lean_object* v___y_5955_, lean_object* v___y_5956_, lean_object* v___y_5957_, lean_object* v___y_5958_){
_start:
{
lean_object* v_res_5959_; 
v_res_5959_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1(v_m_5949_, v___x_5950_, v_cls_5951_, v___y_5952_, v___y_5953_, v___y_5954_, v___y_5955_, v___y_5956_, v___y_5957_);
lean_dec(v___y_5957_);
lean_dec_ref(v___y_5956_);
lean_dec(v___y_5955_);
lean_dec_ref(v___y_5954_);
lean_dec(v___y_5953_);
lean_dec_ref(v___y_5952_);
return v_res_5959_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1(void){
_start:
{
lean_object* v___x_5961_; lean_object* v___x_5962_; 
v___x_5961_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__0));
v___x_5962_ = l_Lean_stringToMessageData(v___x_5961_);
return v___x_5962_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3(void){
_start:
{
lean_object* v___x_5964_; lean_object* v___x_5965_; 
v___x_5964_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__2));
v___x_5965_ = l_Lean_stringToMessageData(v___x_5964_);
return v___x_5965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2(lean_object* v_x_5966_, lean_object* v___y_5967_, lean_object* v___y_5968_, lean_object* v___y_5969_, lean_object* v___y_5970_){
_start:
{
if (lean_obj_tag(v_x_5966_) == 0)
{
lean_object* v_a_5972_; lean_object* v___x_5974_; uint8_t v_isShared_5975_; uint8_t v_isSharedCheck_5982_; 
v_a_5972_ = lean_ctor_get(v_x_5966_, 0);
v_isSharedCheck_5982_ = !lean_is_exclusive(v_x_5966_);
if (v_isSharedCheck_5982_ == 0)
{
v___x_5974_ = v_x_5966_;
v_isShared_5975_ = v_isSharedCheck_5982_;
goto v_resetjp_5973_;
}
else
{
lean_inc(v_a_5972_);
lean_dec(v_x_5966_);
v___x_5974_ = lean_box(0);
v_isShared_5975_ = v_isSharedCheck_5982_;
goto v_resetjp_5973_;
}
v_resetjp_5973_:
{
lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5980_; 
v___x_5976_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1);
v___x_5977_ = l_Lean_Exception_toMessageData(v_a_5972_);
v___x_5978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5978_, 0, v___x_5976_);
lean_ctor_set(v___x_5978_, 1, v___x_5977_);
if (v_isShared_5975_ == 0)
{
lean_ctor_set(v___x_5974_, 0, v___x_5978_);
v___x_5980_ = v___x_5974_;
goto v_reusejp_5979_;
}
else
{
lean_object* v_reuseFailAlloc_5981_; 
v_reuseFailAlloc_5981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5981_, 0, v___x_5978_);
v___x_5980_ = v_reuseFailAlloc_5981_;
goto v_reusejp_5979_;
}
v_reusejp_5979_:
{
return v___x_5980_;
}
}
}
else
{
lean_object* v___x_5984_; uint8_t v_isShared_5985_; uint8_t v_isSharedCheck_5990_; 
v_isSharedCheck_5990_ = !lean_is_exclusive(v_x_5966_);
if (v_isSharedCheck_5990_ == 0)
{
lean_object* v_unused_5991_; 
v_unused_5991_ = lean_ctor_get(v_x_5966_, 0);
lean_dec(v_unused_5991_);
v___x_5984_ = v_x_5966_;
v_isShared_5985_ = v_isSharedCheck_5990_;
goto v_resetjp_5983_;
}
else
{
lean_dec(v_x_5966_);
v___x_5984_ = lean_box(0);
v_isShared_5985_ = v_isSharedCheck_5990_;
goto v_resetjp_5983_;
}
v_resetjp_5983_:
{
lean_object* v___x_5986_; lean_object* v___x_5988_; 
v___x_5986_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3);
if (v_isShared_5985_ == 0)
{
lean_ctor_set_tag(v___x_5984_, 0);
lean_ctor_set(v___x_5984_, 0, v___x_5986_);
v___x_5988_ = v___x_5984_;
goto v_reusejp_5987_;
}
else
{
lean_object* v_reuseFailAlloc_5989_; 
v_reuseFailAlloc_5989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5989_, 0, v___x_5986_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___boxed(lean_object* v_x_5992_, lean_object* v___y_5993_, lean_object* v___y_5994_, lean_object* v___y_5995_, lean_object* v___y_5996_, lean_object* v___y_5997_){
_start:
{
lean_object* v_res_5998_; 
v_res_5998_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2(v_x_5992_, v___y_5993_, v___y_5994_, v___y_5995_, v___y_5996_);
lean_dec(v___y_5996_);
lean_dec_ref(v___y_5995_);
lean_dec(v___y_5994_);
lean_dec_ref(v___y_5993_);
return v_res_5998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3(lean_object* v_a_5999_, uint8_t v_hasTrace_6000_, lean_object* v___y_6001_, lean_object* v___y_6002_, lean_object* v___y_6003_, lean_object* v___y_6004_, lean_object* v___y_6005_, lean_object* v___y_6006_){
_start:
{
lean_object* v___x_6008_; 
v___x_6008_ = l_Lean_MVarId_refl(v_a_5999_, v_hasTrace_6000_, v___y_6003_, v___y_6004_, v___y_6005_, v___y_6006_);
return v___x_6008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3___boxed(lean_object* v_a_6009_, lean_object* v_hasTrace_6010_, lean_object* v___y_6011_, lean_object* v___y_6012_, lean_object* v___y_6013_, lean_object* v___y_6014_, lean_object* v___y_6015_, lean_object* v___y_6016_, lean_object* v___y_6017_){
_start:
{
uint8_t v_hasTrace_boxed_6018_; lean_object* v_res_6019_; 
v_hasTrace_boxed_6018_ = lean_unbox(v_hasTrace_6010_);
v_res_6019_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3(v_a_6009_, v_hasTrace_boxed_6018_, v___y_6011_, v___y_6012_, v___y_6013_, v___y_6014_, v___y_6015_, v___y_6016_);
lean_dec(v___y_6016_);
lean_dec_ref(v___y_6015_);
lean_dec(v___y_6014_);
lean_dec_ref(v___y_6013_);
lean_dec(v___y_6012_);
lean_dec_ref(v___y_6011_);
return v_res_6019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4(lean_object* v_m_6020_, lean_object* v___x_6021_, uint8_t v_hasTrace_6022_, lean_object* v_cls_6023_, lean_object* v___y_6024_, lean_object* v___y_6025_, lean_object* v___y_6026_, lean_object* v___y_6027_, lean_object* v___y_6028_, lean_object* v___y_6029_){
_start:
{
lean_object* v_e_6032_; lean_object* v_onTrue_6033_; lean_object* v___y_6034_; lean_object* v___y_6035_; lean_object* v___y_6036_; lean_object* v___y_6037_; lean_object* v___y_6038_; lean_object* v___y_6039_; lean_object* v___x_6069_; 
v___x_6069_ = l_Lean_Meta_Sym_preprocessMVar(v_m_6020_, v___y_6024_, v___y_6025_, v___y_6026_, v___y_6027_, v___y_6028_, v___y_6029_);
if (lean_obj_tag(v___x_6069_) == 0)
{
lean_object* v_a_6070_; lean_object* v___x_6071_; 
v_a_6070_ = lean_ctor_get(v___x_6069_, 0);
lean_inc_n(v_a_6070_, 2);
lean_dec_ref_known(v___x_6069_, 1);
v___x_6071_ = l_Lean_MVarId_getType(v_a_6070_, v___y_6026_, v___y_6027_, v___y_6028_, v___y_6029_);
if (lean_obj_tag(v___x_6071_) == 0)
{
lean_object* v_a_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; uint8_t v___x_6075_; 
v_a_6072_ = lean_ctor_get(v___x_6071_, 0);
lean_inc(v_a_6072_);
lean_dec_ref_known(v___x_6071_, 1);
v___x_6073_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4));
v___x_6074_ = lean_unsigned_to_nat(3u);
v___x_6075_ = l_Lean_Expr_isAppOfArity(v_a_6072_, v___x_6073_, v___x_6074_);
if (v___x_6075_ == 0)
{
lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; 
lean_dec(v_a_6070_);
lean_dec(v_cls_6023_);
lean_dec_ref(v___x_6021_);
v___x_6076_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6);
v___x_6077_ = l_Lean_indentExpr(v_a_6072_);
v___x_6078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6078_, 0, v___x_6076_);
lean_ctor_set(v___x_6078_, 1, v___x_6077_);
v___x_6079_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6078_, v___y_6026_, v___y_6027_, v___y_6028_, v___y_6029_);
return v___x_6079_;
}
else
{
lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; 
v___x_6080_ = l_Lean_Expr_appFn_x21(v_a_6072_);
lean_dec(v_a_6072_);
v___x_6081_ = l_Lean_Expr_appArg_x21(v___x_6080_);
lean_dec_ref(v___x_6080_);
lean_inc_ref(v___x_6081_);
v___x_6082_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_6081_, v___x_6021_, v___y_6024_, v___y_6025_, v___y_6026_, v___y_6027_, v___y_6028_, v___y_6029_);
if (lean_obj_tag(v___x_6082_) == 0)
{
lean_object* v_options_6083_; lean_object* v_a_6084_; lean_object* v_inheritedTraceOptions_6085_; uint8_t v_hasTrace_6086_; lean_object* v___x_6087_; lean_object* v___f_6088_; lean_object* v___y_6090_; lean_object* v___y_6091_; lean_object* v___y_6092_; lean_object* v___y_6093_; lean_object* v___y_6094_; lean_object* v___y_6095_; 
v_options_6083_ = lean_ctor_get(v___y_6028_, 2);
v_a_6084_ = lean_ctor_get(v___x_6082_, 0);
lean_inc(v_a_6084_);
lean_dec_ref_known(v___x_6082_, 1);
v_inheritedTraceOptions_6085_ = lean_ctor_get(v___y_6028_, 13);
v_hasTrace_6086_ = lean_ctor_get_uint8(v_options_6083_, sizeof(void*)*1);
v___x_6087_ = lean_box(v_hasTrace_6022_);
lean_inc(v_a_6070_);
v___f_6088_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3___boxed), 9, 2);
lean_closure_set(v___f_6088_, 0, v_a_6070_);
lean_closure_set(v___f_6088_, 1, v___x_6087_);
if (v_hasTrace_6086_ == 0)
{
lean_dec(v_cls_6023_);
v___y_6090_ = v___y_6024_;
v___y_6091_ = v___y_6025_;
v___y_6092_ = v___y_6026_;
v___y_6093_ = v___y_6027_;
v___y_6094_ = v___y_6028_;
v___y_6095_ = v___y_6029_;
goto v___jp_6089_;
}
else
{
lean_object* v___x_6099_; lean_object* v___x_6100_; uint8_t v___x_6101_; 
v___x_6099_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
lean_inc(v_cls_6023_);
v___x_6100_ = l_Lean_Name_append(v___x_6099_, v_cls_6023_);
v___x_6101_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6085_, v_options_6083_, v___x_6100_);
lean_dec(v___x_6100_);
if (v___x_6101_ == 0)
{
lean_dec(v_cls_6023_);
v___y_6090_ = v___y_6024_;
v___y_6091_ = v___y_6025_;
v___y_6092_ = v___y_6026_;
v___y_6093_ = v___y_6027_;
v___y_6094_ = v___y_6028_;
v___y_6095_ = v___y_6029_;
goto v___jp_6089_;
}
else
{
lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___x_6110_; 
v___x_6102_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8);
lean_inc_ref(v___x_6081_);
v___x_6103_ = l_Lean_indentExpr(v___x_6081_);
v___x_6104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6104_, 0, v___x_6102_);
lean_ctor_set(v___x_6104_, 1, v___x_6103_);
v___x_6105_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_6106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6106_, 0, v___x_6104_);
lean_ctor_set(v___x_6106_, 1, v___x_6105_);
v___x_6107_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_6081_, v_a_6084_);
v___x_6108_ = l_Lean_indentExpr(v___x_6107_);
v___x_6109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6109_, 0, v___x_6106_);
lean_ctor_set(v___x_6109_, 1, v___x_6108_);
v___x_6110_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_6023_, v___x_6109_, v___y_6026_, v___y_6027_, v___y_6028_, v___y_6029_);
if (lean_obj_tag(v___x_6110_) == 0)
{
lean_dec_ref_known(v___x_6110_, 1);
v___y_6090_ = v___y_6024_;
v___y_6091_ = v___y_6025_;
v___y_6092_ = v___y_6026_;
v___y_6093_ = v___y_6027_;
v___y_6094_ = v___y_6028_;
v___y_6095_ = v___y_6029_;
goto v___jp_6089_;
}
else
{
lean_dec_ref(v___f_6088_);
lean_dec(v_a_6084_);
lean_dec_ref(v___x_6081_);
lean_dec(v_a_6070_);
return v___x_6110_;
}
}
}
v___jp_6089_:
{
if (lean_obj_tag(v_a_6084_) == 0)
{
lean_dec_ref_known(v_a_6084_, 0);
lean_dec(v_a_6070_);
v_e_6032_ = v___x_6081_;
v_onTrue_6033_ = v___f_6088_;
v___y_6034_ = v___y_6090_;
v___y_6035_ = v___y_6091_;
v___y_6036_ = v___y_6092_;
v___y_6037_ = v___y_6093_;
v___y_6038_ = v___y_6094_;
v___y_6039_ = v___y_6095_;
goto v___jp_6031_;
}
else
{
lean_object* v_e_x27_6096_; lean_object* v_proof_6097_; lean_object* v___x_6098_; 
lean_dec_ref(v___f_6088_);
lean_dec_ref(v___x_6081_);
v_e_x27_6096_ = lean_ctor_get(v_a_6084_, 0);
lean_inc_ref(v_e_x27_6096_);
v_proof_6097_ = lean_ctor_get(v_a_6084_, 1);
lean_inc_ref(v_proof_6097_);
lean_dec_ref_known(v_a_6084_, 2);
v___x_6098_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_6098_, 0, v_a_6070_);
lean_closure_set(v___x_6098_, 1, v_proof_6097_);
v_e_6032_ = v_e_x27_6096_;
v_onTrue_6033_ = v___x_6098_;
v___y_6034_ = v___y_6090_;
v___y_6035_ = v___y_6091_;
v___y_6036_ = v___y_6092_;
v___y_6037_ = v___y_6093_;
v___y_6038_ = v___y_6094_;
v___y_6039_ = v___y_6095_;
goto v___jp_6031_;
}
}
}
else
{
lean_object* v_a_6111_; lean_object* v___x_6113_; uint8_t v_isShared_6114_; uint8_t v_isSharedCheck_6118_; 
lean_dec_ref(v___x_6081_);
lean_dec(v_a_6070_);
lean_dec(v_cls_6023_);
v_a_6111_ = lean_ctor_get(v___x_6082_, 0);
v_isSharedCheck_6118_ = !lean_is_exclusive(v___x_6082_);
if (v_isSharedCheck_6118_ == 0)
{
v___x_6113_ = v___x_6082_;
v_isShared_6114_ = v_isSharedCheck_6118_;
goto v_resetjp_6112_;
}
else
{
lean_inc(v_a_6111_);
lean_dec(v___x_6082_);
v___x_6113_ = lean_box(0);
v_isShared_6114_ = v_isSharedCheck_6118_;
goto v_resetjp_6112_;
}
v_resetjp_6112_:
{
lean_object* v___x_6116_; 
if (v_isShared_6114_ == 0)
{
v___x_6116_ = v___x_6113_;
goto v_reusejp_6115_;
}
else
{
lean_object* v_reuseFailAlloc_6117_; 
v_reuseFailAlloc_6117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6117_, 0, v_a_6111_);
v___x_6116_ = v_reuseFailAlloc_6117_;
goto v_reusejp_6115_;
}
v_reusejp_6115_:
{
return v___x_6116_;
}
}
}
}
}
else
{
lean_object* v_a_6119_; lean_object* v___x_6121_; uint8_t v_isShared_6122_; uint8_t v_isSharedCheck_6126_; 
lean_dec(v_a_6070_);
lean_dec(v_cls_6023_);
lean_dec_ref(v___x_6021_);
v_a_6119_ = lean_ctor_get(v___x_6071_, 0);
v_isSharedCheck_6126_ = !lean_is_exclusive(v___x_6071_);
if (v_isSharedCheck_6126_ == 0)
{
v___x_6121_ = v___x_6071_;
v_isShared_6122_ = v_isSharedCheck_6126_;
goto v_resetjp_6120_;
}
else
{
lean_inc(v_a_6119_);
lean_dec(v___x_6071_);
v___x_6121_ = lean_box(0);
v_isShared_6122_ = v_isSharedCheck_6126_;
goto v_resetjp_6120_;
}
v_resetjp_6120_:
{
lean_object* v___x_6124_; 
if (v_isShared_6122_ == 0)
{
v___x_6124_ = v___x_6121_;
goto v_reusejp_6123_;
}
else
{
lean_object* v_reuseFailAlloc_6125_; 
v_reuseFailAlloc_6125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6125_, 0, v_a_6119_);
v___x_6124_ = v_reuseFailAlloc_6125_;
goto v_reusejp_6123_;
}
v_reusejp_6123_:
{
return v___x_6124_;
}
}
}
}
else
{
lean_object* v_a_6127_; lean_object* v___x_6129_; uint8_t v_isShared_6130_; uint8_t v_isSharedCheck_6134_; 
lean_dec(v_cls_6023_);
lean_dec_ref(v___x_6021_);
v_a_6127_ = lean_ctor_get(v___x_6069_, 0);
v_isSharedCheck_6134_ = !lean_is_exclusive(v___x_6069_);
if (v_isSharedCheck_6134_ == 0)
{
v___x_6129_ = v___x_6069_;
v_isShared_6130_ = v_isSharedCheck_6134_;
goto v_resetjp_6128_;
}
else
{
lean_inc(v_a_6127_);
lean_dec(v___x_6069_);
v___x_6129_ = lean_box(0);
v_isShared_6130_ = v_isSharedCheck_6134_;
goto v_resetjp_6128_;
}
v_resetjp_6128_:
{
lean_object* v___x_6132_; 
if (v_isShared_6130_ == 0)
{
v___x_6132_ = v___x_6129_;
goto v_reusejp_6131_;
}
else
{
lean_object* v_reuseFailAlloc_6133_; 
v_reuseFailAlloc_6133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6133_, 0, v_a_6127_);
v___x_6132_ = v_reuseFailAlloc_6133_;
goto v_reusejp_6131_;
}
v_reusejp_6131_:
{
return v___x_6132_;
}
}
}
v___jp_6031_:
{
lean_object* v___x_6040_; 
v___x_6040_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_6032_, v___y_6034_);
if (lean_obj_tag(v___x_6040_) == 0)
{
lean_object* v_a_6041_; uint8_t v___x_6042_; 
v_a_6041_ = lean_ctor_get(v___x_6040_, 0);
lean_inc(v_a_6041_);
lean_dec_ref_known(v___x_6040_, 1);
v___x_6042_ = lean_unbox(v_a_6041_);
lean_dec(v_a_6041_);
if (v___x_6042_ == 0)
{
lean_object* v___x_6043_; 
lean_dec_ref(v_onTrue_6033_);
v___x_6043_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_6032_, v___y_6034_);
if (lean_obj_tag(v___x_6043_) == 0)
{
lean_object* v_a_6044_; uint8_t v___x_6045_; 
v_a_6044_ = lean_ctor_get(v___x_6043_, 0);
lean_inc(v_a_6044_);
lean_dec_ref_known(v___x_6043_, 1);
v___x_6045_ = lean_unbox(v_a_6044_);
lean_dec(v_a_6044_);
if (v___x_6045_ == 0)
{
lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; 
v___x_6046_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1);
v___x_6047_ = l_Lean_indentExpr(v_e_6032_);
v___x_6048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6048_, 0, v___x_6046_);
lean_ctor_set(v___x_6048_, 1, v___x_6047_);
v___x_6049_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6048_, v___y_6036_, v___y_6037_, v___y_6038_, v___y_6039_);
return v___x_6049_;
}
else
{
lean_object* v___x_6050_; lean_object* v___x_6051_; 
lean_dec_ref(v_e_6032_);
v___x_6050_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3);
v___x_6051_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6050_, v___y_6036_, v___y_6037_, v___y_6038_, v___y_6039_);
return v___x_6051_;
}
}
else
{
lean_object* v_a_6052_; lean_object* v___x_6054_; uint8_t v_isShared_6055_; uint8_t v_isSharedCheck_6059_; 
lean_dec_ref(v_e_6032_);
v_a_6052_ = lean_ctor_get(v___x_6043_, 0);
v_isSharedCheck_6059_ = !lean_is_exclusive(v___x_6043_);
if (v_isSharedCheck_6059_ == 0)
{
v___x_6054_ = v___x_6043_;
v_isShared_6055_ = v_isSharedCheck_6059_;
goto v_resetjp_6053_;
}
else
{
lean_inc(v_a_6052_);
lean_dec(v___x_6043_);
v___x_6054_ = lean_box(0);
v_isShared_6055_ = v_isSharedCheck_6059_;
goto v_resetjp_6053_;
}
v_resetjp_6053_:
{
lean_object* v___x_6057_; 
if (v_isShared_6055_ == 0)
{
v___x_6057_ = v___x_6054_;
goto v_reusejp_6056_;
}
else
{
lean_object* v_reuseFailAlloc_6058_; 
v_reuseFailAlloc_6058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6058_, 0, v_a_6052_);
v___x_6057_ = v_reuseFailAlloc_6058_;
goto v_reusejp_6056_;
}
v_reusejp_6056_:
{
return v___x_6057_;
}
}
}
}
else
{
lean_object* v___x_6060_; 
lean_dec_ref(v_e_6032_);
lean_inc(v___y_6039_);
lean_inc_ref(v___y_6038_);
lean_inc(v___y_6037_);
lean_inc_ref(v___y_6036_);
lean_inc(v___y_6035_);
lean_inc_ref(v___y_6034_);
v___x_6060_ = lean_apply_7(v_onTrue_6033_, v___y_6034_, v___y_6035_, v___y_6036_, v___y_6037_, v___y_6038_, v___y_6039_, lean_box(0));
return v___x_6060_;
}
}
else
{
lean_object* v_a_6061_; lean_object* v___x_6063_; uint8_t v_isShared_6064_; uint8_t v_isSharedCheck_6068_; 
lean_dec_ref(v_onTrue_6033_);
lean_dec_ref(v_e_6032_);
v_a_6061_ = lean_ctor_get(v___x_6040_, 0);
v_isSharedCheck_6068_ = !lean_is_exclusive(v___x_6040_);
if (v_isSharedCheck_6068_ == 0)
{
v___x_6063_ = v___x_6040_;
v_isShared_6064_ = v_isSharedCheck_6068_;
goto v_resetjp_6062_;
}
else
{
lean_inc(v_a_6061_);
lean_dec(v___x_6040_);
v___x_6063_ = lean_box(0);
v_isShared_6064_ = v_isSharedCheck_6068_;
goto v_resetjp_6062_;
}
v_resetjp_6062_:
{
lean_object* v___x_6066_; 
if (v_isShared_6064_ == 0)
{
v___x_6066_ = v___x_6063_;
goto v_reusejp_6065_;
}
else
{
lean_object* v_reuseFailAlloc_6067_; 
v_reuseFailAlloc_6067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6067_, 0, v_a_6061_);
v___x_6066_ = v_reuseFailAlloc_6067_;
goto v_reusejp_6065_;
}
v_reusejp_6065_:
{
return v___x_6066_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed(lean_object* v_m_6135_, lean_object* v___x_6136_, lean_object* v_hasTrace_6137_, lean_object* v_cls_6138_, lean_object* v___y_6139_, lean_object* v___y_6140_, lean_object* v___y_6141_, lean_object* v___y_6142_, lean_object* v___y_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_){
_start:
{
uint8_t v_hasTrace_boxed_6146_; lean_object* v_res_6147_; 
v_hasTrace_boxed_6146_ = lean_unbox(v_hasTrace_6137_);
v_res_6147_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4(v_m_6135_, v___x_6136_, v_hasTrace_boxed_6146_, v_cls_6138_, v___y_6139_, v___y_6140_, v___y_6141_, v___y_6142_, v___y_6143_, v___y_6144_);
lean_dec(v___y_6144_);
lean_dec_ref(v___y_6143_);
lean_dec(v___y_6142_);
lean_dec_ref(v___y_6141_);
lean_dec(v___y_6140_);
lean_dec_ref(v___y_6139_);
return v_res_6147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6(lean_object* v_m_6148_, lean_object* v___x_6149_, uint8_t v___x_6150_, lean_object* v_cls_6151_, lean_object* v___y_6152_, lean_object* v___y_6153_, lean_object* v___y_6154_, lean_object* v___y_6155_, lean_object* v___y_6156_, lean_object* v___y_6157_){
_start:
{
lean_object* v_e_6160_; lean_object* v_onTrue_6161_; lean_object* v___y_6162_; lean_object* v___y_6163_; lean_object* v___y_6164_; lean_object* v___y_6165_; lean_object* v___y_6166_; lean_object* v___y_6167_; lean_object* v___x_6197_; 
v___x_6197_ = l_Lean_Meta_Sym_preprocessMVar(v_m_6148_, v___y_6152_, v___y_6153_, v___y_6154_, v___y_6155_, v___y_6156_, v___y_6157_);
if (lean_obj_tag(v___x_6197_) == 0)
{
lean_object* v_a_6198_; lean_object* v___x_6199_; 
v_a_6198_ = lean_ctor_get(v___x_6197_, 0);
lean_inc_n(v_a_6198_, 2);
lean_dec_ref_known(v___x_6197_, 1);
v___x_6199_ = l_Lean_MVarId_getType(v_a_6198_, v___y_6154_, v___y_6155_, v___y_6156_, v___y_6157_);
if (lean_obj_tag(v___x_6199_) == 0)
{
lean_object* v_a_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; uint8_t v___x_6203_; 
v_a_6200_ = lean_ctor_get(v___x_6199_, 0);
lean_inc(v_a_6200_);
lean_dec_ref_known(v___x_6199_, 1);
v___x_6201_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4));
v___x_6202_ = lean_unsigned_to_nat(3u);
v___x_6203_ = l_Lean_Expr_isAppOfArity(v_a_6200_, v___x_6201_, v___x_6202_);
if (v___x_6203_ == 0)
{
lean_object* v___x_6204_; lean_object* v___x_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; 
lean_dec(v_a_6198_);
lean_dec(v_cls_6151_);
lean_dec_ref(v___x_6149_);
v___x_6204_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6);
v___x_6205_ = l_Lean_indentExpr(v_a_6200_);
v___x_6206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6206_, 0, v___x_6204_);
lean_ctor_set(v___x_6206_, 1, v___x_6205_);
v___x_6207_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6206_, v___y_6154_, v___y_6155_, v___y_6156_, v___y_6157_);
return v___x_6207_;
}
else
{
lean_object* v___x_6208_; lean_object* v___x_6209_; lean_object* v___x_6210_; 
v___x_6208_ = l_Lean_Expr_appFn_x21(v_a_6200_);
lean_dec(v_a_6200_);
v___x_6209_ = l_Lean_Expr_appArg_x21(v___x_6208_);
lean_dec_ref(v___x_6208_);
lean_inc_ref(v___x_6209_);
v___x_6210_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_6209_, v___x_6149_, v___y_6152_, v___y_6153_, v___y_6154_, v___y_6155_, v___y_6156_, v___y_6157_);
if (lean_obj_tag(v___x_6210_) == 0)
{
lean_object* v_options_6211_; lean_object* v_a_6212_; lean_object* v_inheritedTraceOptions_6213_; uint8_t v_hasTrace_6214_; lean_object* v___x_6215_; lean_object* v___f_6216_; lean_object* v___y_6218_; lean_object* v___y_6219_; lean_object* v___y_6220_; lean_object* v___y_6221_; lean_object* v___y_6222_; lean_object* v___y_6223_; 
v_options_6211_ = lean_ctor_get(v___y_6156_, 2);
v_a_6212_ = lean_ctor_get(v___x_6210_, 0);
lean_inc(v_a_6212_);
lean_dec_ref_known(v___x_6210_, 1);
v_inheritedTraceOptions_6213_ = lean_ctor_get(v___y_6156_, 13);
v_hasTrace_6214_ = lean_ctor_get_uint8(v_options_6211_, sizeof(void*)*1);
v___x_6215_ = lean_box(v___x_6150_);
lean_inc(v_a_6198_);
v___f_6216_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed), 9, 2);
lean_closure_set(v___f_6216_, 0, v_a_6198_);
lean_closure_set(v___f_6216_, 1, v___x_6215_);
if (v_hasTrace_6214_ == 0)
{
lean_dec(v_cls_6151_);
v___y_6218_ = v___y_6152_;
v___y_6219_ = v___y_6153_;
v___y_6220_ = v___y_6154_;
v___y_6221_ = v___y_6155_;
v___y_6222_ = v___y_6156_;
v___y_6223_ = v___y_6157_;
goto v___jp_6217_;
}
else
{
lean_object* v___x_6227_; lean_object* v___x_6228_; uint8_t v___x_6229_; 
v___x_6227_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
lean_inc(v_cls_6151_);
v___x_6228_ = l_Lean_Name_append(v___x_6227_, v_cls_6151_);
v___x_6229_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6213_, v_options_6211_, v___x_6228_);
lean_dec(v___x_6228_);
if (v___x_6229_ == 0)
{
lean_dec(v_cls_6151_);
v___y_6218_ = v___y_6152_;
v___y_6219_ = v___y_6153_;
v___y_6220_ = v___y_6154_;
v___y_6221_ = v___y_6155_;
v___y_6222_ = v___y_6156_;
v___y_6223_ = v___y_6157_;
goto v___jp_6217_;
}
else
{
lean_object* v___x_6230_; lean_object* v___x_6231_; lean_object* v___x_6232_; lean_object* v___x_6233_; lean_object* v___x_6234_; lean_object* v___x_6235_; lean_object* v___x_6236_; lean_object* v___x_6237_; lean_object* v___x_6238_; 
v___x_6230_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8);
lean_inc_ref(v___x_6209_);
v___x_6231_ = l_Lean_indentExpr(v___x_6209_);
v___x_6232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6232_, 0, v___x_6230_);
lean_ctor_set(v___x_6232_, 1, v___x_6231_);
v___x_6233_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_6234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6234_, 0, v___x_6232_);
lean_ctor_set(v___x_6234_, 1, v___x_6233_);
v___x_6235_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_6209_, v_a_6212_);
v___x_6236_ = l_Lean_indentExpr(v___x_6235_);
v___x_6237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6237_, 0, v___x_6234_);
lean_ctor_set(v___x_6237_, 1, v___x_6236_);
v___x_6238_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_6151_, v___x_6237_, v___y_6154_, v___y_6155_, v___y_6156_, v___y_6157_);
if (lean_obj_tag(v___x_6238_) == 0)
{
lean_dec_ref_known(v___x_6238_, 1);
v___y_6218_ = v___y_6152_;
v___y_6219_ = v___y_6153_;
v___y_6220_ = v___y_6154_;
v___y_6221_ = v___y_6155_;
v___y_6222_ = v___y_6156_;
v___y_6223_ = v___y_6157_;
goto v___jp_6217_;
}
else
{
lean_dec_ref(v___f_6216_);
lean_dec(v_a_6212_);
lean_dec_ref(v___x_6209_);
lean_dec(v_a_6198_);
return v___x_6238_;
}
}
}
v___jp_6217_:
{
if (lean_obj_tag(v_a_6212_) == 0)
{
lean_dec_ref_known(v_a_6212_, 0);
lean_dec(v_a_6198_);
v_e_6160_ = v___x_6209_;
v_onTrue_6161_ = v___f_6216_;
v___y_6162_ = v___y_6218_;
v___y_6163_ = v___y_6219_;
v___y_6164_ = v___y_6220_;
v___y_6165_ = v___y_6221_;
v___y_6166_ = v___y_6222_;
v___y_6167_ = v___y_6223_;
goto v___jp_6159_;
}
else
{
lean_object* v_e_x27_6224_; lean_object* v_proof_6225_; lean_object* v___x_6226_; 
lean_dec_ref(v___f_6216_);
lean_dec_ref(v___x_6209_);
v_e_x27_6224_ = lean_ctor_get(v_a_6212_, 0);
lean_inc_ref(v_e_x27_6224_);
v_proof_6225_ = lean_ctor_get(v_a_6212_, 1);
lean_inc_ref(v_proof_6225_);
lean_dec_ref_known(v_a_6212_, 2);
v___x_6226_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_6226_, 0, v_a_6198_);
lean_closure_set(v___x_6226_, 1, v_proof_6225_);
v_e_6160_ = v_e_x27_6224_;
v_onTrue_6161_ = v___x_6226_;
v___y_6162_ = v___y_6218_;
v___y_6163_ = v___y_6219_;
v___y_6164_ = v___y_6220_;
v___y_6165_ = v___y_6221_;
v___y_6166_ = v___y_6222_;
v___y_6167_ = v___y_6223_;
goto v___jp_6159_;
}
}
}
else
{
lean_object* v_a_6239_; lean_object* v___x_6241_; uint8_t v_isShared_6242_; uint8_t v_isSharedCheck_6246_; 
lean_dec_ref(v___x_6209_);
lean_dec(v_a_6198_);
lean_dec(v_cls_6151_);
v_a_6239_ = lean_ctor_get(v___x_6210_, 0);
v_isSharedCheck_6246_ = !lean_is_exclusive(v___x_6210_);
if (v_isSharedCheck_6246_ == 0)
{
v___x_6241_ = v___x_6210_;
v_isShared_6242_ = v_isSharedCheck_6246_;
goto v_resetjp_6240_;
}
else
{
lean_inc(v_a_6239_);
lean_dec(v___x_6210_);
v___x_6241_ = lean_box(0);
v_isShared_6242_ = v_isSharedCheck_6246_;
goto v_resetjp_6240_;
}
v_resetjp_6240_:
{
lean_object* v___x_6244_; 
if (v_isShared_6242_ == 0)
{
v___x_6244_ = v___x_6241_;
goto v_reusejp_6243_;
}
else
{
lean_object* v_reuseFailAlloc_6245_; 
v_reuseFailAlloc_6245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6245_, 0, v_a_6239_);
v___x_6244_ = v_reuseFailAlloc_6245_;
goto v_reusejp_6243_;
}
v_reusejp_6243_:
{
return v___x_6244_;
}
}
}
}
}
else
{
lean_object* v_a_6247_; lean_object* v___x_6249_; uint8_t v_isShared_6250_; uint8_t v_isSharedCheck_6254_; 
lean_dec(v_a_6198_);
lean_dec(v_cls_6151_);
lean_dec_ref(v___x_6149_);
v_a_6247_ = lean_ctor_get(v___x_6199_, 0);
v_isSharedCheck_6254_ = !lean_is_exclusive(v___x_6199_);
if (v_isSharedCheck_6254_ == 0)
{
v___x_6249_ = v___x_6199_;
v_isShared_6250_ = v_isSharedCheck_6254_;
goto v_resetjp_6248_;
}
else
{
lean_inc(v_a_6247_);
lean_dec(v___x_6199_);
v___x_6249_ = lean_box(0);
v_isShared_6250_ = v_isSharedCheck_6254_;
goto v_resetjp_6248_;
}
v_resetjp_6248_:
{
lean_object* v___x_6252_; 
if (v_isShared_6250_ == 0)
{
v___x_6252_ = v___x_6249_;
goto v_reusejp_6251_;
}
else
{
lean_object* v_reuseFailAlloc_6253_; 
v_reuseFailAlloc_6253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6253_, 0, v_a_6247_);
v___x_6252_ = v_reuseFailAlloc_6253_;
goto v_reusejp_6251_;
}
v_reusejp_6251_:
{
return v___x_6252_;
}
}
}
}
else
{
lean_object* v_a_6255_; lean_object* v___x_6257_; uint8_t v_isShared_6258_; uint8_t v_isSharedCheck_6262_; 
lean_dec(v_cls_6151_);
lean_dec_ref(v___x_6149_);
v_a_6255_ = lean_ctor_get(v___x_6197_, 0);
v_isSharedCheck_6262_ = !lean_is_exclusive(v___x_6197_);
if (v_isSharedCheck_6262_ == 0)
{
v___x_6257_ = v___x_6197_;
v_isShared_6258_ = v_isSharedCheck_6262_;
goto v_resetjp_6256_;
}
else
{
lean_inc(v_a_6255_);
lean_dec(v___x_6197_);
v___x_6257_ = lean_box(0);
v_isShared_6258_ = v_isSharedCheck_6262_;
goto v_resetjp_6256_;
}
v_resetjp_6256_:
{
lean_object* v___x_6260_; 
if (v_isShared_6258_ == 0)
{
v___x_6260_ = v___x_6257_;
goto v_reusejp_6259_;
}
else
{
lean_object* v_reuseFailAlloc_6261_; 
v_reuseFailAlloc_6261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6261_, 0, v_a_6255_);
v___x_6260_ = v_reuseFailAlloc_6261_;
goto v_reusejp_6259_;
}
v_reusejp_6259_:
{
return v___x_6260_;
}
}
}
v___jp_6159_:
{
lean_object* v___x_6168_; 
v___x_6168_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_6160_, v___y_6162_);
if (lean_obj_tag(v___x_6168_) == 0)
{
lean_object* v_a_6169_; uint8_t v___x_6170_; 
v_a_6169_ = lean_ctor_get(v___x_6168_, 0);
lean_inc(v_a_6169_);
lean_dec_ref_known(v___x_6168_, 1);
v___x_6170_ = lean_unbox(v_a_6169_);
lean_dec(v_a_6169_);
if (v___x_6170_ == 0)
{
lean_object* v___x_6171_; 
lean_dec_ref(v_onTrue_6161_);
v___x_6171_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_6160_, v___y_6162_);
if (lean_obj_tag(v___x_6171_) == 0)
{
lean_object* v_a_6172_; uint8_t v___x_6173_; 
v_a_6172_ = lean_ctor_get(v___x_6171_, 0);
lean_inc(v_a_6172_);
lean_dec_ref_known(v___x_6171_, 1);
v___x_6173_ = lean_unbox(v_a_6172_);
lean_dec(v_a_6172_);
if (v___x_6173_ == 0)
{
lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; 
v___x_6174_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1);
v___x_6175_ = l_Lean_indentExpr(v_e_6160_);
v___x_6176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6176_, 0, v___x_6174_);
lean_ctor_set(v___x_6176_, 1, v___x_6175_);
v___x_6177_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6176_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_);
return v___x_6177_;
}
else
{
lean_object* v___x_6178_; lean_object* v___x_6179_; 
lean_dec_ref(v_e_6160_);
v___x_6178_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3);
v___x_6179_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6178_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_);
return v___x_6179_;
}
}
else
{
lean_object* v_a_6180_; lean_object* v___x_6182_; uint8_t v_isShared_6183_; uint8_t v_isSharedCheck_6187_; 
lean_dec_ref(v_e_6160_);
v_a_6180_ = lean_ctor_get(v___x_6171_, 0);
v_isSharedCheck_6187_ = !lean_is_exclusive(v___x_6171_);
if (v_isSharedCheck_6187_ == 0)
{
v___x_6182_ = v___x_6171_;
v_isShared_6183_ = v_isSharedCheck_6187_;
goto v_resetjp_6181_;
}
else
{
lean_inc(v_a_6180_);
lean_dec(v___x_6171_);
v___x_6182_ = lean_box(0);
v_isShared_6183_ = v_isSharedCheck_6187_;
goto v_resetjp_6181_;
}
v_resetjp_6181_:
{
lean_object* v___x_6185_; 
if (v_isShared_6183_ == 0)
{
v___x_6185_ = v___x_6182_;
goto v_reusejp_6184_;
}
else
{
lean_object* v_reuseFailAlloc_6186_; 
v_reuseFailAlloc_6186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6186_, 0, v_a_6180_);
v___x_6185_ = v_reuseFailAlloc_6186_;
goto v_reusejp_6184_;
}
v_reusejp_6184_:
{
return v___x_6185_;
}
}
}
}
else
{
lean_object* v___x_6188_; 
lean_dec_ref(v_e_6160_);
lean_inc(v___y_6167_);
lean_inc_ref(v___y_6166_);
lean_inc(v___y_6165_);
lean_inc_ref(v___y_6164_);
lean_inc(v___y_6163_);
lean_inc_ref(v___y_6162_);
v___x_6188_ = lean_apply_7(v_onTrue_6161_, v___y_6162_, v___y_6163_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_, lean_box(0));
return v___x_6188_;
}
}
else
{
lean_object* v_a_6189_; lean_object* v___x_6191_; uint8_t v_isShared_6192_; uint8_t v_isSharedCheck_6196_; 
lean_dec_ref(v_onTrue_6161_);
lean_dec_ref(v_e_6160_);
v_a_6189_ = lean_ctor_get(v___x_6168_, 0);
v_isSharedCheck_6196_ = !lean_is_exclusive(v___x_6168_);
if (v_isSharedCheck_6196_ == 0)
{
v___x_6191_ = v___x_6168_;
v_isShared_6192_ = v_isSharedCheck_6196_;
goto v_resetjp_6190_;
}
else
{
lean_inc(v_a_6189_);
lean_dec(v___x_6168_);
v___x_6191_ = lean_box(0);
v_isShared_6192_ = v_isSharedCheck_6196_;
goto v_resetjp_6190_;
}
v_resetjp_6190_:
{
lean_object* v___x_6194_; 
if (v_isShared_6192_ == 0)
{
v___x_6194_ = v___x_6191_;
goto v_reusejp_6193_;
}
else
{
lean_object* v_reuseFailAlloc_6195_; 
v_reuseFailAlloc_6195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6195_, 0, v_a_6189_);
v___x_6194_ = v_reuseFailAlloc_6195_;
goto v_reusejp_6193_;
}
v_reusejp_6193_:
{
return v___x_6194_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6___boxed(lean_object* v_m_6263_, lean_object* v___x_6264_, lean_object* v___x_6265_, lean_object* v_cls_6266_, lean_object* v___y_6267_, lean_object* v___y_6268_, lean_object* v___y_6269_, lean_object* v___y_6270_, lean_object* v___y_6271_, lean_object* v___y_6272_, lean_object* v___y_6273_){
_start:
{
uint8_t v___x_25974__boxed_6274_; lean_object* v_res_6275_; 
v___x_25974__boxed_6274_ = lean_unbox(v___x_6265_);
v_res_6275_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6(v_m_6263_, v___x_6264_, v___x_25974__boxed_6274_, v_cls_6266_, v___y_6267_, v___y_6268_, v___y_6269_, v___y_6270_, v___y_6271_, v___y_6272_);
lean_dec(v___y_6272_);
lean_dec_ref(v___y_6271_);
lean_dec(v___y_6270_);
lean_dec_ref(v___y_6269_);
lean_dec(v___y_6268_);
lean_dec_ref(v___y_6267_);
return v_res_6275_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(lean_object* v_e_6276_){
_start:
{
if (lean_obj_tag(v_e_6276_) == 0)
{
uint8_t v___x_6277_; 
v___x_6277_ = 2;
return v___x_6277_;
}
else
{
uint8_t v___x_6278_; 
v___x_6278_ = 0;
return v___x_6278_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2___boxed(lean_object* v_e_6279_){
_start:
{
uint8_t v_res_6280_; lean_object* v_r_6281_; 
v_res_6280_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(v_e_6279_);
lean_dec_ref(v_e_6279_);
v_r_6281_ = lean_box(v_res_6280_);
return v_r_6281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(lean_object* v_cls_6282_, uint8_t v_collapsed_6283_, lean_object* v_tag_6284_, lean_object* v_opts_6285_, uint8_t v_clsEnabled_6286_, lean_object* v_oldTraces_6287_, lean_object* v_msg_6288_, lean_object* v_resStartStop_6289_, lean_object* v___y_6290_, lean_object* v___y_6291_, lean_object* v___y_6292_, lean_object* v___y_6293_){
_start:
{
lean_object* v_fst_6295_; lean_object* v_snd_6296_; lean_object* v___y_6298_; lean_object* v___y_6299_; lean_object* v_data_6300_; lean_object* v_fst_6303_; lean_object* v_snd_6304_; lean_object* v___x_6305_; uint8_t v___x_6306_; lean_object* v___y_6308_; lean_object* v_a_6309_; uint8_t v___y_6324_; double v___y_6355_; 
v_fst_6295_ = lean_ctor_get(v_resStartStop_6289_, 0);
lean_inc(v_fst_6295_);
v_snd_6296_ = lean_ctor_get(v_resStartStop_6289_, 1);
lean_inc(v_snd_6296_);
lean_dec_ref(v_resStartStop_6289_);
v_fst_6303_ = lean_ctor_get(v_snd_6296_, 0);
lean_inc(v_fst_6303_);
v_snd_6304_ = lean_ctor_get(v_snd_6296_, 1);
lean_inc(v_snd_6304_);
lean_dec(v_snd_6296_);
v___x_6305_ = l_Lean_trace_profiler;
v___x_6306_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_6285_, v___x_6305_);
if (v___x_6306_ == 0)
{
v___y_6324_ = v___x_6306_;
goto v___jp_6323_;
}
else
{
lean_object* v___x_6360_; uint8_t v___x_6361_; 
v___x_6360_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6361_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_6285_, v___x_6360_);
if (v___x_6361_ == 0)
{
lean_object* v___x_6362_; lean_object* v___x_6363_; double v___x_6364_; double v___x_6365_; double v___x_6366_; 
v___x_6362_ = l_Lean_trace_profiler_threshold;
v___x_6363_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_6285_, v___x_6362_);
v___x_6364_ = lean_float_of_nat(v___x_6363_);
v___x_6365_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2);
v___x_6366_ = lean_float_div(v___x_6364_, v___x_6365_);
v___y_6355_ = v___x_6366_;
goto v___jp_6354_;
}
else
{
lean_object* v___x_6367_; lean_object* v___x_6368_; double v___x_6369_; 
v___x_6367_ = l_Lean_trace_profiler_threshold;
v___x_6368_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_6285_, v___x_6367_);
v___x_6369_ = lean_float_of_nat(v___x_6368_);
v___y_6355_ = v___x_6369_;
goto v___jp_6354_;
}
}
v___jp_6297_:
{
lean_object* v___x_6301_; 
lean_inc(v___y_6299_);
v___x_6301_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(v_oldTraces_6287_, v_data_6300_, v___y_6299_, v___y_6298_, v___y_6290_, v___y_6291_, v___y_6292_, v___y_6293_);
if (lean_obj_tag(v___x_6301_) == 0)
{
lean_object* v___x_6302_; 
lean_dec_ref_known(v___x_6301_, 1);
v___x_6302_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_6295_);
return v___x_6302_;
}
else
{
lean_dec(v_fst_6295_);
return v___x_6301_;
}
}
v___jp_6307_:
{
uint8_t v_result_6310_; lean_object* v___x_6311_; lean_object* v___x_6312_; double v___x_6313_; lean_object* v_data_6314_; 
v_result_6310_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(v_fst_6295_);
v___x_6311_ = lean_box(v_result_6310_);
v___x_6312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6312_, 0, v___x_6311_);
v___x_6313_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_6284_);
lean_inc_ref(v___x_6312_);
lean_inc(v_cls_6282_);
v_data_6314_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6314_, 0, v_cls_6282_);
lean_ctor_set(v_data_6314_, 1, v___x_6312_);
lean_ctor_set(v_data_6314_, 2, v_tag_6284_);
lean_ctor_set_float(v_data_6314_, sizeof(void*)*3, v___x_6313_);
lean_ctor_set_float(v_data_6314_, sizeof(void*)*3 + 8, v___x_6313_);
lean_ctor_set_uint8(v_data_6314_, sizeof(void*)*3 + 16, v_collapsed_6283_);
if (v___x_6306_ == 0)
{
lean_dec_ref_known(v___x_6312_, 1);
lean_dec(v_snd_6304_);
lean_dec(v_fst_6303_);
lean_dec_ref(v_tag_6284_);
lean_dec(v_cls_6282_);
v___y_6298_ = v_a_6309_;
v___y_6299_ = v___y_6308_;
v_data_6300_ = v_data_6314_;
goto v___jp_6297_;
}
else
{
lean_object* v_data_6315_; double v___x_6316_; double v___x_6317_; 
lean_dec_ref_known(v_data_6314_, 3);
v_data_6315_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6315_, 0, v_cls_6282_);
lean_ctor_set(v_data_6315_, 1, v___x_6312_);
lean_ctor_set(v_data_6315_, 2, v_tag_6284_);
v___x_6316_ = lean_unbox_float(v_fst_6303_);
lean_dec(v_fst_6303_);
lean_ctor_set_float(v_data_6315_, sizeof(void*)*3, v___x_6316_);
v___x_6317_ = lean_unbox_float(v_snd_6304_);
lean_dec(v_snd_6304_);
lean_ctor_set_float(v_data_6315_, sizeof(void*)*3 + 8, v___x_6317_);
lean_ctor_set_uint8(v_data_6315_, sizeof(void*)*3 + 16, v_collapsed_6283_);
v___y_6298_ = v_a_6309_;
v___y_6299_ = v___y_6308_;
v_data_6300_ = v_data_6315_;
goto v___jp_6297_;
}
}
v___jp_6318_:
{
lean_object* v_ref_6319_; lean_object* v___x_6320_; 
v_ref_6319_ = lean_ctor_get(v___y_6292_, 5);
lean_inc(v___y_6293_);
lean_inc_ref(v___y_6292_);
lean_inc(v___y_6291_);
lean_inc_ref(v___y_6290_);
lean_inc(v_fst_6295_);
v___x_6320_ = lean_apply_6(v_msg_6288_, v_fst_6295_, v___y_6290_, v___y_6291_, v___y_6292_, v___y_6293_, lean_box(0));
if (lean_obj_tag(v___x_6320_) == 0)
{
lean_object* v_a_6321_; 
v_a_6321_ = lean_ctor_get(v___x_6320_, 0);
lean_inc(v_a_6321_);
lean_dec_ref_known(v___x_6320_, 1);
v___y_6308_ = v_ref_6319_;
v_a_6309_ = v_a_6321_;
goto v___jp_6307_;
}
else
{
lean_object* v___x_6322_; 
lean_dec_ref_known(v___x_6320_, 1);
v___x_6322_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
v___y_6308_ = v_ref_6319_;
v_a_6309_ = v___x_6322_;
goto v___jp_6307_;
}
}
v___jp_6323_:
{
if (v_clsEnabled_6286_ == 0)
{
if (v___y_6324_ == 0)
{
lean_object* v___x_6325_; lean_object* v_traceState_6326_; lean_object* v_env_6327_; lean_object* v_nextMacroScope_6328_; lean_object* v_ngen_6329_; lean_object* v_auxDeclNGen_6330_; lean_object* v_cache_6331_; lean_object* v_messages_6332_; lean_object* v_infoState_6333_; lean_object* v_snapshotTasks_6334_; lean_object* v___x_6336_; uint8_t v_isShared_6337_; uint8_t v_isSharedCheck_6353_; 
lean_dec(v_snd_6304_);
lean_dec(v_fst_6303_);
lean_dec_ref(v_msg_6288_);
lean_dec_ref(v_tag_6284_);
lean_dec(v_cls_6282_);
v___x_6325_ = lean_st_ref_take(v___y_6293_);
v_traceState_6326_ = lean_ctor_get(v___x_6325_, 4);
v_env_6327_ = lean_ctor_get(v___x_6325_, 0);
v_nextMacroScope_6328_ = lean_ctor_get(v___x_6325_, 1);
v_ngen_6329_ = lean_ctor_get(v___x_6325_, 2);
v_auxDeclNGen_6330_ = lean_ctor_get(v___x_6325_, 3);
v_cache_6331_ = lean_ctor_get(v___x_6325_, 5);
v_messages_6332_ = lean_ctor_get(v___x_6325_, 6);
v_infoState_6333_ = lean_ctor_get(v___x_6325_, 7);
v_snapshotTasks_6334_ = lean_ctor_get(v___x_6325_, 8);
v_isSharedCheck_6353_ = !lean_is_exclusive(v___x_6325_);
if (v_isSharedCheck_6353_ == 0)
{
v___x_6336_ = v___x_6325_;
v_isShared_6337_ = v_isSharedCheck_6353_;
goto v_resetjp_6335_;
}
else
{
lean_inc(v_snapshotTasks_6334_);
lean_inc(v_infoState_6333_);
lean_inc(v_messages_6332_);
lean_inc(v_cache_6331_);
lean_inc(v_traceState_6326_);
lean_inc(v_auxDeclNGen_6330_);
lean_inc(v_ngen_6329_);
lean_inc(v_nextMacroScope_6328_);
lean_inc(v_env_6327_);
lean_dec(v___x_6325_);
v___x_6336_ = lean_box(0);
v_isShared_6337_ = v_isSharedCheck_6353_;
goto v_resetjp_6335_;
}
v_resetjp_6335_:
{
uint64_t v_tid_6338_; lean_object* v_traces_6339_; lean_object* v___x_6341_; uint8_t v_isShared_6342_; uint8_t v_isSharedCheck_6352_; 
v_tid_6338_ = lean_ctor_get_uint64(v_traceState_6326_, sizeof(void*)*1);
v_traces_6339_ = lean_ctor_get(v_traceState_6326_, 0);
v_isSharedCheck_6352_ = !lean_is_exclusive(v_traceState_6326_);
if (v_isSharedCheck_6352_ == 0)
{
v___x_6341_ = v_traceState_6326_;
v_isShared_6342_ = v_isSharedCheck_6352_;
goto v_resetjp_6340_;
}
else
{
lean_inc(v_traces_6339_);
lean_dec(v_traceState_6326_);
v___x_6341_ = lean_box(0);
v_isShared_6342_ = v_isSharedCheck_6352_;
goto v_resetjp_6340_;
}
v_resetjp_6340_:
{
lean_object* v___x_6343_; lean_object* v___x_6345_; 
v___x_6343_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_6287_, v_traces_6339_);
lean_dec_ref(v_traces_6339_);
if (v_isShared_6342_ == 0)
{
lean_ctor_set(v___x_6341_, 0, v___x_6343_);
v___x_6345_ = v___x_6341_;
goto v_reusejp_6344_;
}
else
{
lean_object* v_reuseFailAlloc_6351_; 
v_reuseFailAlloc_6351_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6351_, 0, v___x_6343_);
lean_ctor_set_uint64(v_reuseFailAlloc_6351_, sizeof(void*)*1, v_tid_6338_);
v___x_6345_ = v_reuseFailAlloc_6351_;
goto v_reusejp_6344_;
}
v_reusejp_6344_:
{
lean_object* v___x_6347_; 
if (v_isShared_6337_ == 0)
{
lean_ctor_set(v___x_6336_, 4, v___x_6345_);
v___x_6347_ = v___x_6336_;
goto v_reusejp_6346_;
}
else
{
lean_object* v_reuseFailAlloc_6350_; 
v_reuseFailAlloc_6350_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6350_, 0, v_env_6327_);
lean_ctor_set(v_reuseFailAlloc_6350_, 1, v_nextMacroScope_6328_);
lean_ctor_set(v_reuseFailAlloc_6350_, 2, v_ngen_6329_);
lean_ctor_set(v_reuseFailAlloc_6350_, 3, v_auxDeclNGen_6330_);
lean_ctor_set(v_reuseFailAlloc_6350_, 4, v___x_6345_);
lean_ctor_set(v_reuseFailAlloc_6350_, 5, v_cache_6331_);
lean_ctor_set(v_reuseFailAlloc_6350_, 6, v_messages_6332_);
lean_ctor_set(v_reuseFailAlloc_6350_, 7, v_infoState_6333_);
lean_ctor_set(v_reuseFailAlloc_6350_, 8, v_snapshotTasks_6334_);
v___x_6347_ = v_reuseFailAlloc_6350_;
goto v_reusejp_6346_;
}
v_reusejp_6346_:
{
lean_object* v___x_6348_; lean_object* v___x_6349_; 
v___x_6348_ = lean_st_ref_set(v___y_6293_, v___x_6347_);
v___x_6349_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_6295_);
return v___x_6349_;
}
}
}
}
}
else
{
goto v___jp_6318_;
}
}
else
{
goto v___jp_6318_;
}
}
v___jp_6354_:
{
double v___x_6356_; double v___x_6357_; double v___x_6358_; uint8_t v___x_6359_; 
v___x_6356_ = lean_unbox_float(v_snd_6304_);
v___x_6357_ = lean_unbox_float(v_fst_6303_);
v___x_6358_ = lean_float_sub(v___x_6356_, v___x_6357_);
v___x_6359_ = lean_float_decLt(v___y_6355_, v___x_6358_);
v___y_6324_ = v___x_6359_;
goto v___jp_6323_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2___boxed(lean_object* v_cls_6370_, lean_object* v_collapsed_6371_, lean_object* v_tag_6372_, lean_object* v_opts_6373_, lean_object* v_clsEnabled_6374_, lean_object* v_oldTraces_6375_, lean_object* v_msg_6376_, lean_object* v_resStartStop_6377_, lean_object* v___y_6378_, lean_object* v___y_6379_, lean_object* v___y_6380_, lean_object* v___y_6381_, lean_object* v___y_6382_){
_start:
{
uint8_t v_collapsed_boxed_6383_; uint8_t v_clsEnabled_boxed_6384_; lean_object* v_res_6385_; 
v_collapsed_boxed_6383_ = lean_unbox(v_collapsed_6371_);
v_clsEnabled_boxed_6384_ = lean_unbox(v_clsEnabled_6374_);
v_res_6385_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(v_cls_6370_, v_collapsed_boxed_6383_, v_tag_6372_, v_opts_6373_, v_clsEnabled_boxed_6384_, v_oldTraces_6375_, v_msg_6376_, v_resStartStop_6377_, v___y_6378_, v___y_6379_, v___y_6380_, v___y_6381_);
lean_dec(v___y_6381_);
lean_dec_ref(v___y_6380_);
lean_dec(v___y_6379_);
lean_dec_ref(v___y_6378_);
lean_dec_ref(v_opts_6373_);
return v_res_6385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(lean_object* v_m_6387_, lean_object* v_a_6388_, lean_object* v_a_6389_, lean_object* v_a_6390_, lean_object* v_a_6391_){
_start:
{
lean_object* v_options_6393_; lean_object* v_inheritedTraceOptions_6394_; uint8_t v_hasTrace_6395_; lean_object* v_cls_6396_; 
v_options_6393_ = lean_ctor_get(v_a_6390_, 2);
v_inheritedTraceOptions_6394_ = lean_ctor_get(v_a_6390_, 13);
v_hasTrace_6395_ = lean_ctor_get_uint8(v_options_6393_, sizeof(void*)*1);
v_cls_6396_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
if (v_hasTrace_6395_ == 0)
{
lean_object* v___x_6397_; lean_object* v___x_6398_; lean_object* v___x_6399_; lean_object* v___x_6400_; lean_object* v___f_6401_; lean_object* v___x_6402_; 
v___x_6397_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6398_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6393_, v___x_6397_);
v___x_6399_ = lean_unsigned_to_nat(2u);
v___x_6400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6400_, 0, v___x_6398_);
lean_ctor_set(v___x_6400_, 1, v___x_6399_);
v___f_6401_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___boxed), 10, 3);
lean_closure_set(v___f_6401_, 0, v_m_6387_);
lean_closure_set(v___f_6401_, 1, v___x_6400_);
lean_closure_set(v___f_6401_, 2, v_cls_6396_);
v___x_6402_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6401_, v_a_6388_, v_a_6389_, v_a_6390_, v_a_6391_);
return v___x_6402_;
}
else
{
lean_object* v___f_6403_; lean_object* v___x_6404_; lean_object* v___x_6405_; uint8_t v___x_6406_; lean_object* v___y_6408_; lean_object* v___y_6409_; lean_object* v_a_6410_; lean_object* v___y_6423_; lean_object* v___y_6424_; lean_object* v_a_6425_; 
v___f_6403_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___closed__0));
v___x_6404_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_6405_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_6406_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6394_, v_options_6393_, v___x_6405_);
if (v___x_6406_ == 0)
{
lean_object* v___x_6487_; uint8_t v___x_6488_; 
v___x_6487_ = l_Lean_trace_profiler;
v___x_6488_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_6393_, v___x_6487_);
if (v___x_6488_ == 0)
{
lean_object* v___x_6489_; lean_object* v___x_6490_; lean_object* v___x_6491_; lean_object* v___x_6492_; lean_object* v___x_6493_; lean_object* v___f_6494_; lean_object* v___x_6495_; 
v___x_6489_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6490_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6393_, v___x_6489_);
v___x_6491_ = lean_unsigned_to_nat(2u);
v___x_6492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6492_, 0, v___x_6490_);
lean_ctor_set(v___x_6492_, 1, v___x_6491_);
v___x_6493_ = lean_box(v_hasTrace_6395_);
v___f_6494_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed), 11, 4);
lean_closure_set(v___f_6494_, 0, v_m_6387_);
lean_closure_set(v___f_6494_, 1, v___x_6492_);
lean_closure_set(v___f_6494_, 2, v___x_6493_);
lean_closure_set(v___f_6494_, 3, v_cls_6396_);
v___x_6495_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6494_, v_a_6388_, v_a_6389_, v_a_6390_, v_a_6391_);
return v___x_6495_;
}
else
{
goto v___jp_6434_;
}
}
else
{
goto v___jp_6434_;
}
v___jp_6407_:
{
lean_object* v___x_6411_; double v___x_6412_; double v___x_6413_; double v___x_6414_; double v___x_6415_; double v___x_6416_; lean_object* v___x_6417_; lean_object* v___x_6418_; lean_object* v___x_6419_; lean_object* v___x_6420_; lean_object* v___x_6421_; 
v___x_6411_ = lean_io_mono_nanos_now();
v___x_6412_ = lean_float_of_nat(v___y_6408_);
v___x_6413_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_6414_ = lean_float_div(v___x_6412_, v___x_6413_);
v___x_6415_ = lean_float_of_nat(v___x_6411_);
v___x_6416_ = lean_float_div(v___x_6415_, v___x_6413_);
v___x_6417_ = lean_box_float(v___x_6414_);
v___x_6418_ = lean_box_float(v___x_6416_);
v___x_6419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6419_, 0, v___x_6417_);
lean_ctor_set(v___x_6419_, 1, v___x_6418_);
v___x_6420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6420_, 0, v_a_6410_);
lean_ctor_set(v___x_6420_, 1, v___x_6419_);
v___x_6421_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(v_cls_6396_, v_hasTrace_6395_, v___x_6404_, v_options_6393_, v___x_6406_, v___y_6409_, v___f_6403_, v___x_6420_, v_a_6388_, v_a_6389_, v_a_6390_, v_a_6391_);
return v___x_6421_;
}
v___jp_6422_:
{
lean_object* v___x_6426_; double v___x_6427_; double v___x_6428_; lean_object* v___x_6429_; lean_object* v___x_6430_; lean_object* v___x_6431_; lean_object* v___x_6432_; lean_object* v___x_6433_; 
v___x_6426_ = lean_io_get_num_heartbeats();
v___x_6427_ = lean_float_of_nat(v___y_6424_);
v___x_6428_ = lean_float_of_nat(v___x_6426_);
v___x_6429_ = lean_box_float(v___x_6427_);
v___x_6430_ = lean_box_float(v___x_6428_);
v___x_6431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6431_, 0, v___x_6429_);
lean_ctor_set(v___x_6431_, 1, v___x_6430_);
v___x_6432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6432_, 0, v_a_6425_);
lean_ctor_set(v___x_6432_, 1, v___x_6431_);
v___x_6433_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(v_cls_6396_, v_hasTrace_6395_, v___x_6404_, v_options_6393_, v___x_6406_, v___y_6423_, v___f_6403_, v___x_6432_, v_a_6388_, v_a_6389_, v_a_6390_, v_a_6391_);
return v___x_6433_;
}
v___jp_6434_:
{
lean_object* v___x_6435_; lean_object* v_a_6436_; lean_object* v___x_6437_; uint8_t v___x_6438_; 
v___x_6435_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v_a_6391_);
v_a_6436_ = lean_ctor_get(v___x_6435_, 0);
lean_inc(v_a_6436_);
lean_dec_ref(v___x_6435_);
v___x_6437_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6438_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_6393_, v___x_6437_);
if (v___x_6438_ == 0)
{
lean_object* v___x_6439_; lean_object* v___x_6440_; lean_object* v___x_6441_; lean_object* v___x_6442_; lean_object* v___x_6443_; lean_object* v___x_6444_; lean_object* v___f_6445_; lean_object* v___x_6446_; 
v___x_6439_ = lean_io_mono_nanos_now();
v___x_6440_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6441_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6393_, v___x_6440_);
v___x_6442_ = lean_unsigned_to_nat(2u);
v___x_6443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6443_, 0, v___x_6441_);
lean_ctor_set(v___x_6443_, 1, v___x_6442_);
v___x_6444_ = lean_box(v_hasTrace_6395_);
v___f_6445_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed), 11, 4);
lean_closure_set(v___f_6445_, 0, v_m_6387_);
lean_closure_set(v___f_6445_, 1, v___x_6443_);
lean_closure_set(v___f_6445_, 2, v___x_6444_);
lean_closure_set(v___f_6445_, 3, v_cls_6396_);
v___x_6446_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6445_, v_a_6388_, v_a_6389_, v_a_6390_, v_a_6391_);
if (lean_obj_tag(v___x_6446_) == 0)
{
lean_object* v_a_6447_; lean_object* v___x_6449_; uint8_t v_isShared_6450_; uint8_t v_isSharedCheck_6454_; 
v_a_6447_ = lean_ctor_get(v___x_6446_, 0);
v_isSharedCheck_6454_ = !lean_is_exclusive(v___x_6446_);
if (v_isSharedCheck_6454_ == 0)
{
v___x_6449_ = v___x_6446_;
v_isShared_6450_ = v_isSharedCheck_6454_;
goto v_resetjp_6448_;
}
else
{
lean_inc(v_a_6447_);
lean_dec(v___x_6446_);
v___x_6449_ = lean_box(0);
v_isShared_6450_ = v_isSharedCheck_6454_;
goto v_resetjp_6448_;
}
v_resetjp_6448_:
{
lean_object* v___x_6452_; 
if (v_isShared_6450_ == 0)
{
lean_ctor_set_tag(v___x_6449_, 1);
v___x_6452_ = v___x_6449_;
goto v_reusejp_6451_;
}
else
{
lean_object* v_reuseFailAlloc_6453_; 
v_reuseFailAlloc_6453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6453_, 0, v_a_6447_);
v___x_6452_ = v_reuseFailAlloc_6453_;
goto v_reusejp_6451_;
}
v_reusejp_6451_:
{
v___y_6408_ = v___x_6439_;
v___y_6409_ = v_a_6436_;
v_a_6410_ = v___x_6452_;
goto v___jp_6407_;
}
}
}
else
{
lean_object* v_a_6455_; lean_object* v___x_6457_; uint8_t v_isShared_6458_; uint8_t v_isSharedCheck_6462_; 
v_a_6455_ = lean_ctor_get(v___x_6446_, 0);
v_isSharedCheck_6462_ = !lean_is_exclusive(v___x_6446_);
if (v_isSharedCheck_6462_ == 0)
{
v___x_6457_ = v___x_6446_;
v_isShared_6458_ = v_isSharedCheck_6462_;
goto v_resetjp_6456_;
}
else
{
lean_inc(v_a_6455_);
lean_dec(v___x_6446_);
v___x_6457_ = lean_box(0);
v_isShared_6458_ = v_isSharedCheck_6462_;
goto v_resetjp_6456_;
}
v_resetjp_6456_:
{
lean_object* v___x_6460_; 
if (v_isShared_6458_ == 0)
{
lean_ctor_set_tag(v___x_6457_, 0);
v___x_6460_ = v___x_6457_;
goto v_reusejp_6459_;
}
else
{
lean_object* v_reuseFailAlloc_6461_; 
v_reuseFailAlloc_6461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6461_, 0, v_a_6455_);
v___x_6460_ = v_reuseFailAlloc_6461_;
goto v_reusejp_6459_;
}
v_reusejp_6459_:
{
v___y_6408_ = v___x_6439_;
v___y_6409_ = v_a_6436_;
v_a_6410_ = v___x_6460_;
goto v___jp_6407_;
}
}
}
}
else
{
lean_object* v___x_6463_; lean_object* v___x_6464_; lean_object* v___x_6465_; lean_object* v___x_6466_; lean_object* v___x_6467_; lean_object* v___x_6468_; lean_object* v___f_6469_; lean_object* v___x_6470_; 
v___x_6463_ = lean_io_get_num_heartbeats();
v___x_6464_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6465_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6393_, v___x_6464_);
v___x_6466_ = lean_unsigned_to_nat(2u);
v___x_6467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6467_, 0, v___x_6465_);
lean_ctor_set(v___x_6467_, 1, v___x_6466_);
v___x_6468_ = lean_box(v___x_6438_);
v___f_6469_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6___boxed), 11, 4);
lean_closure_set(v___f_6469_, 0, v_m_6387_);
lean_closure_set(v___f_6469_, 1, v___x_6467_);
lean_closure_set(v___f_6469_, 2, v___x_6468_);
lean_closure_set(v___f_6469_, 3, v_cls_6396_);
v___x_6470_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6469_, v_a_6388_, v_a_6389_, v_a_6390_, v_a_6391_);
if (lean_obj_tag(v___x_6470_) == 0)
{
lean_object* v_a_6471_; lean_object* v___x_6473_; uint8_t v_isShared_6474_; uint8_t v_isSharedCheck_6478_; 
v_a_6471_ = lean_ctor_get(v___x_6470_, 0);
v_isSharedCheck_6478_ = !lean_is_exclusive(v___x_6470_);
if (v_isSharedCheck_6478_ == 0)
{
v___x_6473_ = v___x_6470_;
v_isShared_6474_ = v_isSharedCheck_6478_;
goto v_resetjp_6472_;
}
else
{
lean_inc(v_a_6471_);
lean_dec(v___x_6470_);
v___x_6473_ = lean_box(0);
v_isShared_6474_ = v_isSharedCheck_6478_;
goto v_resetjp_6472_;
}
v_resetjp_6472_:
{
lean_object* v___x_6476_; 
if (v_isShared_6474_ == 0)
{
lean_ctor_set_tag(v___x_6473_, 1);
v___x_6476_ = v___x_6473_;
goto v_reusejp_6475_;
}
else
{
lean_object* v_reuseFailAlloc_6477_; 
v_reuseFailAlloc_6477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6477_, 0, v_a_6471_);
v___x_6476_ = v_reuseFailAlloc_6477_;
goto v_reusejp_6475_;
}
v_reusejp_6475_:
{
v___y_6423_ = v_a_6436_;
v___y_6424_ = v___x_6463_;
v_a_6425_ = v___x_6476_;
goto v___jp_6422_;
}
}
}
else
{
lean_object* v_a_6479_; lean_object* v___x_6481_; uint8_t v_isShared_6482_; uint8_t v_isSharedCheck_6486_; 
v_a_6479_ = lean_ctor_get(v___x_6470_, 0);
v_isSharedCheck_6486_ = !lean_is_exclusive(v___x_6470_);
if (v_isSharedCheck_6486_ == 0)
{
v___x_6481_ = v___x_6470_;
v_isShared_6482_ = v_isSharedCheck_6486_;
goto v_resetjp_6480_;
}
else
{
lean_inc(v_a_6479_);
lean_dec(v___x_6470_);
v___x_6481_ = lean_box(0);
v_isShared_6482_ = v_isSharedCheck_6486_;
goto v_resetjp_6480_;
}
v_resetjp_6480_:
{
lean_object* v___x_6484_; 
if (v_isShared_6482_ == 0)
{
lean_ctor_set_tag(v___x_6481_, 0);
v___x_6484_ = v___x_6481_;
goto v_reusejp_6483_;
}
else
{
lean_object* v_reuseFailAlloc_6485_; 
v_reuseFailAlloc_6485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6485_, 0, v_a_6479_);
v___x_6484_ = v_reuseFailAlloc_6485_;
goto v_reusejp_6483_;
}
v_reusejp_6483_:
{
v___y_6423_ = v_a_6436_;
v___y_6424_ = v___x_6463_;
v_a_6425_ = v___x_6484_;
goto v___jp_6422_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___boxed(lean_object* v_m_6496_, lean_object* v_a_6497_, lean_object* v_a_6498_, lean_object* v_a_6499_, lean_object* v_a_6500_, lean_object* v_a_6501_){
_start:
{
lean_object* v_res_6502_; 
v_res_6502_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(v_m_6496_, v_a_6497_, v_a_6498_, v_a_6499_, v_a_6500_);
lean_dec(v_a_6500_);
lean_dec_ref(v_a_6499_);
lean_dec(v_a_6498_);
lean_dec_ref(v_a_6497_);
return v_res_6502_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0(lean_object* v_00_u03b1_6503_, lean_object* v_msg_6504_, lean_object* v___y_6505_, lean_object* v___y_6506_, lean_object* v___y_6507_, lean_object* v___y_6508_, lean_object* v___y_6509_, lean_object* v___y_6510_){
_start:
{
lean_object* v___x_6512_; 
v___x_6512_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v_msg_6504_, v___y_6507_, v___y_6508_, v___y_6509_, v___y_6510_);
return v___x_6512_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___boxed(lean_object* v_00_u03b1_6513_, lean_object* v_msg_6514_, lean_object* v___y_6515_, lean_object* v___y_6516_, lean_object* v___y_6517_, lean_object* v___y_6518_, lean_object* v___y_6519_, lean_object* v___y_6520_, lean_object* v___y_6521_){
_start:
{
lean_object* v_res_6522_; 
v_res_6522_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0(v_00_u03b1_6513_, v_msg_6514_, v___y_6515_, v___y_6516_, v___y_6517_, v___y_6518_, v___y_6519_, v___y_6520_);
lean_dec(v___y_6520_);
lean_dec_ref(v___y_6519_);
lean_dec(v___y_6518_);
lean_dec_ref(v___y_6517_);
lean_dec(v___y_6516_);
lean_dec_ref(v___y_6515_);
return v_res_6522_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1(lean_object* v_cls_6523_, lean_object* v_msg_6524_, lean_object* v___y_6525_, lean_object* v___y_6526_, lean_object* v___y_6527_, lean_object* v___y_6528_, lean_object* v___y_6529_, lean_object* v___y_6530_){
_start:
{
lean_object* v___x_6532_; 
v___x_6532_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_6523_, v_msg_6524_, v___y_6527_, v___y_6528_, v___y_6529_, v___y_6530_);
return v___x_6532_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___boxed(lean_object* v_cls_6533_, lean_object* v_msg_6534_, lean_object* v___y_6535_, lean_object* v___y_6536_, lean_object* v___y_6537_, lean_object* v___y_6538_, lean_object* v___y_6539_, lean_object* v___y_6540_, lean_object* v___y_6541_){
_start:
{
lean_object* v_res_6542_; 
v_res_6542_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1(v_cls_6533_, v_msg_6534_, v___y_6535_, v___y_6536_, v___y_6537_, v___y_6538_, v___y_6539_, v___y_6540_);
lean_dec(v___y_6540_);
lean_dec_ref(v___y_6539_);
lean_dec(v___y_6538_);
lean_dec_ref(v___y_6537_);
lean_dec(v___y_6536_);
lean_dec_ref(v___y_6535_);
return v_res_6542_;
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

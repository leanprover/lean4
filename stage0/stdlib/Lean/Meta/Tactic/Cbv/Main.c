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
lean_object* l_Lean_Meta_Sym_shareCommonInc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_Simp_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_shareCommon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "zeta:"};
static const lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_array_object l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___closed__0_value)}};
static const lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___boxed__const__1 = (const lean_object*)&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___boxed__const__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg(lean_object* v_e_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v_new_490_; lean_object* v___x_491_; 
lean_inc_ref(v_e_482_);
v_new_490_ = l_Lean_Expr_headBeta(v_e_482_);
v___x_491_ = l_Lean_Meta_Sym_shareCommonInc(v_new_490_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v_a_492_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v_options_519_; uint8_t v_hasTrace_520_; 
v_a_492_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_a_492_);
lean_dec_ref_known(v___x_491_, 1);
v_options_519_ = lean_ctor_get(v_a_487_, 2);
v_hasTrace_520_ = lean_ctor_get_uint8(v_options_519_, sizeof(void*)*1);
if (v_hasTrace_520_ == 0)
{
lean_dec_ref(v_e_482_);
v___y_494_ = v_a_483_;
v___y_495_ = v_a_484_;
v___y_496_ = v_a_485_;
v___y_497_ = v_a_486_;
v___y_498_ = v_a_487_;
v___y_499_ = v_a_488_;
goto v___jp_493_;
}
else
{
lean_object* v_inheritedTraceOptions_521_; lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v_inheritedTraceOptions_521_ = lean_ctor_get(v_a_487_, 13);
v___x_522_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_523_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3);
v___x_524_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_521_, v_options_519_, v___x_523_);
if (v___x_524_ == 0)
{
lean_dec_ref(v_e_482_);
v___y_494_ = v_a_483_;
v___y_495_ = v_a_484_;
v___y_496_ = v_a_485_;
v___y_497_ = v_a_486_;
v___y_498_ = v_a_487_;
v___y_499_ = v_a_488_;
goto v___jp_493_;
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_525_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__5, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__5);
v___x_526_ = l_Lean_indentExpr(v_e_482_);
v___x_527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_525_);
lean_ctor_set(v___x_527_, 1, v___x_526_);
v___x_528_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_529_, 0, v___x_527_);
lean_ctor_set(v___x_529_, 1, v___x_528_);
lean_inc(v_a_492_);
v___x_530_ = l_Lean_indentExpr(v_a_492_);
v___x_531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_529_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_522_, v___x_531_, v_a_485_, v_a_486_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_dec_ref_known(v___x_532_, 1);
v___y_494_ = v_a_483_;
v___y_495_ = v_a_484_;
v___y_496_ = v_a_485_;
v___y_497_ = v_a_486_;
v___y_498_ = v_a_487_;
v___y_499_ = v_a_488_;
goto v___jp_493_;
}
else
{
lean_object* v_a_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_540_; 
lean_dec(v_a_492_);
v_a_533_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_540_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_540_ == 0)
{
v___x_535_ = v___x_532_;
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_a_533_);
lean_dec(v___x_532_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_540_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_a_533_);
v___x_538_ = v_reuseFailAlloc_539_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
return v___x_538_;
}
}
}
}
}
v___jp_493_:
{
lean_object* v___x_500_; 
lean_inc(v_a_492_);
v___x_500_ = l_Lean_Meta_Sym_mkEqRefl(v_a_492_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_510_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_510_ == 0)
{
v___x_503_ = v___x_500_;
v_isShared_504_ = v_isSharedCheck_510_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_a_501_);
lean_dec(v___x_500_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_510_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
uint8_t v___x_505_; lean_object* v___x_506_; lean_object* v___x_508_; 
v___x_505_ = 0;
v___x_506_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_506_, 0, v_a_492_);
lean_ctor_set(v___x_506_, 1, v_a_501_);
lean_ctor_set_uint8(v___x_506_, sizeof(void*)*2, v___x_505_);
lean_ctor_set_uint8(v___x_506_, sizeof(void*)*2 + 1, v___x_505_);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_506_);
v___x_508_ = v___x_503_;
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
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_518_; 
lean_dec(v_a_492_);
v_a_511_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_518_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_518_ == 0)
{
v___x_513_ = v___x_500_;
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_500_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_518_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_516_; 
if (v_isShared_514_ == 0)
{
v___x_516_ = v___x_513_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_a_511_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec_ref(v_e_482_);
v_a_541_ = lean_ctor_get(v___x_491_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_491_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_491_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_491_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
return v___x_546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___boxed(lean_object* v_e_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg(v_e_549_, v_a_550_, v_a_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_);
lean_dec(v_a_555_);
lean_dec_ref(v_a_554_);
lean_dec(v_a_553_);
lean_dec_ref(v_a_552_);
lean_dec(v_a_551_);
lean_dec_ref(v_a_550_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce(lean_object* v_e_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
lean_object* v___x_569_; 
v___x_569_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg(v_e_558_, v_a_562_, v_a_563_, v_a_564_, v_a_565_, v_a_566_, v_a_567_);
return v___x_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___boxed(lean_object* v_e_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce(v_e_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_, v_a_577_, v_a_578_, v_a_579_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
lean_dec(v_a_577_);
lean_dec_ref(v_a_576_);
lean_dec(v_a_575_);
lean_dec_ref(v_a_574_);
lean_dec(v_a_573_);
lean_dec_ref(v_a_572_);
lean_dec(v_a_571_);
return v_res_581_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__1(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_583_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__0));
v___x_584_ = l_Lean_stringToMessageData(v___x_583_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(lean_object* v_e_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_596_ = l_Lean_Expr_getAppFn(v_e_585_);
v___x_597_ = l_Lean_Expr_constName_x3f(v___x_596_);
lean_dec_ref(v___x_596_);
if (lean_obj_tag(v___x_597_) == 1)
{
lean_object* v_val_598_; lean_object* v___y_600_; lean_object* v___x_637_; 
v_val_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_val_598_);
lean_dec_ref_known(v___x_597_, 1);
v___x_637_ = l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas___redArg(v_val_598_, v_a_594_);
if (lean_obj_tag(v___x_637_) == 0)
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_663_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_663_ == 0)
{
v___x_640_ = v___x_637_;
v_isShared_641_ = v_isSharedCheck_663_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_637_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_663_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
if (lean_obj_tag(v_a_638_) == 1)
{
lean_object* v_val_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
lean_del_object(v___x_640_);
v_val_642_ = lean_ctor_get(v_a_638_, 0);
lean_inc(v_val_642_);
lean_dec_ref_known(v_a_638_, 1);
v___x_643_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__11));
lean_inc_ref(v_e_585_);
v___x_644_ = l_Lean_Meta_Sym_Simp_Theorems_rewrite(v_val_642_, v___x_643_, v_e_585_, v_a_586_, v_a_587_, v_a_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
lean_dec(v_val_642_);
if (lean_obj_tag(v___x_644_) == 0)
{
v___y_600_ = v___x_644_;
goto v___jp_599_;
}
else
{
lean_object* v_a_645_; uint8_t v___y_647_; uint8_t v___x_657_; 
v_a_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_a_645_);
v___x_657_ = l_Lean_Exception_isInterrupt(v_a_645_);
if (v___x_657_ == 0)
{
uint8_t v___x_658_; 
v___x_658_ = l_Lean_Exception_isRuntime(v_a_645_);
v___y_647_ = v___x_658_;
goto v___jp_646_;
}
else
{
lean_dec(v_a_645_);
v___y_647_ = v___x_657_;
goto v___jp_646_;
}
v___jp_646_:
{
if (v___y_647_ == 0)
{
lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_655_; 
lean_dec(v_val_598_);
lean_dec_ref(v_e_585_);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_644_);
if (v_isSharedCheck_655_ == 0)
{
lean_object* v_unused_656_; 
v_unused_656_ = lean_ctor_get(v___x_644_, 0);
lean_dec(v_unused_656_);
v___x_649_ = v___x_644_;
v_isShared_650_ = v_isSharedCheck_655_;
goto v_resetjp_648_;
}
else
{
lean_dec(v___x_644_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_655_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; lean_object* v___x_653_; 
v___x_651_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_651_, 0, v___y_647_);
lean_ctor_set_uint8(v___x_651_, 1, v___y_647_);
if (v_isShared_650_ == 0)
{
lean_ctor_set_tag(v___x_649_, 0);
lean_ctor_set(v___x_649_, 0, v___x_651_);
v___x_653_ = v___x_649_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_651_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
else
{
v___y_600_ = v___x_644_;
goto v___jp_599_;
}
}
}
}
else
{
lean_object* v___x_659_; lean_object* v___x_661_; 
lean_dec(v_a_638_);
lean_dec(v_val_598_);
lean_dec_ref(v_e_585_);
v___x_659_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_659_);
v___x_661_ = v___x_640_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
else
{
lean_object* v_a_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_671_; 
lean_dec(v_val_598_);
lean_dec_ref(v_e_585_);
v_a_664_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_671_ == 0)
{
v___x_666_ = v___x_637_;
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_a_664_);
lean_dec(v___x_637_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_671_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v___x_669_; 
if (v_isShared_667_ == 0)
{
v___x_669_ = v___x_666_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
v___jp_599_:
{
if (lean_obj_tag(v___y_600_) == 0)
{
lean_object* v_a_601_; 
v_a_601_ = lean_ctor_get(v___y_600_, 0);
if (lean_obj_tag(v_a_601_) == 1)
{
lean_object* v_options_602_; uint8_t v_hasTrace_603_; 
v_options_602_ = lean_ctor_get(v_a_593_, 2);
v_hasTrace_603_ = lean_ctor_get_uint8(v_options_602_, sizeof(void*)*1);
if (v_hasTrace_603_ == 0)
{
lean_dec(v_val_598_);
lean_dec_ref(v_e_585_);
return v___y_600_;
}
else
{
lean_object* v_e_x27_604_; lean_object* v_inheritedTraceOptions_605_; lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v_e_x27_604_ = lean_ctor_get(v_a_601_, 0);
v_inheritedTraceOptions_605_ = lean_ctor_get(v_a_593_, 13);
v___x_606_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__1));
v___x_607_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__4, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__4_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__4);
v___x_608_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_605_, v_options_602_, v___x_607_);
if (v___x_608_ == 0)
{
lean_dec(v_val_598_);
lean_dec_ref(v_e_585_);
return v___y_600_;
}
else
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
lean_inc_ref(v_a_601_);
lean_dec_ref_known(v___y_600_, 1);
v___x_609_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___closed__1);
v___x_610_ = l_Lean_MessageData_ofName(v_val_598_);
v___x_611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_611_, 0, v___x_609_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8);
v___x_613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_611_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
v___x_614_ = l_Lean_indentExpr(v_e_585_);
v___x_615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_613_);
lean_ctor_set(v___x_615_, 1, v___x_614_);
v___x_616_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_615_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
lean_inc_ref(v_e_x27_604_);
v___x_618_ = l_Lean_indentExpr(v_e_x27_604_);
v___x_619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_606_, v___x_619_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
if (lean_obj_tag(v___x_620_) == 0)
{
lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_627_; 
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; 
v_unused_628_ = lean_ctor_get(v___x_620_, 0);
lean_dec(v_unused_628_);
v___x_622_ = v___x_620_;
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
else
{
lean_dec(v___x_620_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_627_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_625_; 
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v_a_601_);
v___x_625_ = v___x_622_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_a_601_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
else
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_636_; 
lean_dec_ref_known(v_a_601_, 2);
v_a_629_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_636_ == 0)
{
v___x_631_ = v___x_620_;
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_620_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_636_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_634_; 
if (v_isShared_632_ == 0)
{
v___x_634_ = v___x_631_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_629_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
}
}
}
}
else
{
lean_dec(v_val_598_);
lean_dec_ref(v_e_585_);
return v___y_600_;
}
}
else
{
lean_dec(v_val_598_);
lean_dec_ref(v_e_585_);
return v___y_600_;
}
}
}
else
{
lean_object* v___x_672_; lean_object* v___x_673_; 
lean_dec(v___x_597_);
lean_dec_ref(v_e_585_);
v___x_672_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems___boxed(lean_object* v_e_674_, lean_object* v_a_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v_e_674_, v_a_675_, v_a_676_, v_a_677_, v_a_678_, v_a_679_, v_a_680_, v_a_681_, v_a_682_, v_a_683_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
lean_dec(v_a_681_);
lean_dec_ref(v_a_680_);
lean_dec(v_a_679_);
lean_dec_ref(v_a_678_);
lean_dec(v_a_677_);
lean_dec_ref(v_a_676_);
lean_dec(v_a_675_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp(lean_object* v_e_686_, lean_object* v_a_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_){
_start:
{
lean_object* v___x_697_; 
lean_inc_ref(v_e_686_);
v___x_697_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations(v_e_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
if (lean_obj_tag(v_a_698_) == 0)
{
uint8_t v_done_699_; 
v_done_699_ = lean_ctor_get_uint8(v_a_698_, 0);
if (v_done_699_ == 0)
{
uint8_t v_contextDependent_700_; lean_object* v___x_701_; 
lean_dec_ref_known(v___x_697_, 1);
v_contextDependent_700_ = lean_ctor_get_uint8(v_a_698_, 1);
lean_dec_ref_known(v_a_698_, 0);
v___x_701_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold(v_e_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v_a_702_; uint8_t v___y_704_; 
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
if (v_contextDependent_700_ == 0)
{
lean_dec(v_a_702_);
return v___x_701_;
}
else
{
if (lean_obj_tag(v_a_702_) == 0)
{
uint8_t v_contextDependent_714_; 
v_contextDependent_714_ = lean_ctor_get_uint8(v_a_702_, 1);
v___y_704_ = v_contextDependent_714_;
goto v___jp_703_;
}
else
{
uint8_t v_contextDependent_715_; 
v_contextDependent_715_ = lean_ctor_get_uint8(v_a_702_, sizeof(void*)*2 + 1);
v___y_704_ = v_contextDependent_715_;
goto v___jp_703_;
}
}
v___jp_703_:
{
if (v___y_704_ == 0)
{
lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_712_; 
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_701_);
if (v_isSharedCheck_712_ == 0)
{
lean_object* v_unused_713_; 
v_unused_713_ = lean_ctor_get(v___x_701_, 0);
lean_dec(v_unused_713_);
v___x_706_ = v___x_701_;
v_isShared_707_ = v_isSharedCheck_712_;
goto v_resetjp_705_;
}
else
{
lean_dec(v___x_701_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_712_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_708_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_702_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v___x_708_);
v___x_710_ = v___x_706_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
else
{
lean_dec(v_a_702_);
return v___x_701_;
}
}
}
else
{
return v___x_701_;
}
}
else
{
lean_dec_ref_known(v_a_698_, 0);
lean_dec_ref(v_e_686_);
return v___x_697_;
}
}
else
{
lean_dec_ref_known(v_a_698_, 2);
lean_dec_ref(v_e_686_);
return v___x_697_;
}
}
else
{
lean_dec_ref(v_e_686_);
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp___boxed(lean_object* v_e_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp(v_e_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
lean_dec(v_a_725_);
lean_dec_ref(v_a_724_);
lean_dec(v_a_723_);
lean_dec_ref(v_a_722_);
lean_dec(v_a_721_);
lean_dec_ref(v_a_720_);
lean_dec(v_a_719_);
lean_dec_ref(v_a_718_);
lean_dec(v_a_717_);
return v_res_727_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0(lean_object* v_a_728_, uint8_t v_done_729_, lean_object* v_x_730_){
_start:
{
uint8_t v___x_731_; 
v___x_731_ = l_Lean_ConstantInfo_hasValue(v_a_728_, v_done_729_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0___boxed(lean_object* v_a_732_, lean_object* v_done_733_, lean_object* v_x_734_){
_start:
{
uint8_t v_done_18197__boxed_735_; uint8_t v_res_736_; lean_object* v_r_737_; 
v_done_18197__boxed_735_ = lean_unbox(v_done_733_);
v_res_736_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0(v_a_732_, v_done_18197__boxed_735_, v_x_734_);
lean_dec_ref(v_x_734_);
lean_dec_ref(v_a_732_);
v_r_737_ = lean_box(v_res_736_);
return v_r_737_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_738_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
return v___x_740_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_741_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_742_ = lean_unsigned_to_nat(0u);
v___x_743_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
lean_ctor_set(v___x_743_, 1, v___x_742_);
lean_ctor_set(v___x_743_, 2, v___x_742_);
lean_ctor_set(v___x_743_, 3, v___x_742_);
lean_ctor_set(v___x_743_, 4, v___x_741_);
lean_ctor_set(v___x_743_, 5, v___x_741_);
lean_ctor_set(v___x_743_, 6, v___x_741_);
lean_ctor_set(v___x_743_, 7, v___x_741_);
lean_ctor_set(v___x_743_, 8, v___x_741_);
lean_ctor_set(v___x_743_, 9, v___x_741_);
return v___x_743_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_744_ = lean_unsigned_to_nat(32u);
v___x_745_ = lean_mk_empty_array_with_capacity(v___x_744_);
v___x_746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
return v___x_746_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_747_ = ((size_t)5ULL);
v___x_748_ = lean_unsigned_to_nat(0u);
v___x_749_ = lean_unsigned_to_nat(32u);
v___x_750_ = lean_mk_empty_array_with_capacity(v___x_749_);
v___x_751_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_752_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_752_, 0, v___x_751_);
lean_ctor_set(v___x_752_, 1, v___x_750_);
lean_ctor_set(v___x_752_, 2, v___x_748_);
lean_ctor_set(v___x_752_, 3, v___x_748_);
lean_ctor_set_usize(v___x_752_, 4, v___x_747_);
return v___x_752_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_753_ = lean_box(1);
v___x_754_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_755_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_756_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
lean_ctor_set(v___x_756_, 1, v___x_754_);
lean_ctor_set(v___x_756_, 2, v___x_753_);
return v___x_756_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7(void){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6));
v___x_759_ = l_Lean_stringToMessageData(v___x_758_);
return v___x_759_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9(void){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8));
v___x_762_ = l_Lean_stringToMessageData(v___x_761_);
return v___x_762_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; 
v___x_764_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10));
v___x_765_ = l_Lean_stringToMessageData(v___x_764_);
return v___x_765_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12));
v___x_768_ = l_Lean_stringToMessageData(v___x_767_);
return v___x_768_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; 
v___x_770_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14));
v___x_771_ = l_Lean_stringToMessageData(v___x_770_);
return v___x_771_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_773_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16));
v___x_774_ = l_Lean_stringToMessageData(v___x_773_);
return v___x_774_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19(void){
_start:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18));
v___x_777_ = l_Lean_stringToMessageData(v___x_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(lean_object* v_msg_778_, lean_object* v_declHint_779_, lean_object* v___y_780_){
_start:
{
lean_object* v___x_782_; lean_object* v_env_783_; uint8_t v___x_784_; 
v___x_782_ = lean_st_ref_get(v___y_780_);
v_env_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc_ref(v_env_783_);
lean_dec(v___x_782_);
v___x_784_ = l_Lean_Name_isAnonymous(v_declHint_779_);
if (v___x_784_ == 0)
{
uint8_t v_isExporting_785_; 
v_isExporting_785_ = lean_ctor_get_uint8(v_env_783_, sizeof(void*)*8);
if (v_isExporting_785_ == 0)
{
lean_object* v___x_786_; 
lean_dec_ref(v_env_783_);
lean_dec(v_declHint_779_);
v___x_786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_786_, 0, v_msg_778_);
return v___x_786_;
}
else
{
lean_object* v___x_787_; uint8_t v___x_788_; 
lean_inc_ref(v_env_783_);
v___x_787_ = l_Lean_Environment_setExporting(v_env_783_, v___x_784_);
lean_inc(v_declHint_779_);
lean_inc_ref(v___x_787_);
v___x_788_ = l_Lean_Environment_contains(v___x_787_, v_declHint_779_, v_isExporting_785_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; 
lean_dec_ref(v___x_787_);
lean_dec_ref(v_env_783_);
lean_dec(v_declHint_779_);
v___x_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_789_, 0, v_msg_778_);
return v___x_789_;
}
else
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v_c_795_; lean_object* v___x_796_; 
v___x_790_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_791_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_792_ = l_Lean_Options_empty;
v___x_793_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_793_, 0, v___x_787_);
lean_ctor_set(v___x_793_, 1, v___x_790_);
lean_ctor_set(v___x_793_, 2, v___x_791_);
lean_ctor_set(v___x_793_, 3, v___x_792_);
lean_inc(v_declHint_779_);
v___x_794_ = l_Lean_MessageData_ofConstName(v_declHint_779_, v___x_784_);
v_c_795_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_795_, 0, v___x_793_);
lean_ctor_set(v_c_795_, 1, v___x_794_);
v___x_796_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_783_, v_declHint_779_);
if (lean_obj_tag(v___x_796_) == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
lean_dec_ref(v_env_783_);
lean_dec(v_declHint_779_);
v___x_797_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_797_);
lean_ctor_set(v___x_798_, 1, v_c_795_);
v___x_799_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
v___x_800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_798_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = l_Lean_MessageData_note(v___x_800_);
v___x_802_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_802_, 0, v_msg_778_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
return v___x_803_;
}
else
{
lean_object* v_val_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_839_; 
v_val_804_ = lean_ctor_get(v___x_796_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_796_);
if (v_isSharedCheck_839_ == 0)
{
v___x_806_ = v___x_796_;
v_isShared_807_ = v_isSharedCheck_839_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_val_804_);
lean_dec(v___x_796_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_839_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v_mod_811_; uint8_t v___x_812_; 
v___x_808_ = lean_box(0);
v___x_809_ = l_Lean_Environment_header(v_env_783_);
lean_dec_ref(v_env_783_);
v___x_810_ = l_Lean_EnvironmentHeader_moduleNames(v___x_809_);
v_mod_811_ = lean_array_get(v___x_808_, v___x_810_, v_val_804_);
lean_dec(v_val_804_);
lean_dec_ref(v___x_810_);
v___x_812_ = l_Lean_isPrivateName(v_declHint_779_);
lean_dec(v_declHint_779_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_824_; 
v___x_813_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
v___x_814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_813_);
lean_ctor_set(v___x_814_, 1, v_c_795_);
v___x_815_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
v___x_816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_814_);
lean_ctor_set(v___x_816_, 1, v___x_815_);
v___x_817_ = l_Lean_MessageData_ofName(v_mod_811_);
v___x_818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_816_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_818_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v___x_821_ = l_Lean_MessageData_note(v___x_820_);
v___x_822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_822_, 0, v_msg_778_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
if (v_isShared_807_ == 0)
{
lean_ctor_set_tag(v___x_806_, 0);
lean_ctor_set(v___x_806_, 0, v___x_822_);
v___x_824_ = v___x_806_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
else
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_837_; 
v___x_826_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
v___x_827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
lean_ctor_set(v___x_827_, 1, v_c_795_);
v___x_828_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
v___x_829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = l_Lean_MessageData_ofName(v_mod_811_);
v___x_831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_829_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
v___x_833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_831_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
v___x_834_ = l_Lean_MessageData_note(v___x_833_);
v___x_835_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_835_, 0, v_msg_778_);
lean_ctor_set(v___x_835_, 1, v___x_834_);
if (v_isShared_807_ == 0)
{
lean_ctor_set_tag(v___x_806_, 0);
lean_ctor_set(v___x_806_, 0, v___x_835_);
v___x_837_ = v___x_806_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_840_; 
lean_dec_ref(v_env_783_);
lean_dec(v_declHint_779_);
v___x_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_840_, 0, v_msg_778_);
return v___x_840_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msg_841_, lean_object* v_declHint_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_841_, v_declHint_842_, v___y_843_);
lean_dec(v___y_843_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_msg_846_, lean_object* v_declHint_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_){
_start:
{
lean_object* v___x_858_; lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_868_; 
v___x_858_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_846_, v_declHint_847_, v___y_856_);
v_a_859_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_868_ == 0)
{
v___x_861_ = v___x_858_;
v_isShared_862_ = v_isSharedCheck_868_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_858_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_868_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_863_ = l_Lean_unknownIdentifierMessageTag;
v___x_864_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v_a_859_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_864_);
v___x_866_ = v___x_861_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_msg_869_, lean_object* v_declHint_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_869_, v_declHint_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(lean_object* v_msg_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_){
_start:
{
lean_object* v_ref_888_; lean_object* v___x_889_; lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_898_; 
v_ref_888_ = lean_ctor_get(v___y_885_, 5);
v___x_889_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
v_a_890_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_898_ == 0)
{
v___x_892_ = v___x_889_;
v_isShared_893_ = v_isSharedCheck_898_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_889_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_898_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_894_; lean_object* v___x_896_; 
lean_inc(v_ref_888_);
v___x_894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_894_, 0, v_ref_888_);
lean_ctor_set(v___x_894_, 1, v_a_890_);
if (v_isShared_893_ == 0)
{
lean_ctor_set_tag(v___x_892_, 1);
lean_ctor_set(v___x_892_, 0, v___x_894_);
v___x_896_ = v___x_892_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v_msg_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* v_ref_906_, lean_object* v_msg_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_fileName_918_; lean_object* v_fileMap_919_; lean_object* v_options_920_; lean_object* v_currRecDepth_921_; lean_object* v_maxRecDepth_922_; lean_object* v_ref_923_; lean_object* v_currNamespace_924_; lean_object* v_openDecls_925_; lean_object* v_initHeartbeats_926_; lean_object* v_maxHeartbeats_927_; lean_object* v_quotContext_928_; lean_object* v_currMacroScope_929_; uint8_t v_diag_930_; lean_object* v_cancelTk_x3f_931_; uint8_t v_suppressElabErrors_932_; lean_object* v_inheritedTraceOptions_933_; lean_object* v_ref_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v_fileName_918_ = lean_ctor_get(v___y_915_, 0);
v_fileMap_919_ = lean_ctor_get(v___y_915_, 1);
v_options_920_ = lean_ctor_get(v___y_915_, 2);
v_currRecDepth_921_ = lean_ctor_get(v___y_915_, 3);
v_maxRecDepth_922_ = lean_ctor_get(v___y_915_, 4);
v_ref_923_ = lean_ctor_get(v___y_915_, 5);
v_currNamespace_924_ = lean_ctor_get(v___y_915_, 6);
v_openDecls_925_ = lean_ctor_get(v___y_915_, 7);
v_initHeartbeats_926_ = lean_ctor_get(v___y_915_, 8);
v_maxHeartbeats_927_ = lean_ctor_get(v___y_915_, 9);
v_quotContext_928_ = lean_ctor_get(v___y_915_, 10);
v_currMacroScope_929_ = lean_ctor_get(v___y_915_, 11);
v_diag_930_ = lean_ctor_get_uint8(v___y_915_, sizeof(void*)*14);
v_cancelTk_x3f_931_ = lean_ctor_get(v___y_915_, 12);
v_suppressElabErrors_932_ = lean_ctor_get_uint8(v___y_915_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_933_ = lean_ctor_get(v___y_915_, 13);
v_ref_934_ = l_Lean_replaceRef(v_ref_906_, v_ref_923_);
lean_inc_ref(v_inheritedTraceOptions_933_);
lean_inc(v_cancelTk_x3f_931_);
lean_inc(v_currMacroScope_929_);
lean_inc(v_quotContext_928_);
lean_inc(v_maxHeartbeats_927_);
lean_inc(v_initHeartbeats_926_);
lean_inc(v_openDecls_925_);
lean_inc(v_currNamespace_924_);
lean_inc(v_maxRecDepth_922_);
lean_inc(v_currRecDepth_921_);
lean_inc_ref(v_options_920_);
lean_inc_ref(v_fileMap_919_);
lean_inc_ref(v_fileName_918_);
v___x_935_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_935_, 0, v_fileName_918_);
lean_ctor_set(v___x_935_, 1, v_fileMap_919_);
lean_ctor_set(v___x_935_, 2, v_options_920_);
lean_ctor_set(v___x_935_, 3, v_currRecDepth_921_);
lean_ctor_set(v___x_935_, 4, v_maxRecDepth_922_);
lean_ctor_set(v___x_935_, 5, v_ref_934_);
lean_ctor_set(v___x_935_, 6, v_currNamespace_924_);
lean_ctor_set(v___x_935_, 7, v_openDecls_925_);
lean_ctor_set(v___x_935_, 8, v_initHeartbeats_926_);
lean_ctor_set(v___x_935_, 9, v_maxHeartbeats_927_);
lean_ctor_set(v___x_935_, 10, v_quotContext_928_);
lean_ctor_set(v___x_935_, 11, v_currMacroScope_929_);
lean_ctor_set(v___x_935_, 12, v_cancelTk_x3f_931_);
lean_ctor_set(v___x_935_, 13, v_inheritedTraceOptions_933_);
lean_ctor_set_uint8(v___x_935_, sizeof(void*)*14, v_diag_930_);
lean_ctor_set_uint8(v___x_935_, sizeof(void*)*14 + 1, v_suppressElabErrors_932_);
v___x_936_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_907_, v___y_913_, v___y_914_, v___x_935_, v___y_916_);
lean_dec_ref_known(v___x_935_, 14);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_ref_937_, lean_object* v_msg_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_937_, v_msg_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec_ref(v___y_940_);
lean_dec(v___y_939_);
lean_dec(v_ref_937_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_ref_950_, lean_object* v_msg_951_, lean_object* v_declHint_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v___x_963_; lean_object* v_a_964_; lean_object* v___x_965_; 
v___x_963_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_951_, v_declHint_952_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
v_a_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_a_964_);
lean_dec_ref(v___x_963_);
v___x_965_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_950_, v_a_964_, v___y_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_ref_966_, lean_object* v_msg_967_, lean_object* v_declHint_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_966_, v_msg_967_, v_declHint_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec(v_ref_966_);
return v_res_979_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_982_ = l_Lean_stringToMessageData(v___x_981_);
return v___x_982_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_985_ = l_Lean_stringToMessageData(v___x_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_986_, lean_object* v_constName_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_){
_start:
{
lean_object* v___x_998_; uint8_t v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
v___x_998_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_999_ = 0;
lean_inc(v_constName_987_);
v___x_1000_ = l_Lean_MessageData_ofConstName(v_constName_987_, v___x_999_);
v___x_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_998_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
v___x_1002_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_1003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1003_, 0, v___x_1001_);
lean_ctor_set(v___x_1003_, 1, v___x_1002_);
v___x_1004_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_986_, v___x_1003_, v_constName_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_1005_, lean_object* v_constName_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg(v_ref_1005_, v_constName_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec(v_ref_1005_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg(lean_object* v_constName_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_ref_1029_; lean_object* v___x_1030_; 
v_ref_1029_ = lean_ctor_get(v___y_1026_, 5);
v___x_1030_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg(v_ref_1029_, v_constName_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg(v_constName_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(lean_object* v_constName_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_){
_start:
{
lean_object* v___x_1054_; lean_object* v_env_1055_; uint8_t v___x_1056_; lean_object* v___x_1057_; 
v___x_1054_ = lean_st_ref_get(v___y_1052_);
v_env_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc_ref(v_env_1055_);
lean_dec(v___x_1054_);
v___x_1056_ = 0;
lean_inc(v_constName_1043_);
v___x_1057_ = l_Lean_Environment_find_x3f(v_env_1055_, v_constName_1043_, v___x_1056_);
if (lean_obj_tag(v___x_1057_) == 0)
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg(v_constName_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_);
return v___x_1058_;
}
else
{
lean_object* v_val_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_dec(v_constName_1043_);
v_val_1059_ = lean_ctor_get(v___x_1057_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_1057_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_1057_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_val_1059_);
lean_dec(v___x_1057_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
lean_ctor_set_tag(v___x_1061_, 0);
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_val_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0___boxed(lean_object* v_constName_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(v_constName_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp(lean_object* v_e_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_){
_start:
{
lean_object* v___y_1091_; lean_object* v___y_1092_; uint8_t v___y_1093_; uint8_t v___x_1096_; 
v___x_1096_ = l_Lean_Expr_isApp(v_e_1079_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; lean_object* v___x_1098_; 
lean_dec_ref(v_e_1079_);
v___x_1097_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_1097_, 0, v___x_1096_);
lean_ctor_set_uint8(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
return v___x_1098_;
}
else
{
lean_object* v_fn_1099_; 
v_fn_1099_ = l_Lean_Expr_getAppFn(v_e_1079_);
switch(lean_obj_tag(v_fn_1099_))
{
case 4:
{
lean_object* v_declName_1100_; lean_object* v___x_1101_; 
v_declName_1100_ = lean_ctor_get(v_fn_1099_, 0);
lean_inc(v_declName_1100_);
lean_dec_ref_known(v_fn_1099_, 2);
v___x_1101_ = l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(v_declName_1100_, v_a_1088_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; uint8_t v___x_1103_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_a_1102_);
lean_dec_ref_known(v___x_1101_, 1);
v___x_1103_ = lean_unbox(v_a_1102_);
lean_dec(v_a_1102_);
if (v___x_1103_ == 0)
{
lean_object* v___x_1104_; 
v___x_1104_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(v_declName_1100_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; lean_object* v___x_1106_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref_known(v___x_1104_, 1);
lean_inc_ref(v_e_1079_);
v___x_1106_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v_e_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
if (lean_obj_tag(v___x_1106_) == 0)
{
lean_object* v_a_1107_; 
v_a_1107_ = lean_ctor_get(v___x_1106_, 0);
lean_inc(v_a_1107_);
if (lean_obj_tag(v_a_1107_) == 0)
{
uint8_t v_done_1108_; uint8_t v_contextDependent_1109_; lean_object* v___y_1111_; lean_object* v_a_1112_; lean_object* v___y_1116_; 
v_done_1108_ = lean_ctor_get_uint8(v_a_1107_, 0);
v_contextDependent_1109_ = lean_ctor_get_uint8(v_a_1107_, 1);
lean_dec_ref_known(v_a_1107_, 0);
if (v_done_1108_ == 0)
{
lean_object* v___x_1118_; lean_object* v___f_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_dec_ref_known(v___x_1106_, 1);
v___x_1118_ = lean_box(v_done_1108_);
v___f_1119_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1119_, 0, v_a_1105_);
lean_closure_set(v___f_1119_, 1, v___x_1118_);
v___x_1120_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConstApp___boxed), 11, 0);
lean_inc_ref(v_e_1079_);
v___x_1121_ = l_Lean_Meta_Tactic_Cbv_guardSimproc(v___f_1119_, v___x_1120_, v_e_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
lean_inc(v_a_1122_);
if (lean_obj_tag(v_a_1122_) == 0)
{
uint8_t v_done_1123_; 
v_done_1123_ = lean_ctor_get_uint8(v_a_1122_, 0);
if (v_done_1123_ == 0)
{
uint8_t v_contextDependent_1124_; lean_object* v___x_1125_; 
lean_dec_ref_known(v___x_1121_, 1);
v_contextDependent_1124_ = lean_ctor_get_uint8(v_a_1122_, 1);
lean_dec_ref_known(v_a_1122_, 0);
v___x_1125_ = l_Lean_Meta_Tactic_Cbv_reduceRecMatcher(v_e_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; uint8_t v___y_1128_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_a_1126_);
if (v_contextDependent_1124_ == 0)
{
lean_dec(v_a_1126_);
v___y_1116_ = v___x_1125_;
goto v___jp_1115_;
}
else
{
if (lean_obj_tag(v_a_1126_) == 0)
{
uint8_t v_contextDependent_1138_; 
v_contextDependent_1138_ = lean_ctor_get_uint8(v_a_1126_, 1);
v___y_1128_ = v_contextDependent_1138_;
goto v___jp_1127_;
}
else
{
uint8_t v_contextDependent_1139_; 
v_contextDependent_1139_ = lean_ctor_get_uint8(v_a_1126_, sizeof(void*)*2 + 1);
v___y_1128_ = v_contextDependent_1139_;
goto v___jp_1127_;
}
}
v___jp_1127_:
{
if (v___y_1128_ == 0)
{
lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1136_; 
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1136_ == 0)
{
lean_object* v_unused_1137_; 
v_unused_1137_ = lean_ctor_get(v___x_1125_, 0);
lean_dec(v_unused_1137_);
v___x_1130_ = v___x_1125_;
v_isShared_1131_ = v_isSharedCheck_1136_;
goto v_resetjp_1129_;
}
else
{
lean_dec(v___x_1125_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1136_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1132_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_1126_);
lean_inc_ref(v___x_1132_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v___x_1132_);
v___x_1134_ = v___x_1130_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
v___y_1111_ = v___x_1134_;
v_a_1112_ = v___x_1132_;
goto v___jp_1110_;
}
}
}
else
{
lean_dec(v_a_1126_);
v___y_1116_ = v___x_1125_;
goto v___jp_1115_;
}
}
}
else
{
v___y_1116_ = v___x_1125_;
goto v___jp_1115_;
}
}
else
{
lean_dec_ref_known(v_a_1122_, 0);
lean_dec_ref(v_e_1079_);
v___y_1116_ = v___x_1121_;
goto v___jp_1115_;
}
}
else
{
lean_dec_ref_known(v_a_1122_, 2);
lean_dec_ref(v_e_1079_);
v___y_1116_ = v___x_1121_;
goto v___jp_1115_;
}
}
else
{
lean_dec_ref(v_e_1079_);
v___y_1116_ = v___x_1121_;
goto v___jp_1115_;
}
}
else
{
lean_dec(v_a_1105_);
lean_dec_ref(v_e_1079_);
return v___x_1106_;
}
v___jp_1110_:
{
if (v_contextDependent_1109_ == 0)
{
lean_dec_ref(v_a_1112_);
return v___y_1111_;
}
else
{
if (lean_obj_tag(v_a_1112_) == 0)
{
uint8_t v_contextDependent_1113_; 
v_contextDependent_1113_ = lean_ctor_get_uint8(v_a_1112_, 1);
v___y_1091_ = v_a_1112_;
v___y_1092_ = v___y_1111_;
v___y_1093_ = v_contextDependent_1113_;
goto v___jp_1090_;
}
else
{
uint8_t v_contextDependent_1114_; 
v_contextDependent_1114_ = lean_ctor_get_uint8(v_a_1112_, sizeof(void*)*2 + 1);
v___y_1091_ = v_a_1112_;
v___y_1092_ = v___y_1111_;
v___y_1093_ = v_contextDependent_1114_;
goto v___jp_1090_;
}
}
}
v___jp_1115_:
{
if (lean_obj_tag(v___y_1116_) == 0)
{
lean_object* v_a_1117_; 
v_a_1117_ = lean_ctor_get(v___y_1116_, 0);
lean_inc(v_a_1117_);
v___y_1111_ = v___y_1116_;
v_a_1112_ = v_a_1117_;
goto v___jp_1110_;
}
else
{
return v___y_1116_;
}
}
}
else
{
lean_dec_ref_known(v_a_1107_, 2);
lean_dec(v_a_1105_);
lean_dec_ref(v_e_1079_);
return v___x_1106_;
}
}
else
{
lean_dec(v_a_1105_);
lean_dec_ref(v_e_1079_);
return v___x_1106_;
}
}
else
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1147_; 
lean_dec_ref(v_e_1079_);
v_a_1140_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1147_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1147_ == 0)
{
v___x_1142_ = v___x_1104_;
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1104_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1147_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1145_; 
if (v_isShared_1143_ == 0)
{
v___x_1145_ = v___x_1142_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
v___x_1145_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
return v___x_1145_;
}
}
}
}
else
{
lean_object* v___x_1148_; 
lean_dec(v_declName_1100_);
v___x_1148_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v_e_1079_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1157_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1151_ = v___x_1148_;
v_isShared_1152_ = v_isSharedCheck_1157_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1148_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1157_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1153_ = l_Lean_Meta_Tactic_Cbv_markAsDoneIfFailed(v_a_1149_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1153_);
v___x_1155_ = v___x_1151_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
else
{
return v___x_1148_;
}
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec(v_declName_1100_);
lean_dec_ref(v_e_1079_);
v_a_1158_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1101_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1101_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
case 6:
{
lean_object* v___x_1166_; 
lean_dec_ref_known(v_fn_1099_, 3);
v___x_1166_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg(v_e_1079_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
return v___x_1166_;
}
default: 
{
lean_object* v___x_1167_; lean_object* v___x_1168_; 
lean_dec_ref(v_fn_1099_);
lean_dec_ref(v_e_1079_);
v___x_1167_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_1168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1167_);
return v___x_1168_;
}
}
}
v___jp_1090_:
{
if (v___y_1093_ == 0)
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
lean_dec_ref(v___y_1092_);
v___x_1094_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_1091_);
v___x_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
return v___x_1095_;
}
else
{
lean_dec_ref(v___y_1091_);
return v___y_1092_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp___boxed(lean_object* v_e_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp(v_e_1169_, v_a_1170_, v_a_1171_, v_a_1172_, v_a_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_);
lean_dec(v_a_1178_);
lean_dec_ref(v_a_1177_);
lean_dec(v_a_1176_);
lean_dec_ref(v_a_1175_);
lean_dec(v_a_1174_);
lean_dec_ref(v_a_1173_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
lean_dec(v_a_1170_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0(lean_object* v_00_u03b1_1181_, lean_object* v_constName_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v___x_1193_; 
v___x_1193_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___redArg(v_constName_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1194_, lean_object* v_constName_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0(v_00_u03b1_1194_, v_constName_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_1207_, lean_object* v_ref_1208_, lean_object* v_constName_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
lean_object* v___x_1220_; 
v___x_1220_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___redArg(v_ref_1208_, v_constName_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
return v___x_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_1221_, lean_object* v_ref_1222_, lean_object* v_constName_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1(v_00_u03b1_1221_, v_ref_1222_, v_constName_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec(v_ref_1222_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b1_1235_, lean_object* v_ref_1236_, lean_object* v_msg_1237_, lean_object* v_declHint_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1236_, v_msg_1237_, v_declHint_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1250_, lean_object* v_ref_1251_, lean_object* v_msg_1252_, lean_object* v_declHint_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v_res_1264_; 
v_res_1264_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1250_, v_ref_1251_, v_msg_1252_, v_declHint_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec(v_ref_1251_);
return v_res_1264_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(lean_object* v_msg_1265_, lean_object* v_declHint_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1265_, v_declHint_1266_, v___y_1275_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1278_, lean_object* v_declHint_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1278_, v_declHint_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, v___y_1288_);
lean_dec(v___y_1288_);
lean_dec_ref(v___y_1287_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4(lean_object* v_00_u03b1_1291_, lean_object* v_ref_1292_, lean_object* v_msg_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_, lean_object* v___y_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1292_, v_msg_1293_, v___y_1294_, v___y_1295_, v___y_1296_, v___y_1297_, v___y_1298_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(lean_object* v_00_u03b1_1305_, lean_object* v_ref_1306_, lean_object* v_msg_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1305_, v_ref_1306_, v_msg_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec(v_ref_1306_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(lean_object* v_00_u03b1_1319_, lean_object* v_msg_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1320_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(lean_object* v_00_u03b1_1332_, lean_object* v_msg_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_1332_, v_msg_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleOpaqueConst(lean_object* v_e_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
if (lean_obj_tag(v_e_1345_) == 4)
{
lean_object* v_declName_1356_; lean_object* v___x_1357_; 
v_declName_1356_ = lean_ctor_get(v_e_1345_, 0);
v___x_1357_ = l_Lean_Meta_Tactic_Cbv_isCbvOpaque___redArg(v_declName_1356_, v_a_1354_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1379_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1360_ = v___x_1357_;
v_isShared_1361_ = v_isSharedCheck_1379_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1379_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
uint8_t v___x_1362_; 
v___x_1362_ = lean_unbox(v_a_1358_);
if (v___x_1362_ == 0)
{
lean_object* v___x_1363_; uint8_t v___x_1364_; uint8_t v___x_1365_; lean_object* v___x_1367_; 
lean_dec_ref_known(v_e_1345_, 2);
v___x_1363_ = lean_alloc_ctor(0, 0, 2);
v___x_1364_ = lean_unbox(v_a_1358_);
lean_ctor_set_uint8(v___x_1363_, 0, v___x_1364_);
v___x_1365_ = lean_unbox(v_a_1358_);
lean_dec(v_a_1358_);
lean_ctor_set_uint8(v___x_1363_, 1, v___x_1365_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v___x_1363_);
v___x_1367_ = v___x_1360_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1363_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
else
{
lean_object* v___x_1369_; 
lean_del_object(v___x_1360_);
lean_dec(v_a_1358_);
v___x_1369_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v_e_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v_a_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1378_; 
v_a_1370_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1372_ = v___x_1369_;
v_isShared_1373_ = v_isSharedCheck_1378_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_a_1370_);
lean_dec(v___x_1369_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1378_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1374_ = l_Lean_Meta_Tactic_Cbv_markAsDoneIfFailed(v_a_1370_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 0, v___x_1374_);
v___x_1376_ = v___x_1372_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
else
{
return v___x_1369_;
}
}
}
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_dec_ref_known(v_e_1345_, 2);
v_a_1380_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1357_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1357_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
else
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
lean_dec_ref(v_e_1345_);
v___x_1388_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_1389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1389_, 0, v___x_1388_);
return v___x_1389_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleOpaqueConst___boxed(lean_object* v_e_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_, lean_object* v_a_1396_, lean_object* v_a_1397_, lean_object* v_a_1398_, lean_object* v_a_1399_, lean_object* v_a_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleOpaqueConst(v_e_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_, v_a_1395_, v_a_1396_, v_a_1397_, v_a_1398_, v_a_1399_);
lean_dec(v_a_1399_);
lean_dec_ref(v_a_1398_);
lean_dec(v_a_1397_);
lean_dec_ref(v_a_1396_);
lean_dec(v_a_1395_);
lean_dec_ref(v_a_1394_);
lean_dec(v_a_1393_);
lean_dec_ref(v_a_1392_);
lean_dec(v_a_1391_);
return v_res_1401_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1(void){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1403_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__0));
v___x_1404_ = l_Lean_stringToMessageData(v___x_1403_);
return v___x_1404_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3(void){
_start:
{
lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1406_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__2));
v___x_1407_ = l_Lean_stringToMessageData(v___x_1406_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(lean_object* v_e_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_){
_start:
{
lean_object* v___x_1416_; 
lean_inc_ref(v_e_1408_);
v___x_1416_ = l_Lean_Expr_rawNatLit_x3f(v_e_1408_);
if (lean_obj_tag(v___x_1416_) == 1)
{
lean_object* v_val_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v_val_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_val_1417_);
lean_dec_ref_known(v___x_1416_, 1);
v___x_1418_ = l_Lean_mkNatLit(v_val_1417_);
v___x_1419_ = l_Lean_Meta_Sym_shareCommonInc(v___x_1418_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v___y_1422_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; lean_object* v_options_1447_; uint8_t v_hasTrace_1448_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
lean_dec_ref_known(v___x_1419_, 1);
v_options_1447_ = lean_ctor_get(v_a_1413_, 2);
v_hasTrace_1448_ = lean_ctor_get_uint8(v_options_1447_, sizeof(void*)*1);
if (v_hasTrace_1448_ == 0)
{
v___y_1422_ = v_a_1409_;
v___y_1423_ = v_a_1410_;
v___y_1424_ = v_a_1411_;
v___y_1425_ = v_a_1412_;
v___y_1426_ = v_a_1413_;
v___y_1427_ = v_a_1414_;
goto v___jp_1421_;
}
else
{
lean_object* v_inheritedTraceOptions_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
v_inheritedTraceOptions_1449_ = lean_ctor_get(v_a_1413_, 13);
v___x_1450_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_1451_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3);
v___x_1452_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1449_, v_options_1447_, v___x_1451_);
if (v___x_1452_ == 0)
{
v___y_1422_ = v_a_1409_;
v___y_1423_ = v_a_1410_;
v___y_1424_ = v_a_1411_;
v___y_1425_ = v_a_1412_;
v___y_1426_ = v_a_1413_;
v___y_1427_ = v_a_1414_;
goto v___jp_1421_;
}
else
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1453_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__1);
lean_inc_ref(v_e_1408_);
v___x_1454_ = l_Lean_MessageData_ofExpr(v_e_1408_);
v___x_1455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1455_, 0, v___x_1453_);
lean_ctor_set(v___x_1455_, 1, v___x_1454_);
v___x_1456_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___closed__3);
v___x_1457_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1455_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
lean_inc(v_a_1420_);
v___x_1458_ = l_Lean_MessageData_ofExpr(v_a_1420_);
v___x_1459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1459_, 0, v___x_1457_);
lean_ctor_set(v___x_1459_, 1, v___x_1458_);
v___x_1460_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_1450_, v___x_1459_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_dec_ref_known(v___x_1460_, 1);
v___y_1422_ = v_a_1409_;
v___y_1423_ = v_a_1410_;
v___y_1424_ = v_a_1411_;
v___y_1425_ = v_a_1412_;
v___y_1426_ = v_a_1413_;
v___y_1427_ = v_a_1414_;
goto v___jp_1421_;
}
else
{
lean_object* v_a_1461_; lean_object* v___x_1463_; uint8_t v_isShared_1464_; uint8_t v_isSharedCheck_1468_; 
lean_dec(v_a_1420_);
lean_dec_ref(v_e_1408_);
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1468_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1468_ == 0)
{
v___x_1463_ = v___x_1460_;
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
else
{
lean_inc(v_a_1461_);
lean_dec(v___x_1460_);
v___x_1463_ = lean_box(0);
v_isShared_1464_ = v_isSharedCheck_1468_;
goto v_resetjp_1462_;
}
v_resetjp_1462_:
{
lean_object* v___x_1466_; 
if (v_isShared_1464_ == 0)
{
v___x_1466_ = v___x_1463_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1467_; 
v_reuseFailAlloc_1467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1467_, 0, v_a_1461_);
v___x_1466_ = v_reuseFailAlloc_1467_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
return v___x_1466_;
}
}
}
}
}
v___jp_1421_:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Lean_Meta_Sym_mkEqRefl(v_e_1408_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1438_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1438_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1438_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
uint8_t v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1436_; 
v___x_1433_ = 0;
v___x_1434_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1434_, 0, v_a_1420_);
lean_ctor_set(v___x_1434_, 1, v_a_1429_);
lean_ctor_set_uint8(v___x_1434_, sizeof(void*)*2, v___x_1433_);
lean_ctor_set_uint8(v___x_1434_, sizeof(void*)*2 + 1, v___x_1433_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1434_);
v___x_1436_ = v___x_1431_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1434_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec(v_a_1420_);
v_a_1439_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1428_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1428_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
}
else
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec_ref(v_e_1408_);
v_a_1469_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1419_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1419_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
lean_dec(v___x_1416_);
lean_dec_ref(v_e_1408_);
v___x_1477_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
return v___x_1478_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg___boxed(lean_object* v_e_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_, lean_object* v_a_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_){
_start:
{
lean_object* v_res_1487_; 
v_res_1487_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(v_e_1479_, v_a_1480_, v_a_1481_, v_a_1482_, v_a_1483_, v_a_1484_, v_a_1485_);
lean_dec(v_a_1485_);
lean_dec_ref(v_a_1484_);
lean_dec(v_a_1483_);
lean_dec_ref(v_a_1482_);
lean_dec(v_a_1481_);
lean_dec_ref(v_a_1480_);
return v_res_1487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit(lean_object* v_e_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(v_e_1488_, v_a_1492_, v_a_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___boxed(lean_object* v_e_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit(v_e_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_);
lean_dec(v_a_1509_);
lean_dec_ref(v_a_1508_);
lean_dec(v_a_1507_);
lean_dec_ref(v_a_1506_);
lean_dec(v_a_1505_);
lean_dec_ref(v_a_1504_);
lean_dec(v_a_1503_);
lean_dec_ref(v_a_1502_);
lean_dec(v_a_1501_);
return v_res_1511_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__0));
v___x_1514_ = l_Lean_stringToMessageData(v___x_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(lean_object* v_e_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_){
_start:
{
if (lean_obj_tag(v_e_1515_) == 8)
{
lean_object* v_value_1523_; lean_object* v_body_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; lean_object* v_new_1529_; lean_object* v___x_1530_; 
v_value_1523_ = lean_ctor_get(v_e_1515_, 2);
v_body_1524_ = lean_ctor_get(v_e_1515_, 3);
v___x_1525_ = lean_unsigned_to_nat(1u);
v___x_1526_ = lean_mk_empty_array_with_capacity(v___x_1525_);
lean_inc_ref(v_value_1523_);
v___x_1527_ = lean_array_push(v___x_1526_, v_value_1523_);
v___x_1528_ = 1;
v_new_1529_ = l_Lean_Meta_expandLet(v_body_1524_, v___x_1527_, v___x_1528_);
v___x_1530_ = l_Lean_Meta_Sym_shareCommonInc(v_new_1529_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; lean_object* v___y_1533_; lean_object* v___y_1534_; lean_object* v___y_1535_; lean_object* v___y_1536_; lean_object* v___y_1537_; lean_object* v___y_1538_; lean_object* v_options_1558_; uint8_t v_hasTrace_1559_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v___x_1530_, 1);
v_options_1558_ = lean_ctor_get(v_a_1520_, 2);
v_hasTrace_1559_ = lean_ctor_get_uint8(v_options_1558_, sizeof(void*)*1);
if (v_hasTrace_1559_ == 0)
{
lean_dec_ref_known(v_e_1515_, 4);
v___y_1533_ = v_a_1516_;
v___y_1534_ = v_a_1517_;
v___y_1535_ = v_a_1518_;
v___y_1536_ = v_a_1519_;
v___y_1537_ = v_a_1520_;
v___y_1538_ = v_a_1521_;
goto v___jp_1532_;
}
else
{
lean_object* v_inheritedTraceOptions_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; uint8_t v___x_1563_; 
v_inheritedTraceOptions_1560_ = lean_ctor_get(v_a_1520_, 13);
v___x_1561_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_1562_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3);
v___x_1563_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1560_, v_options_1558_, v___x_1562_);
if (v___x_1563_ == 0)
{
lean_dec_ref_known(v_e_1515_, 4);
v___y_1533_ = v_a_1516_;
v___y_1534_ = v_a_1517_;
v___y_1535_ = v_a_1518_;
v___y_1536_ = v_a_1519_;
v___y_1537_ = v_a_1520_;
v___y_1538_ = v_a_1521_;
goto v___jp_1532_;
}
else
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1564_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___closed__1);
v___x_1565_ = l_Lean_indentExpr(v_e_1515_);
v___x_1566_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1564_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
v___x_1567_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_1568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1566_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
lean_inc(v_a_1531_);
v___x_1569_ = l_Lean_indentExpr(v_a_1531_);
v___x_1570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1568_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
v___x_1571_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_1561_, v___x_1570_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_dec_ref_known(v___x_1571_, 1);
v___y_1533_ = v_a_1516_;
v___y_1534_ = v_a_1517_;
v___y_1535_ = v_a_1518_;
v___y_1536_ = v_a_1519_;
v___y_1537_ = v_a_1520_;
v___y_1538_ = v_a_1521_;
goto v___jp_1532_;
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_dec(v_a_1531_);
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1571_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1571_);
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
}
v___jp_1532_:
{
lean_object* v___x_1539_; 
lean_inc(v_a_1531_);
v___x_1539_ = l_Lean_Meta_Sym_mkEqRefl(v_a_1531_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1549_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1549_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1549_ == 0)
{
v___x_1542_ = v___x_1539_;
v_isShared_1543_ = v_isSharedCheck_1549_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1549_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
uint8_t v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1547_; 
v___x_1544_ = 0;
v___x_1545_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_1545_, 0, v_a_1531_);
lean_ctor_set(v___x_1545_, 1, v_a_1540_);
lean_ctor_set_uint8(v___x_1545_, sizeof(void*)*2, v___x_1544_);
lean_ctor_set_uint8(v___x_1545_, sizeof(void*)*2 + 1, v___x_1544_);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v___x_1545_);
v___x_1547_ = v___x_1542_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1545_);
v___x_1547_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
return v___x_1547_;
}
}
}
else
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1557_; 
lean_dec(v_a_1531_);
v_a_1550_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1552_ = v___x_1539_;
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1539_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1557_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v___x_1555_; 
if (v_isShared_1553_ == 0)
{
v___x_1555_ = v___x_1552_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_a_1550_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec_ref_known(v_e_1515_, 4);
v_a_1580_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1530_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1530_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
else
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
lean_dec_ref(v_e_1515_);
v___x_1588_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_1589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
return v___x_1589_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg___boxed(lean_object* v_e_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_, lean_object* v_a_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(v_e_1590_, v_a_1591_, v_a_1592_, v_a_1593_, v_a_1594_, v_a_1595_, v_a_1596_);
lean_dec(v_a_1596_);
lean_dec_ref(v_a_1595_);
lean_dec(v_a_1594_);
lean_dec_ref(v_a_1593_);
lean_dec(v_a_1592_);
lean_dec_ref(v_a_1591_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce(lean_object* v_e_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v___x_1610_; 
v___x_1610_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(v_e_1599_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___boxed(lean_object* v_e_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce(v_e_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_);
lean_dec(v_a_1620_);
lean_dec_ref(v_a_1619_);
lean_dec(v_a_1618_);
lean_dec_ref(v_a_1617_);
lean_dec(v_a_1616_);
lean_dec_ref(v_a_1615_);
lean_dec(v_a_1614_);
lean_dec_ref(v_a_1613_);
lean_dec(v_a_1612_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(lean_object* v_structName_1623_, lean_object* v_idx_1624_, lean_object* v_struct_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___y_1634_; lean_object* v___x_1637_; uint8_t v_debug_1638_; 
v___x_1637_ = lean_st_ref_get(v___y_1627_);
v_debug_1638_ = lean_ctor_get_uint8(v___x_1637_, sizeof(void*)*10);
lean_dec(v___x_1637_);
if (v_debug_1638_ == 0)
{
v___y_1634_ = v___y_1627_;
goto v___jp_1633_;
}
else
{
lean_object* v___x_1639_; 
lean_inc_ref(v_struct_1625_);
v___x_1639_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_struct_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
if (lean_obj_tag(v___x_1639_) == 0)
{
lean_dec_ref_known(v___x_1639_, 1);
v___y_1634_ = v___y_1627_;
goto v___jp_1633_;
}
else
{
lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1647_; 
lean_dec_ref(v_struct_1625_);
lean_dec(v_idx_1624_);
lean_dec(v_structName_1623_);
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1647_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1645_; 
if (v_isShared_1643_ == 0)
{
v___x_1645_ = v___x_1642_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_a_1640_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
v___jp_1633_:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = l_Lean_Expr_proj___override(v_structName_1623_, v_idx_1624_, v_struct_1625_);
v___x_1636_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_1635_, v___y_1634_);
return v___x_1636_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg___boxed(lean_object* v_structName_1648_, lean_object* v_idx_1649_, lean_object* v_struct_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_structName_1648_, v_idx_1649_, v_struct_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
lean_dec(v___y_1656_);
lean_dec_ref(v___y_1655_);
lean_dec(v___y_1654_);
lean_dec_ref(v___y_1653_);
lean_dec(v___y_1652_);
lean_dec_ref(v___y_1651_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0(lean_object* v_structName_1659_, lean_object* v_idx_1660_, lean_object* v_struct_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_structName_1659_, v_idx_1660_, v_struct_1661_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___boxed(lean_object* v_structName_1673_, lean_object* v_idx_1674_, lean_object* v_struct_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0(v_structName_1673_, v_idx_1674_, v_struct_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
return v_res_1686_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l_Lean_Meta_Sym_Simp_instInhabitedSimpM(lean_box(0));
return v___x_1687_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(lean_object* v_msg_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_146520__overap_1700_; lean_object* v___x_1701_; 
v___x_1699_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___closed__0);
v___x_146520__overap_1700_ = lean_panic_fn_borrowed(v___x_1699_, v_msg_1688_);
lean_inc(v___y_1697_);
lean_inc_ref(v___y_1696_);
lean_inc(v___y_1695_);
lean_inc_ref(v___y_1694_);
lean_inc(v___y_1693_);
lean_inc_ref(v___y_1692_);
lean_inc(v___y_1691_);
lean_inc_ref(v___y_1690_);
lean_inc(v___y_1689_);
v___x_1701_ = lean_apply_10(v___x_146520__overap_1700_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, lean_box(0));
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1___boxed(lean_object* v_msg_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v_res_1713_; 
v_res_1713_ = l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(v_msg_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
return v_res_1713_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; 
v___x_1714_ = lean_unsigned_to_nat(32u);
v___x_1715_ = lean_mk_empty_array_with_capacity(v___x_1714_);
v___x_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1716_, 0, v___x_1715_);
return v___x_1716_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1717_ = ((size_t)5ULL);
v___x_1718_ = lean_unsigned_to_nat(0u);
v___x_1719_ = lean_unsigned_to_nat(32u);
v___x_1720_ = lean_mk_empty_array_with_capacity(v___x_1719_);
v___x_1721_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__0);
v___x_1722_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1722_, 0, v___x_1721_);
lean_ctor_set(v___x_1722_, 1, v___x_1720_);
lean_ctor_set(v___x_1722_, 2, v___x_1718_);
lean_ctor_set(v___x_1722_, 3, v___x_1718_);
lean_ctor_set_usize(v___x_1722_, 4, v___x_1717_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg(lean_object* v___y_1723_){
_start:
{
lean_object* v___x_1725_; lean_object* v_traceState_1726_; lean_object* v_traces_1727_; lean_object* v___x_1728_; lean_object* v_traceState_1729_; lean_object* v_env_1730_; lean_object* v_nextMacroScope_1731_; lean_object* v_ngen_1732_; lean_object* v_auxDeclNGen_1733_; lean_object* v_cache_1734_; lean_object* v_messages_1735_; lean_object* v_infoState_1736_; lean_object* v_snapshotTasks_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1756_; 
v___x_1725_ = lean_st_ref_get(v___y_1723_);
v_traceState_1726_ = lean_ctor_get(v___x_1725_, 4);
lean_inc_ref(v_traceState_1726_);
lean_dec(v___x_1725_);
v_traces_1727_ = lean_ctor_get(v_traceState_1726_, 0);
lean_inc_ref(v_traces_1727_);
lean_dec_ref(v_traceState_1726_);
v___x_1728_ = lean_st_ref_take(v___y_1723_);
v_traceState_1729_ = lean_ctor_get(v___x_1728_, 4);
v_env_1730_ = lean_ctor_get(v___x_1728_, 0);
v_nextMacroScope_1731_ = lean_ctor_get(v___x_1728_, 1);
v_ngen_1732_ = lean_ctor_get(v___x_1728_, 2);
v_auxDeclNGen_1733_ = lean_ctor_get(v___x_1728_, 3);
v_cache_1734_ = lean_ctor_get(v___x_1728_, 5);
v_messages_1735_ = lean_ctor_get(v___x_1728_, 6);
v_infoState_1736_ = lean_ctor_get(v___x_1728_, 7);
v_snapshotTasks_1737_ = lean_ctor_get(v___x_1728_, 8);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1739_ = v___x_1728_;
v_isShared_1740_ = v_isSharedCheck_1756_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_snapshotTasks_1737_);
lean_inc(v_infoState_1736_);
lean_inc(v_messages_1735_);
lean_inc(v_cache_1734_);
lean_inc(v_traceState_1729_);
lean_inc(v_auxDeclNGen_1733_);
lean_inc(v_ngen_1732_);
lean_inc(v_nextMacroScope_1731_);
lean_inc(v_env_1730_);
lean_dec(v___x_1728_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1756_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
uint64_t v_tid_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1754_; 
v_tid_1741_ = lean_ctor_get_uint64(v_traceState_1729_, sizeof(void*)*1);
v_isSharedCheck_1754_ = !lean_is_exclusive(v_traceState_1729_);
if (v_isSharedCheck_1754_ == 0)
{
lean_object* v_unused_1755_; 
v_unused_1755_ = lean_ctor_get(v_traceState_1729_, 0);
lean_dec(v_unused_1755_);
v___x_1743_ = v_traceState_1729_;
v_isShared_1744_ = v_isSharedCheck_1754_;
goto v_resetjp_1742_;
}
else
{
lean_dec(v_traceState_1729_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1754_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1745_; lean_object* v___x_1747_; 
v___x_1745_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1);
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1745_);
v___x_1747_ = v___x_1743_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1745_);
lean_ctor_set_uint64(v_reuseFailAlloc_1753_, sizeof(void*)*1, v_tid_1741_);
v___x_1747_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
lean_object* v___x_1749_; 
if (v_isShared_1740_ == 0)
{
lean_ctor_set(v___x_1739_, 4, v___x_1747_);
v___x_1749_ = v___x_1739_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_env_1730_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_nextMacroScope_1731_);
lean_ctor_set(v_reuseFailAlloc_1752_, 2, v_ngen_1732_);
lean_ctor_set(v_reuseFailAlloc_1752_, 3, v_auxDeclNGen_1733_);
lean_ctor_set(v_reuseFailAlloc_1752_, 4, v___x_1747_);
lean_ctor_set(v_reuseFailAlloc_1752_, 5, v_cache_1734_);
lean_ctor_set(v_reuseFailAlloc_1752_, 6, v_messages_1735_);
lean_ctor_set(v_reuseFailAlloc_1752_, 7, v_infoState_1736_);
lean_ctor_set(v_reuseFailAlloc_1752_, 8, v_snapshotTasks_1737_);
v___x_1749_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; 
v___x_1750_ = lean_st_ref_set(v___y_1723_, v___x_1749_);
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v_traces_1727_);
return v___x_1751_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___boxed(lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg(v___y_1757_);
lean_dec(v___y_1757_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
lean_object* v___x_1770_; 
v___x_1770_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg(v___y_1768_);
return v___x_1770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___boxed(lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2(v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_, v___y_1779_);
lean_dec(v___y_1779_);
lean_dec_ref(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec_ref(v___y_1776_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec(v___y_1771_);
return v_res_1781_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(lean_object* v_opts_1782_, lean_object* v_opt_1783_){
_start:
{
lean_object* v_name_1784_; lean_object* v_defValue_1785_; lean_object* v_map_1786_; lean_object* v___x_1787_; 
v_name_1784_ = lean_ctor_get(v_opt_1783_, 0);
v_defValue_1785_ = lean_ctor_get(v_opt_1783_, 1);
v_map_1786_ = lean_ctor_get(v_opts_1782_, 0);
v___x_1787_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1786_, v_name_1784_);
if (lean_obj_tag(v___x_1787_) == 0)
{
uint8_t v___x_1788_; 
v___x_1788_ = lean_unbox(v_defValue_1785_);
return v___x_1788_;
}
else
{
lean_object* v_val_1789_; 
v_val_1789_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_val_1789_);
lean_dec_ref_known(v___x_1787_, 1);
if (lean_obj_tag(v_val_1789_) == 1)
{
uint8_t v_v_1790_; 
v_v_1790_ = lean_ctor_get_uint8(v_val_1789_, 0);
lean_dec_ref_known(v_val_1789_, 0);
return v_v_1790_;
}
else
{
uint8_t v___x_1791_; 
lean_dec(v_val_1789_);
v___x_1791_ = lean_unbox(v_defValue_1785_);
return v___x_1791_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3___boxed(lean_object* v_opts_1792_, lean_object* v_opt_1793_){
_start:
{
uint8_t v_res_1794_; lean_object* v_r_1795_; 
v_res_1794_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_1792_, v_opt_1793_);
lean_dec_ref(v_opt_1793_);
lean_dec_ref(v_opts_1792_);
v_r_1795_ = lean_box(v_res_1794_);
return v_r_1795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0(uint8_t v___x_1796_, lean_object* v_e_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
lean_object* v___x_1803_; uint8_t v_foApprox_1804_; uint8_t v_ctxApprox_1805_; uint8_t v_quasiPatternApprox_1806_; uint8_t v_constApprox_1807_; uint8_t v_isDefEqStuckEx_1808_; uint8_t v_unificationHints_1809_; uint8_t v_proofIrrelevance_1810_; uint8_t v_assignSyntheticOpaque_1811_; uint8_t v_offsetCnstrs_1812_; uint8_t v_etaStruct_1813_; uint8_t v_univApprox_1814_; uint8_t v_iota_1815_; uint8_t v_beta_1816_; uint8_t v_proj_1817_; uint8_t v_zeta_1818_; uint8_t v_zetaDelta_1819_; uint8_t v_zetaUnused_1820_; uint8_t v_zetaHave_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1860_; 
v___x_1803_ = l_Lean_Meta_Context_config(v___y_1798_);
v_foApprox_1804_ = lean_ctor_get_uint8(v___x_1803_, 0);
v_ctxApprox_1805_ = lean_ctor_get_uint8(v___x_1803_, 1);
v_quasiPatternApprox_1806_ = lean_ctor_get_uint8(v___x_1803_, 2);
v_constApprox_1807_ = lean_ctor_get_uint8(v___x_1803_, 3);
v_isDefEqStuckEx_1808_ = lean_ctor_get_uint8(v___x_1803_, 4);
v_unificationHints_1809_ = lean_ctor_get_uint8(v___x_1803_, 5);
v_proofIrrelevance_1810_ = lean_ctor_get_uint8(v___x_1803_, 6);
v_assignSyntheticOpaque_1811_ = lean_ctor_get_uint8(v___x_1803_, 7);
v_offsetCnstrs_1812_ = lean_ctor_get_uint8(v___x_1803_, 8);
v_etaStruct_1813_ = lean_ctor_get_uint8(v___x_1803_, 10);
v_univApprox_1814_ = lean_ctor_get_uint8(v___x_1803_, 11);
v_iota_1815_ = lean_ctor_get_uint8(v___x_1803_, 12);
v_beta_1816_ = lean_ctor_get_uint8(v___x_1803_, 13);
v_proj_1817_ = lean_ctor_get_uint8(v___x_1803_, 14);
v_zeta_1818_ = lean_ctor_get_uint8(v___x_1803_, 15);
v_zetaDelta_1819_ = lean_ctor_get_uint8(v___x_1803_, 16);
v_zetaUnused_1820_ = lean_ctor_get_uint8(v___x_1803_, 17);
v_zetaHave_1821_ = lean_ctor_get_uint8(v___x_1803_, 18);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1823_ = v___x_1803_;
v_isShared_1824_ = v_isSharedCheck_1860_;
goto v_resetjp_1822_;
}
else
{
lean_dec(v___x_1803_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1860_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
uint8_t v_trackZetaDelta_1825_; lean_object* v_zetaDeltaSet_1826_; lean_object* v_lctx_1827_; lean_object* v_localInstances_1828_; lean_object* v_defEqCtx_x3f_1829_; lean_object* v_synthPendingDepth_1830_; lean_object* v_canUnfold_x3f_1831_; uint8_t v_univApprox_1832_; uint8_t v_inTypeClassResolution_1833_; uint8_t v_cacheInferType_1834_; lean_object* v_config_1836_; 
v_trackZetaDelta_1825_ = lean_ctor_get_uint8(v___y_1798_, sizeof(void*)*7);
v_zetaDeltaSet_1826_ = lean_ctor_get(v___y_1798_, 1);
lean_inc(v_zetaDeltaSet_1826_);
v_lctx_1827_ = lean_ctor_get(v___y_1798_, 2);
lean_inc_ref(v_lctx_1827_);
v_localInstances_1828_ = lean_ctor_get(v___y_1798_, 3);
lean_inc_ref(v_localInstances_1828_);
v_defEqCtx_x3f_1829_ = lean_ctor_get(v___y_1798_, 4);
lean_inc(v_defEqCtx_x3f_1829_);
v_synthPendingDepth_1830_ = lean_ctor_get(v___y_1798_, 5);
lean_inc(v_synthPendingDepth_1830_);
v_canUnfold_x3f_1831_ = lean_ctor_get(v___y_1798_, 6);
lean_inc(v_canUnfold_x3f_1831_);
v_univApprox_1832_ = lean_ctor_get_uint8(v___y_1798_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1833_ = lean_ctor_get_uint8(v___y_1798_, sizeof(void*)*7 + 2);
v_cacheInferType_1834_ = lean_ctor_get_uint8(v___y_1798_, sizeof(void*)*7 + 3);
if (v_isShared_1824_ == 0)
{
v_config_1836_ = v___x_1823_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, 0, v_foApprox_1804_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, 1, v_ctxApprox_1805_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, 2, v_quasiPatternApprox_1806_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, 3, v_constApprox_1807_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, 4, v_isDefEqStuckEx_1808_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, 5, v_unificationHints_1809_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, 6, v_proofIrrelevance_1810_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, 7, v_assignSyntheticOpaque_1811_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, 8, v_offsetCnstrs_1812_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, 10, v_etaStruct_1813_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, 11, v_univApprox_1814_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, 12, v_iota_1815_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, 13, v_beta_1816_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, 14, v_proj_1817_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, 15, v_zeta_1818_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, 16, v_zetaDelta_1819_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, 17, v_zetaUnused_1820_);
lean_ctor_set_uint8(v_reuseFailAlloc_1859_, 18, v_zetaHave_1821_);
v_config_1836_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
uint64_t v___x_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1851_; 
lean_ctor_set_uint8(v_config_1836_, 9, v___x_1796_);
v___x_1837_ = l_Lean_Meta_Context_configKey(v___y_1798_);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___y_1798_);
if (v_isSharedCheck_1851_ == 0)
{
lean_object* v_unused_1852_; lean_object* v_unused_1853_; lean_object* v_unused_1854_; lean_object* v_unused_1855_; lean_object* v_unused_1856_; lean_object* v_unused_1857_; lean_object* v_unused_1858_; 
v_unused_1852_ = lean_ctor_get(v___y_1798_, 6);
lean_dec(v_unused_1852_);
v_unused_1853_ = lean_ctor_get(v___y_1798_, 5);
lean_dec(v_unused_1853_);
v_unused_1854_ = lean_ctor_get(v___y_1798_, 4);
lean_dec(v_unused_1854_);
v_unused_1855_ = lean_ctor_get(v___y_1798_, 3);
lean_dec(v_unused_1855_);
v_unused_1856_ = lean_ctor_get(v___y_1798_, 2);
lean_dec(v_unused_1856_);
v_unused_1857_ = lean_ctor_get(v___y_1798_, 1);
lean_dec(v_unused_1857_);
v_unused_1858_ = lean_ctor_get(v___y_1798_, 0);
lean_dec(v_unused_1858_);
v___x_1839_ = v___y_1798_;
v_isShared_1840_ = v_isSharedCheck_1851_;
goto v_resetjp_1838_;
}
else
{
lean_dec(v___y_1798_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1851_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
uint64_t v___x_1841_; uint64_t v___x_1842_; uint64_t v___x_1843_; uint64_t v___x_1844_; uint64_t v_key_1845_; lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1841_ = 3ULL;
v___x_1842_ = lean_uint64_shift_right(v___x_1837_, v___x_1841_);
v___x_1843_ = lean_uint64_shift_left(v___x_1842_, v___x_1841_);
v___x_1844_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1796_);
v_key_1845_ = lean_uint64_lor(v___x_1843_, v___x_1844_);
v___x_1846_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1846_, 0, v_config_1836_);
lean_ctor_set_uint64(v___x_1846_, sizeof(void*)*1, v_key_1845_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1846_);
v___x_1848_ = v___x_1839_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1846_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_zetaDeltaSet_1826_);
lean_ctor_set(v_reuseFailAlloc_1850_, 2, v_lctx_1827_);
lean_ctor_set(v_reuseFailAlloc_1850_, 3, v_localInstances_1828_);
lean_ctor_set(v_reuseFailAlloc_1850_, 4, v_defEqCtx_x3f_1829_);
lean_ctor_set(v_reuseFailAlloc_1850_, 5, v_synthPendingDepth_1830_);
lean_ctor_set(v_reuseFailAlloc_1850_, 6, v_canUnfold_x3f_1831_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, sizeof(void*)*7, v_trackZetaDelta_1825_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, sizeof(void*)*7 + 1, v_univApprox_1832_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1833_);
lean_ctor_set_uint8(v_reuseFailAlloc_1850_, sizeof(void*)*7 + 3, v_cacheInferType_1834_);
v___x_1848_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1849_; 
v___x_1849_ = l_Lean_Meta_reduceProj_x3f(v_e_1797_, v___x_1848_, v___y_1799_, v___y_1800_, v___y_1801_);
lean_dec_ref(v___x_1848_);
return v___x_1849_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed(lean_object* v___x_1861_, lean_object* v_e_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
uint8_t v___x_163278__boxed_1868_; lean_object* v_res_1869_; 
v___x_163278__boxed_1868_ = lean_unbox(v___x_1861_);
v_res_1869_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0(v___x_163278__boxed_1868_, v_e_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
return v_res_1869_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1(void){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1871_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__0));
v___x_1872_ = l_Lean_stringToMessageData(v___x_1871_);
return v___x_1872_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__2));
v___x_1875_ = l_Lean_stringToMessageData(v___x_1874_);
return v___x_1875_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__5(void){
_start:
{
lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1877_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__4));
v___x_1878_ = l_Lean_stringToMessageData(v___x_1877_);
return v___x_1878_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__7(void){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__6));
v___x_1881_ = l_Lean_stringToMessageData(v___x_1880_);
return v___x_1881_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__9(void){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__8));
v___x_1884_ = l_Lean_stringToMessageData(v___x_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2(lean_object* v_typeName_1885_, lean_object* v_idx_1886_, lean_object* v_e_1887_, lean_object* v_x_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
if (lean_obj_tag(v_x_1888_) == 0)
{
lean_object* v_a_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1919_; 
lean_dec_ref(v_e_1887_);
v_a_1899_ = lean_ctor_get(v_x_1888_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v_x_1888_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1901_ = v_x_1888_;
v_isShared_1902_ = v_isSharedCheck_1919_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_a_1899_);
lean_dec(v_x_1888_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1919_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1910_; 
v___x_1903_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1);
v___x_1904_ = l_Lean_MessageData_ofName(v_typeName_1885_);
v___x_1905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
v___x_1906_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___x_1905_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = l_Nat_reprFast(v_idx_1886_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set_tag(v___x_1901_, 3);
lean_ctor_set(v___x_1901_, 0, v___x_1908_);
v___x_1910_ = v___x_1901_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1911_ = l_Lean_MessageData_ofFormat(v___x_1910_);
v___x_1912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1907_);
lean_ctor_set(v___x_1912_, 1, v___x_1911_);
v___x_1913_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__3);
v___x_1914_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1912_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = l_Lean_Exception_toMessageData(v_a_1899_);
v___x_1916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1914_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1916_);
return v___x_1917_;
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1976_; 
v_a_1920_ = lean_ctor_get(v_x_1888_, 0);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_x_1888_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1922_ = v_x_1888_;
v_isShared_1923_ = v_isSharedCheck_1976_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v_x_1888_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1976_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
if (lean_obj_tag(v_a_1920_) == 0)
{
uint8_t v_done_1924_; 
v_done_1924_ = lean_ctor_get_uint8(v_a_1920_, 0);
lean_dec_ref_known(v_a_1920_, 0);
if (v_done_1924_ == 1)
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1932_; 
v___x_1925_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1);
v___x_1926_ = l_Lean_MessageData_ofName(v_typeName_1885_);
v___x_1927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1925_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1927_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = l_Nat_reprFast(v_idx_1886_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set_tag(v___x_1922_, 3);
lean_ctor_set(v___x_1922_, 0, v___x_1930_);
v___x_1932_ = v___x_1922_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v___x_1930_);
v___x_1932_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1933_ = l_Lean_MessageData_ofFormat(v___x_1932_);
v___x_1934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1929_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__5, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__5_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__5);
v___x_1936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1934_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
v___x_1937_ = l_Lean_indentExpr(v_e_1887_);
v___x_1938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1936_);
lean_ctor_set(v___x_1938_, 1, v___x_1937_);
v___x_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
return v___x_1939_;
}
}
else
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1948_; 
lean_dec_ref(v_e_1887_);
v___x_1941_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1);
v___x_1942_ = l_Lean_MessageData_ofName(v_typeName_1885_);
v___x_1943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1941_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
v___x_1944_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1943_);
lean_ctor_set(v___x_1945_, 1, v___x_1944_);
v___x_1946_ = l_Nat_reprFast(v_idx_1886_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set_tag(v___x_1922_, 3);
lean_ctor_set(v___x_1922_, 0, v___x_1946_);
v___x_1948_ = v___x_1922_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1946_);
v___x_1948_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1949_ = l_Lean_MessageData_ofFormat(v___x_1948_);
v___x_1950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1945_);
lean_ctor_set(v___x_1950_, 1, v___x_1949_);
v___x_1951_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__7, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__7_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__7);
v___x_1952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1950_);
lean_ctor_set(v___x_1952_, 1, v___x_1951_);
v___x_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
return v___x_1953_;
}
}
}
else
{
lean_object* v_e_x27_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1963_; 
v_e_x27_1955_ = lean_ctor_get(v_a_1920_, 0);
lean_inc_ref(v_e_x27_1955_);
lean_dec_ref_known(v_a_1920_, 2);
v___x_1956_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__1);
v___x_1957_ = l_Lean_MessageData_ofName(v_typeName_1885_);
v___x_1958_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1958_, 0, v___x_1956_);
lean_ctor_set(v___x_1958_, 1, v___x_1957_);
v___x_1959_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
v___x_1960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1958_);
lean_ctor_set(v___x_1960_, 1, v___x_1959_);
v___x_1961_ = l_Nat_reprFast(v_idx_1886_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set_tag(v___x_1922_, 3);
lean_ctor_set(v___x_1922_, 0, v___x_1961_);
v___x_1963_ = v___x_1922_;
goto v_reusejp_1962_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v___x_1961_);
v___x_1963_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1962_;
}
v_reusejp_1962_:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1964_ = l_Lean_MessageData_ofFormat(v___x_1963_);
v___x_1965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1965_, 0, v___x_1960_);
lean_ctor_set(v___x_1965_, 1, v___x_1964_);
v___x_1966_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___closed__9);
v___x_1967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1967_, 0, v___x_1965_);
lean_ctor_set(v___x_1967_, 1, v___x_1966_);
v___x_1968_ = l_Lean_indentExpr(v_e_1887_);
v___x_1969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1967_);
lean_ctor_set(v___x_1969_, 1, v___x_1968_);
v___x_1970_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_1971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1969_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___x_1972_ = l_Lean_indentExpr(v_e_x27_1955_);
v___x_1973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1971_);
lean_ctor_set(v___x_1973_, 1, v___x_1972_);
v___x_1974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
return v___x_1974_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___boxed(lean_object* v_typeName_1977_, lean_object* v_idx_1978_, lean_object* v_e_1979_, lean_object* v_x_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2(v_typeName_1977_, v_idx_1978_, v_e_1979_, v_x_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_);
lean_dec(v___y_1989_);
lean_dec_ref(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(lean_object* v_x_1992_){
_start:
{
if (lean_obj_tag(v_x_1992_) == 0)
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
v_a_1994_ = lean_ctor_get(v_x_1992_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v_x_1992_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v_x_1992_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v_x_1992_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
lean_ctor_set_tag(v___x_1996_, 1);
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
else
{
lean_object* v_a_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2009_; 
v_a_2002_ = lean_ctor_get(v_x_1992_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v_x_1992_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2004_ = v_x_1992_;
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_a_2002_);
lean_dec(v_x_1992_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2009_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2007_; 
if (v_isShared_2005_ == 0)
{
lean_ctor_set_tag(v___x_2004_, 0);
v___x_2007_ = v___x_2004_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_a_2002_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg___boxed(lean_object* v_x_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(v_x_2010_);
return v_res_2012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5(size_t v_sz_2013_, size_t v_i_2014_, lean_object* v_bs_2015_){
_start:
{
uint8_t v___x_2016_; 
v___x_2016_ = lean_usize_dec_lt(v_i_2014_, v_sz_2013_);
if (v___x_2016_ == 0)
{
return v_bs_2015_;
}
else
{
lean_object* v_v_2017_; lean_object* v_msg_2018_; lean_object* v___x_2019_; lean_object* v_bs_x27_2020_; size_t v___x_2021_; size_t v___x_2022_; lean_object* v___x_2023_; 
v_v_2017_ = lean_array_uget_borrowed(v_bs_2015_, v_i_2014_);
v_msg_2018_ = lean_ctor_get(v_v_2017_, 1);
lean_inc_ref(v_msg_2018_);
v___x_2019_ = lean_unsigned_to_nat(0u);
v_bs_x27_2020_ = lean_array_uset(v_bs_2015_, v_i_2014_, v___x_2019_);
v___x_2021_ = ((size_t)1ULL);
v___x_2022_ = lean_usize_add(v_i_2014_, v___x_2021_);
v___x_2023_ = lean_array_uset(v_bs_x27_2020_, v_i_2014_, v_msg_2018_);
v_i_2014_ = v___x_2022_;
v_bs_2015_ = v___x_2023_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5___boxed(lean_object* v_sz_2025_, lean_object* v_i_2026_, lean_object* v_bs_2027_){
_start:
{
size_t v_sz_boxed_2028_; size_t v_i_boxed_2029_; lean_object* v_res_2030_; 
v_sz_boxed_2028_ = lean_unbox_usize(v_sz_2025_);
lean_dec(v_sz_2025_);
v_i_boxed_2029_ = lean_unbox_usize(v_i_2026_);
lean_dec(v_i_2026_);
v_res_2030_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5(v_sz_boxed_2028_, v_i_boxed_2029_, v_bs_2027_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___redArg(lean_object* v_oldTraces_2031_, lean_object* v_data_2032_, lean_object* v_ref_2033_, lean_object* v_msg_2034_, lean_object* v___y_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_){
_start:
{
lean_object* v_fileName_2040_; lean_object* v_fileMap_2041_; lean_object* v_options_2042_; lean_object* v_currRecDepth_2043_; lean_object* v_maxRecDepth_2044_; lean_object* v_ref_2045_; lean_object* v_currNamespace_2046_; lean_object* v_openDecls_2047_; lean_object* v_initHeartbeats_2048_; lean_object* v_maxHeartbeats_2049_; lean_object* v_quotContext_2050_; lean_object* v_currMacroScope_2051_; uint8_t v_diag_2052_; lean_object* v_cancelTk_x3f_2053_; uint8_t v_suppressElabErrors_2054_; lean_object* v_inheritedTraceOptions_2055_; lean_object* v___x_2056_; lean_object* v_traceState_2057_; lean_object* v_traces_2058_; lean_object* v_ref_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; size_t v_sz_2062_; size_t v___x_2063_; lean_object* v___x_2064_; lean_object* v_msg_2065_; lean_object* v___x_2066_; lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2104_; 
v_fileName_2040_ = lean_ctor_get(v___y_2037_, 0);
v_fileMap_2041_ = lean_ctor_get(v___y_2037_, 1);
v_options_2042_ = lean_ctor_get(v___y_2037_, 2);
v_currRecDepth_2043_ = lean_ctor_get(v___y_2037_, 3);
v_maxRecDepth_2044_ = lean_ctor_get(v___y_2037_, 4);
v_ref_2045_ = lean_ctor_get(v___y_2037_, 5);
v_currNamespace_2046_ = lean_ctor_get(v___y_2037_, 6);
v_openDecls_2047_ = lean_ctor_get(v___y_2037_, 7);
v_initHeartbeats_2048_ = lean_ctor_get(v___y_2037_, 8);
v_maxHeartbeats_2049_ = lean_ctor_get(v___y_2037_, 9);
v_quotContext_2050_ = lean_ctor_get(v___y_2037_, 10);
v_currMacroScope_2051_ = lean_ctor_get(v___y_2037_, 11);
v_diag_2052_ = lean_ctor_get_uint8(v___y_2037_, sizeof(void*)*14);
v_cancelTk_x3f_2053_ = lean_ctor_get(v___y_2037_, 12);
v_suppressElabErrors_2054_ = lean_ctor_get_uint8(v___y_2037_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2055_ = lean_ctor_get(v___y_2037_, 13);
v___x_2056_ = lean_st_ref_get(v___y_2038_);
v_traceState_2057_ = lean_ctor_get(v___x_2056_, 4);
lean_inc_ref(v_traceState_2057_);
lean_dec(v___x_2056_);
v_traces_2058_ = lean_ctor_get(v_traceState_2057_, 0);
lean_inc_ref(v_traces_2058_);
lean_dec_ref(v_traceState_2057_);
v_ref_2059_ = l_Lean_replaceRef(v_ref_2033_, v_ref_2045_);
lean_inc_ref(v_inheritedTraceOptions_2055_);
lean_inc(v_cancelTk_x3f_2053_);
lean_inc(v_currMacroScope_2051_);
lean_inc(v_quotContext_2050_);
lean_inc(v_maxHeartbeats_2049_);
lean_inc(v_initHeartbeats_2048_);
lean_inc(v_openDecls_2047_);
lean_inc(v_currNamespace_2046_);
lean_inc(v_maxRecDepth_2044_);
lean_inc(v_currRecDepth_2043_);
lean_inc_ref(v_options_2042_);
lean_inc_ref(v_fileMap_2041_);
lean_inc_ref(v_fileName_2040_);
v___x_2060_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2060_, 0, v_fileName_2040_);
lean_ctor_set(v___x_2060_, 1, v_fileMap_2041_);
lean_ctor_set(v___x_2060_, 2, v_options_2042_);
lean_ctor_set(v___x_2060_, 3, v_currRecDepth_2043_);
lean_ctor_set(v___x_2060_, 4, v_maxRecDepth_2044_);
lean_ctor_set(v___x_2060_, 5, v_ref_2059_);
lean_ctor_set(v___x_2060_, 6, v_currNamespace_2046_);
lean_ctor_set(v___x_2060_, 7, v_openDecls_2047_);
lean_ctor_set(v___x_2060_, 8, v_initHeartbeats_2048_);
lean_ctor_set(v___x_2060_, 9, v_maxHeartbeats_2049_);
lean_ctor_set(v___x_2060_, 10, v_quotContext_2050_);
lean_ctor_set(v___x_2060_, 11, v_currMacroScope_2051_);
lean_ctor_set(v___x_2060_, 12, v_cancelTk_x3f_2053_);
lean_ctor_set(v___x_2060_, 13, v_inheritedTraceOptions_2055_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*14, v_diag_2052_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*14 + 1, v_suppressElabErrors_2054_);
v___x_2061_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2058_);
lean_dec_ref(v_traces_2058_);
v_sz_2062_ = lean_array_size(v___x_2061_);
v___x_2063_ = ((size_t)0ULL);
v___x_2064_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5(v_sz_2062_, v___x_2063_, v___x_2061_);
v_msg_2065_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2065_, 0, v_data_2032_);
lean_ctor_set(v_msg_2065_, 1, v_msg_2034_);
lean_ctor_set(v_msg_2065_, 2, v___x_2064_);
v___x_2066_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_2065_, v___y_2035_, v___y_2036_, v___x_2060_, v___y_2038_);
lean_dec_ref_known(v___x_2060_, 14);
v_a_2067_ = lean_ctor_get(v___x_2066_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2069_ = v___x_2066_;
v_isShared_2070_ = v_isSharedCheck_2104_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2066_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2104_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; lean_object* v_traceState_2072_; lean_object* v_env_2073_; lean_object* v_nextMacroScope_2074_; lean_object* v_ngen_2075_; lean_object* v_auxDeclNGen_2076_; lean_object* v_cache_2077_; lean_object* v_messages_2078_; lean_object* v_infoState_2079_; lean_object* v_snapshotTasks_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2103_; 
v___x_2071_ = lean_st_ref_take(v___y_2038_);
v_traceState_2072_ = lean_ctor_get(v___x_2071_, 4);
v_env_2073_ = lean_ctor_get(v___x_2071_, 0);
v_nextMacroScope_2074_ = lean_ctor_get(v___x_2071_, 1);
v_ngen_2075_ = lean_ctor_get(v___x_2071_, 2);
v_auxDeclNGen_2076_ = lean_ctor_get(v___x_2071_, 3);
v_cache_2077_ = lean_ctor_get(v___x_2071_, 5);
v_messages_2078_ = lean_ctor_get(v___x_2071_, 6);
v_infoState_2079_ = lean_ctor_get(v___x_2071_, 7);
v_snapshotTasks_2080_ = lean_ctor_get(v___x_2071_, 8);
v_isSharedCheck_2103_ = !lean_is_exclusive(v___x_2071_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2082_ = v___x_2071_;
v_isShared_2083_ = v_isSharedCheck_2103_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_snapshotTasks_2080_);
lean_inc(v_infoState_2079_);
lean_inc(v_messages_2078_);
lean_inc(v_cache_2077_);
lean_inc(v_traceState_2072_);
lean_inc(v_auxDeclNGen_2076_);
lean_inc(v_ngen_2075_);
lean_inc(v_nextMacroScope_2074_);
lean_inc(v_env_2073_);
lean_dec(v___x_2071_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2103_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
uint64_t v_tid_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2101_; 
v_tid_2084_ = lean_ctor_get_uint64(v_traceState_2072_, sizeof(void*)*1);
v_isSharedCheck_2101_ = !lean_is_exclusive(v_traceState_2072_);
if (v_isSharedCheck_2101_ == 0)
{
lean_object* v_unused_2102_; 
v_unused_2102_ = lean_ctor_get(v_traceState_2072_, 0);
lean_dec(v_unused_2102_);
v___x_2086_ = v_traceState_2072_;
v_isShared_2087_ = v_isSharedCheck_2101_;
goto v_resetjp_2085_;
}
else
{
lean_dec(v_traceState_2072_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2101_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2091_; 
v___x_2088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2088_, 0, v_ref_2033_);
lean_ctor_set(v___x_2088_, 1, v_a_2067_);
v___x_2089_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2031_, v___x_2088_);
if (v_isShared_2087_ == 0)
{
lean_ctor_set(v___x_2086_, 0, v___x_2089_);
v___x_2091_ = v___x_2086_;
goto v_reusejp_2090_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2089_);
lean_ctor_set_uint64(v_reuseFailAlloc_2100_, sizeof(void*)*1, v_tid_2084_);
v___x_2091_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2090_;
}
v_reusejp_2090_:
{
lean_object* v___x_2093_; 
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 4, v___x_2091_);
v___x_2093_ = v___x_2082_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_env_2073_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v_nextMacroScope_2074_);
lean_ctor_set(v_reuseFailAlloc_2099_, 2, v_ngen_2075_);
lean_ctor_set(v_reuseFailAlloc_2099_, 3, v_auxDeclNGen_2076_);
lean_ctor_set(v_reuseFailAlloc_2099_, 4, v___x_2091_);
lean_ctor_set(v_reuseFailAlloc_2099_, 5, v_cache_2077_);
lean_ctor_set(v_reuseFailAlloc_2099_, 6, v_messages_2078_);
lean_ctor_set(v_reuseFailAlloc_2099_, 7, v_infoState_2079_);
lean_ctor_set(v_reuseFailAlloc_2099_, 8, v_snapshotTasks_2080_);
v___x_2093_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2097_; 
v___x_2094_ = lean_st_ref_set(v___y_2038_, v___x_2093_);
v___x_2095_ = lean_box(0);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2095_);
v___x_2097_ = v___x_2069_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___redArg___boxed(lean_object* v_oldTraces_2105_, lean_object* v_data_2106_, lean_object* v_ref_2107_, lean_object* v_msg_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___redArg(v_oldTraces_2105_, v_data_2106_, v_ref_2107_, v_msg_2108_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
lean_dec(v___y_2112_);
lean_dec_ref(v___y_2111_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
return v_res_2114_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(lean_object* v_e_2115_){
_start:
{
if (lean_obj_tag(v_e_2115_) == 0)
{
uint8_t v___x_2116_; 
v___x_2116_ = 2;
return v___x_2116_;
}
else
{
uint8_t v___x_2117_; 
v___x_2117_ = 0;
return v___x_2117_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6___boxed(lean_object* v_e_2118_){
_start:
{
uint8_t v_res_2119_; lean_object* v_r_2120_; 
v_res_2119_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(v_e_2118_);
lean_dec_ref(v_e_2118_);
v_r_2120_ = lean_box(v_res_2119_);
return v_r_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(lean_object* v_opts_2121_, lean_object* v_opt_2122_){
_start:
{
lean_object* v_name_2123_; lean_object* v_defValue_2124_; lean_object* v_map_2125_; lean_object* v___x_2126_; 
v_name_2123_ = lean_ctor_get(v_opt_2122_, 0);
v_defValue_2124_ = lean_ctor_get(v_opt_2122_, 1);
v_map_2125_ = lean_ctor_get(v_opts_2121_, 0);
v___x_2126_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2125_, v_name_2123_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_inc(v_defValue_2124_);
return v_defValue_2124_;
}
else
{
lean_object* v_val_2127_; 
v_val_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_val_2127_);
lean_dec_ref_known(v___x_2126_, 1);
if (lean_obj_tag(v_val_2127_) == 3)
{
lean_object* v_v_2128_; 
v_v_2128_ = lean_ctor_get(v_val_2127_, 0);
lean_inc(v_v_2128_);
lean_dec_ref_known(v_val_2127_, 1);
return v_v_2128_;
}
else
{
lean_dec(v_val_2127_);
lean_inc(v_defValue_2124_);
return v_defValue_2124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7___boxed(lean_object* v_opts_2129_, lean_object* v_opt_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_2129_, v_opt_2130_);
lean_dec_ref(v_opt_2130_);
lean_dec_ref(v_opts_2129_);
return v_res_2131_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1(void){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2133_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__0));
v___x_2134_ = l_Lean_stringToMessageData(v___x_2133_);
return v___x_2134_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2(void){
_start:
{
lean_object* v___x_2135_; double v___x_2136_; 
v___x_2135_ = lean_unsigned_to_nat(1000u);
v___x_2136_ = lean_float_of_nat(v___x_2135_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4(lean_object* v_cls_2137_, uint8_t v_collapsed_2138_, lean_object* v_tag_2139_, lean_object* v_opts_2140_, uint8_t v_clsEnabled_2141_, lean_object* v_oldTraces_2142_, lean_object* v_msg_2143_, lean_object* v_resStartStop_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v_fst_2155_; lean_object* v_snd_2156_; lean_object* v___y_2158_; lean_object* v___y_2159_; lean_object* v_data_2160_; lean_object* v_fst_2171_; lean_object* v_snd_2172_; lean_object* v___x_2173_; uint8_t v___x_2174_; lean_object* v___y_2176_; lean_object* v_a_2177_; uint8_t v___y_2192_; double v___y_2223_; 
v_fst_2155_ = lean_ctor_get(v_resStartStop_2144_, 0);
lean_inc(v_fst_2155_);
v_snd_2156_ = lean_ctor_get(v_resStartStop_2144_, 1);
lean_inc(v_snd_2156_);
lean_dec_ref(v_resStartStop_2144_);
v_fst_2171_ = lean_ctor_get(v_snd_2156_, 0);
lean_inc(v_fst_2171_);
v_snd_2172_ = lean_ctor_get(v_snd_2156_, 1);
lean_inc(v_snd_2172_);
lean_dec(v_snd_2156_);
v___x_2173_ = l_Lean_trace_profiler;
v___x_2174_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_2140_, v___x_2173_);
if (v___x_2174_ == 0)
{
v___y_2192_ = v___x_2174_;
goto v___jp_2191_;
}
else
{
lean_object* v___x_2228_; uint8_t v___x_2229_; 
v___x_2228_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2229_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_2140_, v___x_2228_);
if (v___x_2229_ == 0)
{
lean_object* v___x_2230_; lean_object* v___x_2231_; double v___x_2232_; double v___x_2233_; double v___x_2234_; 
v___x_2230_ = l_Lean_trace_profiler_threshold;
v___x_2231_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_2140_, v___x_2230_);
v___x_2232_ = lean_float_of_nat(v___x_2231_);
v___x_2233_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2);
v___x_2234_ = lean_float_div(v___x_2232_, v___x_2233_);
v___y_2223_ = v___x_2234_;
goto v___jp_2222_;
}
else
{
lean_object* v___x_2235_; lean_object* v___x_2236_; double v___x_2237_; 
v___x_2235_ = l_Lean_trace_profiler_threshold;
v___x_2236_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_2140_, v___x_2235_);
v___x_2237_ = lean_float_of_nat(v___x_2236_);
v___y_2223_ = v___x_2237_;
goto v___jp_2222_;
}
}
v___jp_2157_:
{
lean_object* v___x_2161_; 
lean_inc(v___y_2158_);
v___x_2161_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___redArg(v_oldTraces_2142_, v_data_2160_, v___y_2158_, v___y_2159_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
if (lean_obj_tag(v___x_2161_) == 0)
{
lean_object* v___x_2162_; 
lean_dec_ref_known(v___x_2161_, 1);
v___x_2162_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(v_fst_2155_);
return v___x_2162_;
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
lean_dec(v_fst_2155_);
v_a_2163_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___x_2161_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2161_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2163_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
v___jp_2175_:
{
uint8_t v_result_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; double v___x_2181_; lean_object* v_data_2182_; 
v_result_2178_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(v_fst_2155_);
v___x_2179_ = lean_box(v_result_2178_);
v___x_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2179_);
v___x_2181_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_2139_);
lean_inc_ref(v___x_2180_);
lean_inc(v_cls_2137_);
v_data_2182_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2182_, 0, v_cls_2137_);
lean_ctor_set(v_data_2182_, 1, v___x_2180_);
lean_ctor_set(v_data_2182_, 2, v_tag_2139_);
lean_ctor_set_float(v_data_2182_, sizeof(void*)*3, v___x_2181_);
lean_ctor_set_float(v_data_2182_, sizeof(void*)*3 + 8, v___x_2181_);
lean_ctor_set_uint8(v_data_2182_, sizeof(void*)*3 + 16, v_collapsed_2138_);
if (v___x_2174_ == 0)
{
lean_dec_ref_known(v___x_2180_, 1);
lean_dec(v_snd_2172_);
lean_dec(v_fst_2171_);
lean_dec_ref(v_tag_2139_);
lean_dec(v_cls_2137_);
v___y_2158_ = v___y_2176_;
v___y_2159_ = v_a_2177_;
v_data_2160_ = v_data_2182_;
goto v___jp_2157_;
}
else
{
lean_object* v_data_2183_; double v___x_2184_; double v___x_2185_; 
lean_dec_ref_known(v_data_2182_, 3);
v_data_2183_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2183_, 0, v_cls_2137_);
lean_ctor_set(v_data_2183_, 1, v___x_2180_);
lean_ctor_set(v_data_2183_, 2, v_tag_2139_);
v___x_2184_ = lean_unbox_float(v_fst_2171_);
lean_dec(v_fst_2171_);
lean_ctor_set_float(v_data_2183_, sizeof(void*)*3, v___x_2184_);
v___x_2185_ = lean_unbox_float(v_snd_2172_);
lean_dec(v_snd_2172_);
lean_ctor_set_float(v_data_2183_, sizeof(void*)*3 + 8, v___x_2185_);
lean_ctor_set_uint8(v_data_2183_, sizeof(void*)*3 + 16, v_collapsed_2138_);
v___y_2158_ = v___y_2176_;
v___y_2159_ = v_a_2177_;
v_data_2160_ = v_data_2183_;
goto v___jp_2157_;
}
}
v___jp_2186_:
{
lean_object* v_ref_2187_; lean_object* v___x_2188_; 
v_ref_2187_ = lean_ctor_get(v___y_2152_, 5);
lean_inc(v___y_2153_);
lean_inc_ref(v___y_2152_);
lean_inc(v___y_2151_);
lean_inc_ref(v___y_2150_);
lean_inc(v___y_2149_);
lean_inc_ref(v___y_2148_);
lean_inc(v___y_2147_);
lean_inc_ref(v___y_2146_);
lean_inc(v___y_2145_);
lean_inc(v_fst_2155_);
v___x_2188_ = lean_apply_11(v_msg_2143_, v_fst_2155_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, lean_box(0));
if (lean_obj_tag(v___x_2188_) == 0)
{
lean_object* v_a_2189_; 
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_a_2189_);
lean_dec_ref_known(v___x_2188_, 1);
v___y_2176_ = v_ref_2187_;
v_a_2177_ = v_a_2189_;
goto v___jp_2175_;
}
else
{
lean_object* v___x_2190_; 
lean_dec_ref_known(v___x_2188_, 1);
v___x_2190_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
v___y_2176_ = v_ref_2187_;
v_a_2177_ = v___x_2190_;
goto v___jp_2175_;
}
}
v___jp_2191_:
{
if (v_clsEnabled_2141_ == 0)
{
if (v___y_2192_ == 0)
{
lean_object* v___x_2193_; lean_object* v_traceState_2194_; lean_object* v_env_2195_; lean_object* v_nextMacroScope_2196_; lean_object* v_ngen_2197_; lean_object* v_auxDeclNGen_2198_; lean_object* v_cache_2199_; lean_object* v_messages_2200_; lean_object* v_infoState_2201_; lean_object* v_snapshotTasks_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2221_; 
lean_dec(v_snd_2172_);
lean_dec(v_fst_2171_);
lean_dec_ref(v_msg_2143_);
lean_dec_ref(v_tag_2139_);
lean_dec(v_cls_2137_);
v___x_2193_ = lean_st_ref_take(v___y_2153_);
v_traceState_2194_ = lean_ctor_get(v___x_2193_, 4);
v_env_2195_ = lean_ctor_get(v___x_2193_, 0);
v_nextMacroScope_2196_ = lean_ctor_get(v___x_2193_, 1);
v_ngen_2197_ = lean_ctor_get(v___x_2193_, 2);
v_auxDeclNGen_2198_ = lean_ctor_get(v___x_2193_, 3);
v_cache_2199_ = lean_ctor_get(v___x_2193_, 5);
v_messages_2200_ = lean_ctor_get(v___x_2193_, 6);
v_infoState_2201_ = lean_ctor_get(v___x_2193_, 7);
v_snapshotTasks_2202_ = lean_ctor_get(v___x_2193_, 8);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2204_ = v___x_2193_;
v_isShared_2205_ = v_isSharedCheck_2221_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_snapshotTasks_2202_);
lean_inc(v_infoState_2201_);
lean_inc(v_messages_2200_);
lean_inc(v_cache_2199_);
lean_inc(v_traceState_2194_);
lean_inc(v_auxDeclNGen_2198_);
lean_inc(v_ngen_2197_);
lean_inc(v_nextMacroScope_2196_);
lean_inc(v_env_2195_);
lean_dec(v___x_2193_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2221_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
uint64_t v_tid_2206_; lean_object* v_traces_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2220_; 
v_tid_2206_ = lean_ctor_get_uint64(v_traceState_2194_, sizeof(void*)*1);
v_traces_2207_ = lean_ctor_get(v_traceState_2194_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v_traceState_2194_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2209_ = v_traceState_2194_;
v_isShared_2210_ = v_isSharedCheck_2220_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_traces_2207_);
lean_dec(v_traceState_2194_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2220_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2211_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2142_, v_traces_2207_);
lean_dec_ref(v_traces_2207_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2211_);
v___x_2213_ = v___x_2209_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2211_);
lean_ctor_set_uint64(v_reuseFailAlloc_2219_, sizeof(void*)*1, v_tid_2206_);
v___x_2213_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
lean_object* v___x_2215_; 
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 4, v___x_2213_);
v___x_2215_ = v___x_2204_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_env_2195_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v_nextMacroScope_2196_);
lean_ctor_set(v_reuseFailAlloc_2218_, 2, v_ngen_2197_);
lean_ctor_set(v_reuseFailAlloc_2218_, 3, v_auxDeclNGen_2198_);
lean_ctor_set(v_reuseFailAlloc_2218_, 4, v___x_2213_);
lean_ctor_set(v_reuseFailAlloc_2218_, 5, v_cache_2199_);
lean_ctor_set(v_reuseFailAlloc_2218_, 6, v_messages_2200_);
lean_ctor_set(v_reuseFailAlloc_2218_, 7, v_infoState_2201_);
lean_ctor_set(v_reuseFailAlloc_2218_, 8, v_snapshotTasks_2202_);
v___x_2215_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2216_ = lean_st_ref_set(v___y_2153_, v___x_2215_);
v___x_2217_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(v_fst_2155_);
return v___x_2217_;
}
}
}
}
}
else
{
goto v___jp_2186_;
}
}
else
{
goto v___jp_2186_;
}
}
v___jp_2222_:
{
double v___x_2224_; double v___x_2225_; double v___x_2226_; uint8_t v___x_2227_; 
v___x_2224_ = lean_unbox_float(v_snd_2172_);
v___x_2225_ = lean_unbox_float(v_fst_2171_);
v___x_2226_ = lean_float_sub(v___x_2224_, v___x_2225_);
v___x_2227_ = lean_float_decLt(v___y_2223_, v___x_2226_);
v___y_2192_ = v___x_2227_;
goto v___jp_2191_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___boxed(lean_object** _args){
lean_object* v_cls_2238_ = _args[0];
lean_object* v_collapsed_2239_ = _args[1];
lean_object* v_tag_2240_ = _args[2];
lean_object* v_opts_2241_ = _args[3];
lean_object* v_clsEnabled_2242_ = _args[4];
lean_object* v_oldTraces_2243_ = _args[5];
lean_object* v_msg_2244_ = _args[6];
lean_object* v_resStartStop_2245_ = _args[7];
lean_object* v___y_2246_ = _args[8];
lean_object* v___y_2247_ = _args[9];
lean_object* v___y_2248_ = _args[10];
lean_object* v___y_2249_ = _args[11];
lean_object* v___y_2250_ = _args[12];
lean_object* v___y_2251_ = _args[13];
lean_object* v___y_2252_ = _args[14];
lean_object* v___y_2253_ = _args[15];
lean_object* v___y_2254_ = _args[16];
lean_object* v___y_2255_ = _args[17];
_start:
{
uint8_t v_collapsed_boxed_2256_; uint8_t v_clsEnabled_boxed_2257_; lean_object* v_res_2258_; 
v_collapsed_boxed_2256_ = lean_unbox(v_collapsed_2239_);
v_clsEnabled_boxed_2257_ = lean_unbox(v_clsEnabled_2242_);
v_res_2258_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4(v_cls_2238_, v_collapsed_boxed_2256_, v_tag_2240_, v_opts_2241_, v_clsEnabled_boxed_2257_, v_oldTraces_2243_, v_msg_2244_, v_resStartStop_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v___y_2246_);
lean_dec_ref(v_opts_2241_);
return v_res_2258_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2(void){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2262_ = lean_unsigned_to_nat(0u);
v___x_2263_ = l_Lean_Expr_bvar___override(v___x_2262_);
return v___x_2263_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8(void){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2270_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__7));
v___x_2271_ = lean_unsigned_to_nat(48u);
v___x_2272_ = lean_unsigned_to_nat(219u);
v___x_2273_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__6));
v___x_2274_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__5));
v___x_2275_ = l_mkPanicMessageWithDecl(v___x_2274_, v___x_2273_, v___x_2272_, v___x_2271_, v___x_2270_);
return v___x_2275_;
}
}
static double _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9(void){
_start:
{
lean_object* v___x_2276_; double v___x_2277_; 
v___x_2276_ = lean_unsigned_to_nat(1000000000u);
v___x_2277_ = lean_float_of_nat(v___x_2276_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(lean_object* v_e_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_, lean_object* v_a_2287_){
_start:
{
lean_object* v___y_2290_; uint8_t v___y_2291_; uint8_t v___y_2292_; lean_object* v_a_2293_; lean_object* v___y_2297_; uint8_t v___y_2298_; lean_object* v_a_2299_; 
if (lean_obj_tag(v_e_2278_) == 11)
{
lean_object* v_typeName_2303_; lean_object* v_idx_2304_; lean_object* v_struct_2305_; lean_object* v_res_2307_; lean_object* v___y_2308_; lean_object* v___y_2309_; lean_object* v___y_2310_; lean_object* v___y_2311_; lean_object* v___y_2312_; lean_object* v___y_2313_; lean_object* v___y_2314_; lean_object* v___y_2315_; lean_object* v___y_2316_; lean_object* v_options_2547_; uint8_t v_hasTrace_2548_; 
v_typeName_2303_ = lean_ctor_get(v_e_2278_, 0);
v_idx_2304_ = lean_ctor_get(v_e_2278_, 1);
v_struct_2305_ = lean_ctor_get(v_e_2278_, 2);
v_options_2547_ = lean_ctor_get(v_a_2286_, 2);
v_hasTrace_2548_ = lean_ctor_get_uint8(v_options_2547_, sizeof(void*)*1);
if (v_hasTrace_2548_ == 0)
{
lean_object* v___x_2549_; 
lean_inc(v_a_2287_);
lean_inc_ref(v_a_2286_);
lean_inc(v_a_2285_);
lean_inc_ref(v_a_2284_);
lean_inc(v_a_2283_);
lean_inc_ref(v_a_2282_);
lean_inc(v_a_2281_);
lean_inc_ref(v_a_2280_);
lean_inc(v_a_2279_);
lean_inc_ref(v_struct_2305_);
v___x_2549_ = lean_sym_simp(v_struct_2305_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2549_) == 0)
{
lean_object* v_a_2550_; 
v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc(v_a_2550_);
lean_dec_ref_known(v___x_2549_, 1);
v_res_2307_ = v_a_2550_;
v___y_2308_ = v_a_2279_;
v___y_2309_ = v_a_2280_;
v___y_2310_ = v_a_2281_;
v___y_2311_ = v_a_2282_;
v___y_2312_ = v_a_2283_;
v___y_2313_ = v_a_2284_;
v___y_2314_ = v_a_2285_;
v___y_2315_ = v_a_2286_;
v___y_2316_ = v_a_2287_;
goto v___jp_2306_;
}
else
{
lean_dec_ref_known(v_e_2278_, 3);
return v___x_2549_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2551_; lean_object* v___f_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; uint8_t v___x_2556_; lean_object* v___y_2558_; lean_object* v___y_2559_; lean_object* v_a_2560_; lean_object* v___y_2573_; lean_object* v___y_2574_; lean_object* v_a_2575_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v_a_2580_; lean_object* v___y_2583_; lean_object* v___y_2584_; uint8_t v___y_2585_; uint8_t v___y_2586_; lean_object* v___y_2587_; lean_object* v_a_2588_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2597_; uint8_t v___y_2598_; uint8_t v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v_a_2602_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v_a_2607_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v_a_2619_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v_a_2624_; lean_object* v___y_2627_; uint8_t v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; uint8_t v___y_2631_; lean_object* v_a_2632_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v___y_2641_; uint8_t v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v_a_2645_; 
v_inheritedTraceOptions_2551_ = lean_ctor_get(v_a_2286_, 13);
lean_inc_ref(v_e_2278_);
lean_inc(v_idx_2304_);
lean_inc(v_typeName_2303_);
v___f_2552_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__2___boxed), 14, 3);
lean_closure_set(v___f_2552_, 0, v_typeName_2303_);
lean_closure_set(v___f_2552_, 1, v_idx_2304_);
lean_closure_set(v___f_2552_, 2, v_e_2278_);
v___x_2553_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_2554_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_2555_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3);
v___x_2556_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2551_, v_options_2547_, v___x_2555_);
if (v___x_2556_ == 0)
{
lean_object* v___x_2848_; uint8_t v___x_2849_; 
v___x_2848_ = l_Lean_trace_profiler;
v___x_2849_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_2547_, v___x_2848_);
if (v___x_2849_ == 0)
{
lean_object* v___x_2850_; 
lean_dec_ref(v___f_2552_);
lean_inc(v_a_2287_);
lean_inc_ref(v_a_2286_);
lean_inc(v_a_2285_);
lean_inc_ref(v_a_2284_);
lean_inc(v_a_2283_);
lean_inc_ref(v_a_2282_);
lean_inc(v_a_2281_);
lean_inc_ref(v_a_2280_);
lean_inc(v_a_2279_);
lean_inc_ref(v_struct_2305_);
v___x_2850_ = lean_sym_simp(v_struct_2305_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v_a_2851_; 
v_a_2851_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_a_2851_);
lean_dec_ref_known(v___x_2850_, 1);
v_res_2307_ = v_a_2851_;
v___y_2308_ = v_a_2279_;
v___y_2309_ = v_a_2280_;
v___y_2310_ = v_a_2281_;
v___y_2311_ = v_a_2282_;
v___y_2312_ = v_a_2283_;
v___y_2313_ = v_a_2284_;
v___y_2314_ = v_a_2285_;
v___y_2315_ = v_a_2286_;
v___y_2316_ = v_a_2287_;
goto v___jp_2306_;
}
else
{
lean_dec_ref_known(v_e_2278_, 3);
return v___x_2850_;
}
}
else
{
goto v___jp_2648_;
}
}
else
{
goto v___jp_2648_;
}
v___jp_2557_:
{
lean_object* v___x_2561_; double v___x_2562_; double v___x_2563_; double v___x_2564_; double v___x_2565_; double v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; 
v___x_2561_ = lean_io_mono_nanos_now();
v___x_2562_ = lean_float_of_nat(v___y_2558_);
v___x_2563_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_2564_ = lean_float_div(v___x_2562_, v___x_2563_);
v___x_2565_ = lean_float_of_nat(v___x_2561_);
v___x_2566_ = lean_float_div(v___x_2565_, v___x_2563_);
v___x_2567_ = lean_box_float(v___x_2564_);
v___x_2568_ = lean_box_float(v___x_2566_);
v___x_2569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2569_, 0, v___x_2567_);
lean_ctor_set(v___x_2569_, 1, v___x_2568_);
v___x_2570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2570_, 0, v_a_2560_);
lean_ctor_set(v___x_2570_, 1, v___x_2569_);
v___x_2571_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4(v___x_2553_, v_hasTrace_2548_, v___x_2554_, v_options_2547_, v___x_2556_, v___y_2559_, v___f_2552_, v___x_2570_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_2571_;
}
v___jp_2572_:
{
lean_object* v___x_2576_; 
v___x_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2576_, 0, v_a_2575_);
v___y_2558_ = v___y_2573_;
v___y_2559_ = v___y_2574_;
v_a_2560_ = v___x_2576_;
goto v___jp_2557_;
}
v___jp_2577_:
{
lean_object* v___x_2581_; 
v___x_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2581_, 0, v_a_2580_);
v___y_2558_ = v___y_2578_;
v___y_2559_ = v___y_2579_;
v_a_2560_ = v___x_2581_;
goto v___jp_2557_;
}
v___jp_2582_:
{
lean_object* v___x_2589_; 
v___x_2589_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2589_, 0, v_a_2588_);
lean_ctor_set(v___x_2589_, 1, v___y_2584_);
lean_ctor_set_uint8(v___x_2589_, sizeof(void*)*2, v___y_2585_);
lean_ctor_set_uint8(v___x_2589_, sizeof(void*)*2 + 1, v___y_2586_);
v___y_2578_ = v___y_2583_;
v___y_2579_ = v___y_2587_;
v_a_2580_ = v___x_2589_;
goto v___jp_2577_;
}
v___jp_2590_:
{
if (lean_obj_tag(v___y_2593_) == 0)
{
lean_object* v_a_2594_; 
v_a_2594_ = lean_ctor_get(v___y_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___y_2593_, 1);
v___y_2578_ = v___y_2591_;
v___y_2579_ = v___y_2592_;
v_a_2580_ = v_a_2594_;
goto v___jp_2577_;
}
else
{
lean_object* v_a_2595_; 
v_a_2595_ = lean_ctor_get(v___y_2593_, 0);
lean_inc(v_a_2595_);
lean_dec_ref_known(v___y_2593_, 1);
v___y_2573_ = v___y_2591_;
v___y_2574_ = v___y_2592_;
v_a_2575_ = v_a_2595_;
goto v___jp_2572_;
}
}
v___jp_2596_:
{
lean_object* v___x_2603_; 
v___x_2603_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2603_, 0, v_a_2602_);
lean_ctor_set(v___x_2603_, 1, v___y_2600_);
lean_ctor_set_uint8(v___x_2603_, sizeof(void*)*2, v___y_2598_);
lean_ctor_set_uint8(v___x_2603_, sizeof(void*)*2 + 1, v___y_2599_);
v___y_2578_ = v___y_2597_;
v___y_2579_ = v___y_2601_;
v_a_2580_ = v___x_2603_;
goto v___jp_2577_;
}
v___jp_2604_:
{
lean_object* v___x_2608_; double v___x_2609_; double v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2608_ = lean_io_get_num_heartbeats();
v___x_2609_ = lean_float_of_nat(v___y_2605_);
v___x_2610_ = lean_float_of_nat(v___x_2608_);
v___x_2611_ = lean_box_float(v___x_2609_);
v___x_2612_ = lean_box_float(v___x_2610_);
v___x_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2611_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
v___x_2614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2614_, 0, v_a_2607_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
v___x_2615_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4(v___x_2553_, v_hasTrace_2548_, v___x_2554_, v_options_2547_, v___x_2556_, v___y_2606_, v___f_2552_, v___x_2614_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
return v___x_2615_;
}
v___jp_2616_:
{
lean_object* v___x_2620_; 
v___x_2620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2620_, 0, v_a_2619_);
v___y_2605_ = v___y_2617_;
v___y_2606_ = v___y_2618_;
v_a_2607_ = v___x_2620_;
goto v___jp_2604_;
}
v___jp_2621_:
{
lean_object* v___x_2625_; 
v___x_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2625_, 0, v_a_2624_);
v___y_2605_ = v___y_2622_;
v___y_2606_ = v___y_2623_;
v_a_2607_ = v___x_2625_;
goto v___jp_2604_;
}
v___jp_2626_:
{
lean_object* v___x_2633_; 
v___x_2633_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2633_, 0, v_a_2632_);
lean_ctor_set(v___x_2633_, 1, v___y_2629_);
lean_ctor_set_uint8(v___x_2633_, sizeof(void*)*2, v___y_2628_);
lean_ctor_set_uint8(v___x_2633_, sizeof(void*)*2 + 1, v___y_2631_);
v___y_2622_ = v___y_2627_;
v___y_2623_ = v___y_2630_;
v_a_2624_ = v___x_2633_;
goto v___jp_2621_;
}
v___jp_2634_:
{
if (lean_obj_tag(v___y_2637_) == 0)
{
lean_object* v_a_2638_; 
v_a_2638_ = lean_ctor_get(v___y_2637_, 0);
lean_inc(v_a_2638_);
lean_dec_ref_known(v___y_2637_, 1);
v___y_2622_ = v___y_2635_;
v___y_2623_ = v___y_2636_;
v_a_2624_ = v_a_2638_;
goto v___jp_2621_;
}
else
{
lean_object* v_a_2639_; 
v_a_2639_ = lean_ctor_get(v___y_2637_, 0);
lean_inc(v_a_2639_);
lean_dec_ref_known(v___y_2637_, 1);
v___y_2617_ = v___y_2635_;
v___y_2618_ = v___y_2636_;
v_a_2619_ = v_a_2639_;
goto v___jp_2616_;
}
}
v___jp_2640_:
{
uint8_t v___x_2646_; lean_object* v___x_2647_; 
v___x_2646_ = 0;
v___x_2647_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2647_, 0, v_a_2645_);
lean_ctor_set(v___x_2647_, 1, v___y_2643_);
lean_ctor_set_uint8(v___x_2647_, sizeof(void*)*2, v___y_2642_);
lean_ctor_set_uint8(v___x_2647_, sizeof(void*)*2 + 1, v___x_2646_);
v___y_2622_ = v___y_2641_;
v___y_2623_ = v___y_2644_;
v_a_2624_ = v___x_2647_;
goto v___jp_2621_;
}
v___jp_2648_:
{
lean_object* v___x_2649_; lean_object* v_a_2650_; lean_object* v___x_2651_; uint8_t v___x_2652_; 
v___x_2649_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg(v_a_2287_);
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
lean_dec_ref(v___x_2649_);
v___x_2651_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2652_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_2547_, v___x_2651_);
if (v___x_2652_ == 0)
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = lean_io_mono_nanos_now();
lean_inc(v_a_2287_);
lean_inc_ref(v_a_2286_);
lean_inc(v_a_2285_);
lean_inc_ref(v_a_2284_);
lean_inc(v_a_2283_);
lean_inc_ref(v_a_2282_);
lean_inc(v_a_2281_);
lean_inc_ref(v_a_2280_);
lean_inc(v_a_2279_);
lean_inc_ref(v_struct_2305_);
v___x_2654_ = lean_sym_simp(v_struct_2305_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
lean_dec_ref_known(v___x_2654_, 1);
if (lean_obj_tag(v_a_2655_) == 0)
{
uint8_t v_contextDependent_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2677_; 
v_contextDependent_2656_ = lean_ctor_get_uint8(v_a_2655_, 1);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_a_2655_);
if (v_isSharedCheck_2677_ == 0)
{
v___x_2658_ = v_a_2655_;
v_isShared_2659_ = v_isSharedCheck_2677_;
goto v_resetjp_2657_;
}
else
{
lean_dec(v_a_2655_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2677_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
uint8_t v___x_2660_; lean_object* v___x_2661_; lean_object* v___f_2662_; lean_object* v___x_2663_; 
v___x_2660_ = 1;
v___x_2661_ = lean_box(v___x_2660_);
v___f_2662_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2662_, 0, v___x_2661_);
lean_closure_set(v___f_2662_, 1, v_e_2278_);
v___x_2663_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2662_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_a_2664_; 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
lean_inc(v_a_2664_);
lean_dec_ref_known(v___x_2663_, 1);
if (lean_obj_tag(v_a_2664_) == 1)
{
lean_object* v_val_2665_; lean_object* v___x_2666_; 
lean_del_object(v___x_2658_);
v_val_2665_ = lean_ctor_get(v_a_2664_, 0);
lean_inc(v_val_2665_);
lean_dec_ref_known(v_a_2664_, 1);
v___x_2666_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2665_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v___x_2668_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc_n(v_a_2667_, 2);
lean_dec_ref_known(v___x_2666_, 1);
v___x_2668_ = l_Lean_Meta_Sym_mkEqRefl(v_a_2667_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_a_2669_; lean_object* v___x_2670_; 
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2669_);
lean_dec_ref_known(v___x_2668_, 1);
v___x_2670_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2670_, 0, v_a_2667_);
lean_ctor_set(v___x_2670_, 1, v_a_2669_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*2, v_contextDependent_2656_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*2 + 1, v___x_2652_);
v___y_2578_ = v___x_2653_;
v___y_2579_ = v_a_2650_;
v_a_2580_ = v___x_2670_;
goto v___jp_2577_;
}
else
{
lean_object* v_a_2671_; 
lean_dec(v_a_2667_);
v_a_2671_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2671_);
lean_dec_ref_known(v___x_2668_, 1);
v___y_2573_ = v___x_2653_;
v___y_2574_ = v_a_2650_;
v_a_2575_ = v_a_2671_;
goto v___jp_2572_;
}
}
else
{
lean_object* v_a_2672_; 
v_a_2672_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_a_2672_);
lean_dec_ref_known(v___x_2666_, 1);
v___y_2573_ = v___x_2653_;
v___y_2574_ = v_a_2650_;
v_a_2575_ = v_a_2672_;
goto v___jp_2572_;
}
}
else
{
lean_object* v___x_2674_; 
lean_dec(v_a_2664_);
if (v_isShared_2659_ == 0)
{
v___x_2674_ = v___x_2658_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_2675_, 1, v_contextDependent_2656_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
lean_ctor_set_uint8(v___x_2674_, 0, v_hasTrace_2548_);
v___y_2578_ = v___x_2653_;
v___y_2579_ = v_a_2650_;
v_a_2580_ = v___x_2674_;
goto v___jp_2577_;
}
}
}
else
{
lean_object* v_a_2676_; 
lean_del_object(v___x_2658_);
v_a_2676_ = lean_ctor_get(v___x_2663_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v___x_2663_, 1);
v___y_2573_ = v___x_2653_;
v___y_2574_ = v_a_2650_;
v_a_2575_ = v_a_2676_;
goto v___jp_2572_;
}
}
}
else
{
lean_object* v_e_x27_2678_; lean_object* v_proof_2679_; uint8_t v_contextDependent_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2749_; 
v_e_x27_2678_ = lean_ctor_get(v_a_2655_, 0);
v_proof_2679_ = lean_ctor_get(v_a_2655_, 1);
v_contextDependent_2680_ = lean_ctor_get_uint8(v_a_2655_, sizeof(void*)*2 + 1);
v_isSharedCheck_2749_ = !lean_is_exclusive(v_a_2655_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2682_ = v_a_2655_;
v_isShared_2683_ = v_isSharedCheck_2749_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_proof_2679_);
lean_inc(v_e_x27_2678_);
lean_dec(v_a_2655_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2749_;
goto v_resetjp_2681_;
}
v_resetjp_2681_:
{
lean_object* v___x_2684_; 
lean_inc_ref(v_e_x27_2678_);
v___x_2684_ = l_Lean_Meta_Sym_inferType(v_e_x27_2678_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_object* v_a_2685_; lean_object* v___x_2686_; uint8_t v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2685_);
lean_dec_ref_known(v___x_2684_, 1);
v___x_2686_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1));
v___x_2687_ = 0;
v___x_2688_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2);
lean_inc(v_idx_2304_);
lean_inc(v_typeName_2303_);
v___x_2689_ = l_Lean_Expr_proj___override(v_typeName_2303_, v_idx_2304_, v___x_2688_);
v___x_2690_ = l_Lean_mkLambda(v___x_2686_, v___x_2687_, v_a_2685_, v___x_2689_);
lean_inc_ref(v___x_2690_);
v___x_2691_ = l_Lean_Meta_Sym_inferType(v___x_2690_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; uint8_t v___x_2693_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2692_);
lean_dec_ref_known(v___x_2691_, 1);
v___x_2693_ = l_Lean_Expr_isArrow(v_a_2692_);
if (v___x_2693_ == 0)
{
uint8_t v___x_2694_; lean_object* v___x_2695_; lean_object* v___f_2696_; lean_object* v___x_2697_; 
lean_dec(v_a_2692_);
v___x_2694_ = 1;
v___x_2695_ = lean_box(v___x_2694_);
lean_inc_ref(v_e_2278_);
v___f_2696_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2696_, 0, v___x_2695_);
lean_closure_set(v___f_2696_, 1, v_e_2278_);
v___x_2697_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2696_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2698_);
lean_dec_ref_known(v___x_2697_, 1);
if (lean_obj_tag(v_a_2698_) == 0)
{
lean_object* v___x_2699_; 
lean_del_object(v___x_2682_);
lean_inc_ref(v_e_x27_2678_);
lean_inc_ref(v_struct_2305_);
v___x_2699_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_struct_2305_, v_e_x27_2678_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v_a_2700_; uint8_t v___x_2701_; 
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_a_2700_);
lean_dec_ref_known(v___x_2699_, 1);
v___x_2701_ = lean_unbox(v_a_2700_);
lean_dec(v_a_2700_);
if (v___x_2701_ == 0)
{
lean_object* v___x_2702_; 
lean_dec_ref(v___x_2690_);
lean_dec_ref(v_proof_2679_);
lean_dec_ref(v_e_x27_2678_);
lean_dec_ref_known(v_e_2278_, 3);
v___x_2702_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2702_, 0, v_hasTrace_2548_);
lean_ctor_set_uint8(v___x_2702_, 1, v_contextDependent_2680_);
v___y_2578_ = v___x_2653_;
v___y_2579_ = v_a_2650_;
v_a_2580_ = v___x_2702_;
goto v___jp_2577_;
}
else
{
lean_object* v___x_2703_; 
v___x_2703_ = l_Lean_Meta_mkHCongr(v___x_2690_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v_proof_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2703_, 1);
v_proof_2705_ = lean_ctor_get(v_a_2704_, 1);
lean_inc_ref(v_proof_2705_);
lean_dec(v_a_2704_);
lean_inc_ref(v_e_x27_2678_);
lean_inc_ref(v_struct_2305_);
v___x_2706_ = l_Lean_mkApp3(v_proof_2705_, v_struct_2305_, v_e_x27_2678_, v_proof_2679_);
v___x_2707_ = l_Lean_Meta_mkEqOfHEq(v___x_2706_, v___x_2652_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; uint8_t v___x_2709_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
lean_inc(v_a_2708_);
lean_dec_ref_known(v___x_2707_, 1);
v___x_2709_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2305_, v_e_x27_2678_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2710_; 
lean_inc(v_idx_2304_);
lean_inc(v_typeName_2303_);
lean_dec_ref_known(v_e_2278_, 3);
v___x_2710_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2303_, v_idx_2304_, v_e_x27_2678_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v_a_2711_; 
v_a_2711_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2711_);
lean_dec_ref_known(v___x_2710_, 1);
v___y_2583_ = v___x_2653_;
v___y_2584_ = v_a_2708_;
v___y_2585_ = v_contextDependent_2680_;
v___y_2586_ = v___x_2652_;
v___y_2587_ = v_a_2650_;
v_a_2588_ = v_a_2711_;
goto v___jp_2582_;
}
else
{
lean_object* v_a_2712_; 
lean_dec(v_a_2708_);
v_a_2712_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_a_2712_);
lean_dec_ref_known(v___x_2710_, 1);
v___y_2573_ = v___x_2653_;
v___y_2574_ = v_a_2650_;
v_a_2575_ = v_a_2712_;
goto v___jp_2572_;
}
}
else
{
lean_dec_ref(v_e_x27_2678_);
v___y_2583_ = v___x_2653_;
v___y_2584_ = v_a_2708_;
v___y_2585_ = v_contextDependent_2680_;
v___y_2586_ = v___x_2652_;
v___y_2587_ = v_a_2650_;
v_a_2588_ = v_e_2278_;
goto v___jp_2582_;
}
}
else
{
lean_object* v_a_2713_; 
lean_dec_ref(v_e_x27_2678_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2713_ = lean_ctor_get(v___x_2707_, 0);
lean_inc(v_a_2713_);
lean_dec_ref_known(v___x_2707_, 1);
v___y_2573_ = v___x_2653_;
v___y_2574_ = v_a_2650_;
v_a_2575_ = v_a_2713_;
goto v___jp_2572_;
}
}
else
{
lean_object* v_a_2714_; 
lean_dec_ref(v_proof_2679_);
lean_dec_ref(v_e_x27_2678_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2714_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2714_);
lean_dec_ref_known(v___x_2703_, 1);
v___y_2573_ = v___x_2653_;
v___y_2574_ = v_a_2650_;
v_a_2575_ = v_a_2714_;
goto v___jp_2572_;
}
}
}
else
{
lean_object* v_a_2715_; 
lean_dec_ref(v___x_2690_);
lean_dec_ref(v_proof_2679_);
lean_dec_ref(v_e_x27_2678_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2715_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_a_2715_);
lean_dec_ref_known(v___x_2699_, 1);
v___y_2573_ = v___x_2653_;
v___y_2574_ = v_a_2650_;
v_a_2575_ = v_a_2715_;
goto v___jp_2572_;
}
}
else
{
lean_object* v_val_2716_; lean_object* v___x_2717_; 
lean_dec_ref(v___x_2690_);
lean_dec_ref(v_proof_2679_);
lean_dec_ref(v_e_x27_2678_);
lean_dec_ref_known(v_e_2278_, 3);
v_val_2716_ = lean_ctor_get(v_a_2698_, 0);
lean_inc(v_val_2716_);
lean_dec_ref_known(v_a_2698_, 1);
v___x_2717_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2716_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_a_2718_; lean_object* v___x_2719_; 
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
lean_inc_n(v_a_2718_, 2);
lean_dec_ref_known(v___x_2717_, 1);
v___x_2719_ = l_Lean_Meta_Sym_mkEqRefl(v_a_2718_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v_a_2720_; lean_object* v___x_2722_; 
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_a_2720_);
lean_dec_ref_known(v___x_2719_, 1);
if (v_isShared_2683_ == 0)
{
lean_ctor_set(v___x_2682_, 1, v_a_2720_);
lean_ctor_set(v___x_2682_, 0, v_a_2718_);
v___x_2722_ = v___x_2682_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2718_);
lean_ctor_set(v_reuseFailAlloc_2723_, 1, v_a_2720_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*2, v_contextDependent_2680_);
lean_ctor_set_uint8(v___x_2722_, sizeof(void*)*2 + 1, v___x_2652_);
v___y_2578_ = v___x_2653_;
v___y_2579_ = v_a_2650_;
v_a_2580_ = v___x_2722_;
goto v___jp_2577_;
}
}
else
{
lean_object* v_a_2724_; 
lean_dec(v_a_2718_);
lean_del_object(v___x_2682_);
v_a_2724_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_a_2724_);
lean_dec_ref_known(v___x_2719_, 1);
v___y_2573_ = v___x_2653_;
v___y_2574_ = v_a_2650_;
v_a_2575_ = v_a_2724_;
goto v___jp_2572_;
}
}
else
{
lean_object* v_a_2725_; 
lean_del_object(v___x_2682_);
v_a_2725_ = lean_ctor_get(v___x_2717_, 0);
lean_inc(v_a_2725_);
lean_dec_ref_known(v___x_2717_, 1);
v___y_2573_ = v___x_2653_;
v___y_2574_ = v_a_2650_;
v_a_2575_ = v_a_2725_;
goto v___jp_2572_;
}
}
}
else
{
lean_object* v_a_2726_; 
lean_dec_ref(v___x_2690_);
lean_del_object(v___x_2682_);
lean_dec_ref(v_proof_2679_);
lean_dec_ref(v_e_x27_2678_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2726_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2726_);
lean_dec_ref_known(v___x_2697_, 1);
v___y_2573_ = v___x_2653_;
v___y_2574_ = v_a_2650_;
v_a_2575_ = v_a_2726_;
goto v___jp_2572_;
}
}
else
{
lean_del_object(v___x_2682_);
if (lean_obj_tag(v_a_2692_) == 7)
{
lean_object* v_binderType_2727_; lean_object* v_body_2728_; lean_object* v___x_2729_; 
v_binderType_2727_ = lean_ctor_get(v_a_2692_, 1);
lean_inc_ref_n(v_binderType_2727_, 2);
v_body_2728_ = lean_ctor_get(v_a_2692_, 2);
lean_inc_ref(v_body_2728_);
lean_dec_ref_known(v_a_2692_, 3);
v___x_2729_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2727_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2729_) == 0)
{
lean_object* v_a_2730_; lean_object* v___x_2731_; 
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_a_2730_);
lean_dec_ref_known(v___x_2729_, 1);
lean_inc_ref(v_body_2728_);
v___x_2731_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_2728_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; uint8_t v___x_2739_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2732_);
lean_dec_ref_known(v___x_2731_, 1);
v___x_2733_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4));
v___x_2734_ = lean_box(0);
v___x_2735_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2735_, 0, v_a_2732_);
lean_ctor_set(v___x_2735_, 1, v___x_2734_);
v___x_2736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2736_, 0, v_a_2730_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
v___x_2737_ = l_Lean_mkConst(v___x_2733_, v___x_2736_);
lean_inc_ref(v_e_x27_2678_);
lean_inc_ref(v_struct_2305_);
v___x_2738_ = l_Lean_mkApp6(v___x_2737_, v_binderType_2727_, v_body_2728_, v_struct_2305_, v_e_x27_2678_, v___x_2690_, v_proof_2679_);
v___x_2739_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2305_, v_e_x27_2678_);
if (v___x_2739_ == 0)
{
lean_object* v___x_2740_; 
lean_inc(v_idx_2304_);
lean_inc(v_typeName_2303_);
lean_dec_ref_known(v_e_2278_, 3);
v___x_2740_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2303_, v_idx_2304_, v_e_x27_2678_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_a_2741_; 
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2741_);
lean_dec_ref_known(v___x_2740_, 1);
v___y_2597_ = v___x_2653_;
v___y_2598_ = v_contextDependent_2680_;
v___y_2599_ = v___x_2652_;
v___y_2600_ = v___x_2738_;
v___y_2601_ = v_a_2650_;
v_a_2602_ = v_a_2741_;
goto v___jp_2596_;
}
else
{
lean_object* v_a_2742_; 
lean_dec_ref(v___x_2738_);
v_a_2742_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_a_2742_);
lean_dec_ref_known(v___x_2740_, 1);
v___y_2573_ = v___x_2653_;
v___y_2574_ = v_a_2650_;
v_a_2575_ = v_a_2742_;
goto v___jp_2572_;
}
}
else
{
lean_dec_ref(v_e_x27_2678_);
v___y_2597_ = v___x_2653_;
v___y_2598_ = v_contextDependent_2680_;
v___y_2599_ = v___x_2652_;
v___y_2600_ = v___x_2738_;
v___y_2601_ = v_a_2650_;
v_a_2602_ = v_e_2278_;
goto v___jp_2596_;
}
}
else
{
lean_object* v_a_2743_; 
lean_dec(v_a_2730_);
lean_dec_ref(v_body_2728_);
lean_dec_ref(v_binderType_2727_);
lean_dec_ref(v___x_2690_);
lean_dec_ref(v_proof_2679_);
lean_dec_ref(v_e_x27_2678_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2743_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2743_);
lean_dec_ref_known(v___x_2731_, 1);
v___y_2573_ = v___x_2653_;
v___y_2574_ = v_a_2650_;
v_a_2575_ = v_a_2743_;
goto v___jp_2572_;
}
}
else
{
lean_object* v_a_2744_; 
lean_dec_ref(v_body_2728_);
lean_dec_ref(v_binderType_2727_);
lean_dec_ref(v___x_2690_);
lean_dec_ref(v_proof_2679_);
lean_dec_ref(v_e_x27_2678_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2744_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_a_2744_);
lean_dec_ref_known(v___x_2729_, 1);
v___y_2573_ = v___x_2653_;
v___y_2574_ = v_a_2650_;
v_a_2575_ = v_a_2744_;
goto v___jp_2572_;
}
}
else
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
lean_dec(v_a_2692_);
lean_dec_ref(v___x_2690_);
lean_dec_ref(v_proof_2679_);
lean_dec_ref(v_e_x27_2678_);
lean_dec_ref_known(v_e_2278_, 3);
v___x_2745_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8);
v___x_2746_ = l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(v___x_2745_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
v___y_2591_ = v___x_2653_;
v___y_2592_ = v_a_2650_;
v___y_2593_ = v___x_2746_;
goto v___jp_2590_;
}
}
}
else
{
lean_object* v_a_2747_; 
lean_dec_ref(v___x_2690_);
lean_del_object(v___x_2682_);
lean_dec_ref(v_proof_2679_);
lean_dec_ref(v_e_x27_2678_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2747_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2747_);
lean_dec_ref_known(v___x_2691_, 1);
v___y_2573_ = v___x_2653_;
v___y_2574_ = v_a_2650_;
v_a_2575_ = v_a_2747_;
goto v___jp_2572_;
}
}
else
{
lean_object* v_a_2748_; 
lean_del_object(v___x_2682_);
lean_dec_ref(v_proof_2679_);
lean_dec_ref(v_e_x27_2678_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2748_ = lean_ctor_get(v___x_2684_, 0);
lean_inc(v_a_2748_);
lean_dec_ref_known(v___x_2684_, 1);
v___y_2573_ = v___x_2653_;
v___y_2574_ = v_a_2650_;
v_a_2575_ = v_a_2748_;
goto v___jp_2572_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2278_, 3);
v___y_2591_ = v___x_2653_;
v___y_2592_ = v_a_2650_;
v___y_2593_ = v___x_2654_;
goto v___jp_2590_;
}
}
else
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2287_);
lean_inc_ref(v_a_2286_);
lean_inc(v_a_2285_);
lean_inc_ref(v_a_2284_);
lean_inc(v_a_2283_);
lean_inc_ref(v_a_2282_);
lean_inc(v_a_2281_);
lean_inc_ref(v_a_2280_);
lean_inc(v_a_2279_);
lean_inc_ref(v_struct_2305_);
v___x_2751_ = lean_sym_simp(v_struct_2305_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v_a_2752_; 
v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
lean_inc(v_a_2752_);
lean_dec_ref_known(v___x_2751_, 1);
if (lean_obj_tag(v_a_2752_) == 0)
{
uint8_t v_contextDependent_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2775_; 
v_contextDependent_2753_ = lean_ctor_get_uint8(v_a_2752_, 1);
v_isSharedCheck_2775_ = !lean_is_exclusive(v_a_2752_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2755_ = v_a_2752_;
v_isShared_2756_ = v_isSharedCheck_2775_;
goto v_resetjp_2754_;
}
else
{
lean_dec(v_a_2752_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2775_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
uint8_t v___x_2757_; lean_object* v___x_2758_; lean_object* v___f_2759_; lean_object* v___x_2760_; 
v___x_2757_ = 1;
v___x_2758_ = lean_box(v___x_2757_);
v___f_2759_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2759_, 0, v___x_2758_);
lean_closure_set(v___f_2759_, 1, v_e_2278_);
v___x_2760_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2759_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_object* v_a_2761_; 
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
lean_inc(v_a_2761_);
lean_dec_ref_known(v___x_2760_, 1);
if (lean_obj_tag(v_a_2761_) == 1)
{
lean_object* v_val_2762_; lean_object* v___x_2763_; 
lean_del_object(v___x_2755_);
v_val_2762_ = lean_ctor_get(v_a_2761_, 0);
lean_inc(v_val_2762_);
lean_dec_ref_known(v_a_2761_, 1);
v___x_2763_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2762_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; lean_object* v___x_2765_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
lean_inc_n(v_a_2764_, 2);
lean_dec_ref_known(v___x_2763_, 1);
v___x_2765_ = l_Lean_Meta_Sym_mkEqRefl(v_a_2764_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v_a_2766_; uint8_t v___x_2767_; lean_object* v___x_2768_; 
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_a_2766_);
lean_dec_ref_known(v___x_2765_, 1);
v___x_2767_ = 0;
v___x_2768_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2768_, 0, v_a_2764_);
lean_ctor_set(v___x_2768_, 1, v_a_2766_);
lean_ctor_set_uint8(v___x_2768_, sizeof(void*)*2, v_contextDependent_2753_);
lean_ctor_set_uint8(v___x_2768_, sizeof(void*)*2 + 1, v___x_2767_);
v___y_2622_ = v___x_2750_;
v___y_2623_ = v_a_2650_;
v_a_2624_ = v___x_2768_;
goto v___jp_2621_;
}
else
{
lean_object* v_a_2769_; 
lean_dec(v_a_2764_);
v_a_2769_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_a_2769_);
lean_dec_ref_known(v___x_2765_, 1);
v___y_2617_ = v___x_2750_;
v___y_2618_ = v_a_2650_;
v_a_2619_ = v_a_2769_;
goto v___jp_2616_;
}
}
else
{
lean_object* v_a_2770_; 
v_a_2770_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_a_2770_);
lean_dec_ref_known(v___x_2763_, 1);
v___y_2617_ = v___x_2750_;
v___y_2618_ = v_a_2650_;
v_a_2619_ = v_a_2770_;
goto v___jp_2616_;
}
}
else
{
lean_object* v___x_2772_; 
lean_dec(v_a_2761_);
if (v_isShared_2756_ == 0)
{
v___x_2772_ = v___x_2755_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_2773_, 1, v_contextDependent_2753_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
lean_ctor_set_uint8(v___x_2772_, 0, v___x_2652_);
v___y_2622_ = v___x_2750_;
v___y_2623_ = v_a_2650_;
v_a_2624_ = v___x_2772_;
goto v___jp_2621_;
}
}
}
else
{
lean_object* v_a_2774_; 
lean_del_object(v___x_2755_);
v_a_2774_ = lean_ctor_get(v___x_2760_, 0);
lean_inc(v_a_2774_);
lean_dec_ref_known(v___x_2760_, 1);
v___y_2617_ = v___x_2750_;
v___y_2618_ = v_a_2650_;
v_a_2619_ = v_a_2774_;
goto v___jp_2616_;
}
}
}
else
{
lean_object* v_e_x27_2776_; lean_object* v_proof_2777_; uint8_t v_contextDependent_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2847_; 
v_e_x27_2776_ = lean_ctor_get(v_a_2752_, 0);
v_proof_2777_ = lean_ctor_get(v_a_2752_, 1);
v_contextDependent_2778_ = lean_ctor_get_uint8(v_a_2752_, sizeof(void*)*2 + 1);
v_isSharedCheck_2847_ = !lean_is_exclusive(v_a_2752_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2780_ = v_a_2752_;
v_isShared_2781_ = v_isSharedCheck_2847_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_proof_2777_);
lean_inc(v_e_x27_2776_);
lean_dec(v_a_2752_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2847_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2782_; 
lean_inc_ref(v_e_x27_2776_);
v___x_2782_ = l_Lean_Meta_Sym_inferType(v_e_x27_2776_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2784_; uint8_t v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_a_2783_);
lean_dec_ref_known(v___x_2782_, 1);
v___x_2784_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1));
v___x_2785_ = 0;
v___x_2786_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2);
lean_inc(v_idx_2304_);
lean_inc(v_typeName_2303_);
v___x_2787_ = l_Lean_Expr_proj___override(v_typeName_2303_, v_idx_2304_, v___x_2786_);
v___x_2788_ = l_Lean_mkLambda(v___x_2784_, v___x_2785_, v_a_2783_, v___x_2787_);
lean_inc_ref(v___x_2788_);
v___x_2789_ = l_Lean_Meta_Sym_inferType(v___x_2788_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; uint8_t v___x_2791_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___x_2789_, 1);
v___x_2791_ = l_Lean_Expr_isArrow(v_a_2790_);
if (v___x_2791_ == 0)
{
uint8_t v___x_2792_; lean_object* v___x_2793_; lean_object* v___f_2794_; lean_object* v___x_2795_; 
lean_dec(v_a_2790_);
v___x_2792_ = 1;
v___x_2793_ = lean_box(v___x_2792_);
lean_inc_ref(v_e_2278_);
v___f_2794_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2794_, 0, v___x_2793_);
lean_closure_set(v___f_2794_, 1, v_e_2278_);
v___x_2795_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2794_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2796_; 
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_a_2796_);
lean_dec_ref_known(v___x_2795_, 1);
if (lean_obj_tag(v_a_2796_) == 0)
{
lean_object* v___x_2797_; 
lean_del_object(v___x_2780_);
lean_inc_ref(v_e_x27_2776_);
lean_inc_ref(v_struct_2305_);
v___x_2797_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_struct_2305_, v_e_x27_2776_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; uint8_t v___x_2799_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2798_);
lean_dec_ref_known(v___x_2797_, 1);
v___x_2799_ = lean_unbox(v_a_2798_);
lean_dec(v_a_2798_);
if (v___x_2799_ == 0)
{
lean_object* v___x_2800_; 
lean_dec_ref(v___x_2788_);
lean_dec_ref(v_proof_2777_);
lean_dec_ref(v_e_x27_2776_);
lean_dec_ref_known(v_e_2278_, 3);
v___x_2800_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2800_, 0, v___x_2652_);
lean_ctor_set_uint8(v___x_2800_, 1, v_contextDependent_2778_);
v___y_2622_ = v___x_2750_;
v___y_2623_ = v_a_2650_;
v_a_2624_ = v___x_2800_;
goto v___jp_2621_;
}
else
{
lean_object* v___x_2801_; 
v___x_2801_ = l_Lean_Meta_mkHCongr(v___x_2788_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; lean_object* v_proof_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2802_);
lean_dec_ref_known(v___x_2801_, 1);
v_proof_2803_ = lean_ctor_get(v_a_2802_, 1);
lean_inc_ref(v_proof_2803_);
lean_dec(v_a_2802_);
lean_inc_ref(v_e_x27_2776_);
lean_inc_ref(v_struct_2305_);
v___x_2804_ = l_Lean_mkApp3(v_proof_2803_, v_struct_2305_, v_e_x27_2776_, v_proof_2777_);
v___x_2805_ = l_Lean_Meta_mkEqOfHEq(v___x_2804_, v___x_2791_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; uint8_t v___x_2807_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2806_);
lean_dec_ref_known(v___x_2805_, 1);
v___x_2807_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2305_, v_e_x27_2776_);
if (v___x_2807_ == 0)
{
lean_object* v___x_2808_; 
lean_inc(v_idx_2304_);
lean_inc(v_typeName_2303_);
lean_dec_ref_known(v_e_2278_, 3);
v___x_2808_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2303_, v_idx_2304_, v_e_x27_2776_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_a_2809_);
lean_dec_ref_known(v___x_2808_, 1);
v___y_2627_ = v___x_2750_;
v___y_2628_ = v_contextDependent_2778_;
v___y_2629_ = v_a_2806_;
v___y_2630_ = v_a_2650_;
v___y_2631_ = v___x_2791_;
v_a_2632_ = v_a_2809_;
goto v___jp_2626_;
}
else
{
lean_object* v_a_2810_; 
lean_dec(v_a_2806_);
v_a_2810_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_a_2810_);
lean_dec_ref_known(v___x_2808_, 1);
v___y_2617_ = v___x_2750_;
v___y_2618_ = v_a_2650_;
v_a_2619_ = v_a_2810_;
goto v___jp_2616_;
}
}
else
{
lean_dec_ref(v_e_x27_2776_);
v___y_2627_ = v___x_2750_;
v___y_2628_ = v_contextDependent_2778_;
v___y_2629_ = v_a_2806_;
v___y_2630_ = v_a_2650_;
v___y_2631_ = v___x_2791_;
v_a_2632_ = v_e_2278_;
goto v___jp_2626_;
}
}
else
{
lean_object* v_a_2811_; 
lean_dec_ref(v_e_x27_2776_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2811_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2811_);
lean_dec_ref_known(v___x_2805_, 1);
v___y_2617_ = v___x_2750_;
v___y_2618_ = v_a_2650_;
v_a_2619_ = v_a_2811_;
goto v___jp_2616_;
}
}
else
{
lean_object* v_a_2812_; 
lean_dec_ref(v_proof_2777_);
lean_dec_ref(v_e_x27_2776_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2812_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2812_);
lean_dec_ref_known(v___x_2801_, 1);
v___y_2617_ = v___x_2750_;
v___y_2618_ = v_a_2650_;
v_a_2619_ = v_a_2812_;
goto v___jp_2616_;
}
}
}
else
{
lean_object* v_a_2813_; 
lean_dec_ref(v___x_2788_);
lean_dec_ref(v_proof_2777_);
lean_dec_ref(v_e_x27_2776_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2813_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2813_);
lean_dec_ref_known(v___x_2797_, 1);
v___y_2617_ = v___x_2750_;
v___y_2618_ = v_a_2650_;
v_a_2619_ = v_a_2813_;
goto v___jp_2616_;
}
}
else
{
lean_object* v_val_2814_; lean_object* v___x_2815_; 
lean_dec_ref(v___x_2788_);
lean_dec_ref(v_proof_2777_);
lean_dec_ref(v_e_x27_2776_);
lean_dec_ref_known(v_e_2278_, 3);
v_val_2814_ = lean_ctor_get(v_a_2796_, 0);
lean_inc(v_val_2814_);
lean_dec_ref_known(v_a_2796_, 1);
v___x_2815_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2814_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; lean_object* v___x_2817_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc_n(v_a_2816_, 2);
lean_dec_ref_known(v___x_2815_, 1);
v___x_2817_ = l_Lean_Meta_Sym_mkEqRefl(v_a_2816_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v___x_2820_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_a_2818_);
lean_dec_ref_known(v___x_2817_, 1);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 1, v_a_2818_);
lean_ctor_set(v___x_2780_, 0, v_a_2816_);
v___x_2820_ = v___x_2780_;
goto v_reusejp_2819_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2816_);
lean_ctor_set(v_reuseFailAlloc_2821_, 1, v_a_2818_);
v___x_2820_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2819_;
}
v_reusejp_2819_:
{
lean_ctor_set_uint8(v___x_2820_, sizeof(void*)*2, v_contextDependent_2778_);
lean_ctor_set_uint8(v___x_2820_, sizeof(void*)*2 + 1, v___x_2791_);
v___y_2622_ = v___x_2750_;
v___y_2623_ = v_a_2650_;
v_a_2624_ = v___x_2820_;
goto v___jp_2621_;
}
}
else
{
lean_object* v_a_2822_; 
lean_dec(v_a_2816_);
lean_del_object(v___x_2780_);
v_a_2822_ = lean_ctor_get(v___x_2817_, 0);
lean_inc(v_a_2822_);
lean_dec_ref_known(v___x_2817_, 1);
v___y_2617_ = v___x_2750_;
v___y_2618_ = v_a_2650_;
v_a_2619_ = v_a_2822_;
goto v___jp_2616_;
}
}
else
{
lean_object* v_a_2823_; 
lean_del_object(v___x_2780_);
v_a_2823_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2823_);
lean_dec_ref_known(v___x_2815_, 1);
v___y_2617_ = v___x_2750_;
v___y_2618_ = v_a_2650_;
v_a_2619_ = v_a_2823_;
goto v___jp_2616_;
}
}
}
else
{
lean_object* v_a_2824_; 
lean_dec_ref(v___x_2788_);
lean_del_object(v___x_2780_);
lean_dec_ref(v_proof_2777_);
lean_dec_ref(v_e_x27_2776_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2824_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_a_2824_);
lean_dec_ref_known(v___x_2795_, 1);
v___y_2617_ = v___x_2750_;
v___y_2618_ = v_a_2650_;
v_a_2619_ = v_a_2824_;
goto v___jp_2616_;
}
}
else
{
lean_del_object(v___x_2780_);
if (lean_obj_tag(v_a_2790_) == 7)
{
lean_object* v_binderType_2825_; lean_object* v_body_2826_; lean_object* v___x_2827_; 
v_binderType_2825_ = lean_ctor_get(v_a_2790_, 1);
lean_inc_ref_n(v_binderType_2825_, 2);
v_body_2826_ = lean_ctor_get(v_a_2790_, 2);
lean_inc_ref(v_body_2826_);
lean_dec_ref_known(v_a_2790_, 3);
v___x_2827_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2825_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v_a_2828_; lean_object* v___x_2829_; 
v_a_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2828_);
lean_dec_ref_known(v___x_2827_, 1);
lean_inc_ref(v_body_2826_);
v___x_2829_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_2826_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; uint8_t v___x_2837_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2830_);
lean_dec_ref_known(v___x_2829_, 1);
v___x_2831_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4));
v___x_2832_ = lean_box(0);
v___x_2833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2833_, 0, v_a_2830_);
lean_ctor_set(v___x_2833_, 1, v___x_2832_);
v___x_2834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2834_, 0, v_a_2828_);
lean_ctor_set(v___x_2834_, 1, v___x_2833_);
v___x_2835_ = l_Lean_mkConst(v___x_2831_, v___x_2834_);
lean_inc_ref(v_e_x27_2776_);
lean_inc_ref(v_struct_2305_);
v___x_2836_ = l_Lean_mkApp6(v___x_2835_, v_binderType_2825_, v_body_2826_, v_struct_2305_, v_e_x27_2776_, v___x_2788_, v_proof_2777_);
v___x_2837_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2305_, v_e_x27_2776_);
if (v___x_2837_ == 0)
{
lean_object* v___x_2838_; 
lean_inc(v_idx_2304_);
lean_inc(v_typeName_2303_);
lean_dec_ref_known(v_e_2278_, 3);
v___x_2838_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2303_, v_idx_2304_, v_e_x27_2776_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v_a_2839_; 
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_a_2839_);
lean_dec_ref_known(v___x_2838_, 1);
v___y_2641_ = v___x_2750_;
v___y_2642_ = v_contextDependent_2778_;
v___y_2643_ = v___x_2836_;
v___y_2644_ = v_a_2650_;
v_a_2645_ = v_a_2839_;
goto v___jp_2640_;
}
else
{
lean_object* v_a_2840_; 
lean_dec_ref(v___x_2836_);
v_a_2840_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_a_2840_);
lean_dec_ref_known(v___x_2838_, 1);
v___y_2617_ = v___x_2750_;
v___y_2618_ = v_a_2650_;
v_a_2619_ = v_a_2840_;
goto v___jp_2616_;
}
}
else
{
lean_dec_ref(v_e_x27_2776_);
v___y_2641_ = v___x_2750_;
v___y_2642_ = v_contextDependent_2778_;
v___y_2643_ = v___x_2836_;
v___y_2644_ = v_a_2650_;
v_a_2645_ = v_e_2278_;
goto v___jp_2640_;
}
}
else
{
lean_object* v_a_2841_; 
lean_dec(v_a_2828_);
lean_dec_ref(v_body_2826_);
lean_dec_ref(v_binderType_2825_);
lean_dec_ref(v___x_2788_);
lean_dec_ref(v_proof_2777_);
lean_dec_ref(v_e_x27_2776_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2841_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2841_);
lean_dec_ref_known(v___x_2829_, 1);
v___y_2617_ = v___x_2750_;
v___y_2618_ = v_a_2650_;
v_a_2619_ = v_a_2841_;
goto v___jp_2616_;
}
}
else
{
lean_object* v_a_2842_; 
lean_dec_ref(v_body_2826_);
lean_dec_ref(v_binderType_2825_);
lean_dec_ref(v___x_2788_);
lean_dec_ref(v_proof_2777_);
lean_dec_ref(v_e_x27_2776_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2842_ = lean_ctor_get(v___x_2827_, 0);
lean_inc(v_a_2842_);
lean_dec_ref_known(v___x_2827_, 1);
v___y_2617_ = v___x_2750_;
v___y_2618_ = v_a_2650_;
v_a_2619_ = v_a_2842_;
goto v___jp_2616_;
}
}
else
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
lean_dec(v_a_2790_);
lean_dec_ref(v___x_2788_);
lean_dec_ref(v_proof_2777_);
lean_dec_ref(v_e_x27_2776_);
lean_dec_ref_known(v_e_2278_, 3);
v___x_2843_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8);
v___x_2844_ = l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(v___x_2843_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_, v_a_2287_);
v___y_2635_ = v___x_2750_;
v___y_2636_ = v_a_2650_;
v___y_2637_ = v___x_2844_;
goto v___jp_2634_;
}
}
}
else
{
lean_object* v_a_2845_; 
lean_dec_ref(v___x_2788_);
lean_del_object(v___x_2780_);
lean_dec_ref(v_proof_2777_);
lean_dec_ref(v_e_x27_2776_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2845_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2845_);
lean_dec_ref_known(v___x_2789_, 1);
v___y_2617_ = v___x_2750_;
v___y_2618_ = v_a_2650_;
v_a_2619_ = v_a_2845_;
goto v___jp_2616_;
}
}
else
{
lean_object* v_a_2846_; 
lean_del_object(v___x_2780_);
lean_dec_ref(v_proof_2777_);
lean_dec_ref(v_e_x27_2776_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2846_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_a_2846_);
lean_dec_ref_known(v___x_2782_, 1);
v___y_2617_ = v___x_2750_;
v___y_2618_ = v_a_2650_;
v_a_2619_ = v_a_2846_;
goto v___jp_2616_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_2278_, 3);
v___y_2635_ = v___x_2750_;
v___y_2636_ = v_a_2650_;
v___y_2637_ = v___x_2751_;
goto v___jp_2634_;
}
}
}
}
v___jp_2306_:
{
if (lean_obj_tag(v_res_2307_) == 0)
{
uint8_t v_contextDependent_2317_; lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2375_; 
v_contextDependent_2317_ = lean_ctor_get_uint8(v_res_2307_, 1);
v_isSharedCheck_2375_ = !lean_is_exclusive(v_res_2307_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2319_ = v_res_2307_;
v_isShared_2320_ = v_isSharedCheck_2375_;
goto v_resetjp_2318_;
}
else
{
lean_dec(v_res_2307_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2375_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
uint8_t v___x_2321_; lean_object* v___x_2322_; lean_object* v___f_2323_; lean_object* v___x_2324_; 
v___x_2321_ = 1;
v___x_2322_ = lean_box(v___x_2321_);
v___f_2323_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2323_, 0, v___x_2322_);
lean_closure_set(v___f_2323_, 1, v_e_2278_);
v___x_2324_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2323_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2366_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2327_ = v___x_2324_;
v_isShared_2328_ = v_isSharedCheck_2366_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2324_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2366_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
if (lean_obj_tag(v_a_2325_) == 1)
{
lean_object* v_val_2329_; lean_object* v___x_2330_; 
lean_del_object(v___x_2327_);
lean_del_object(v___x_2319_);
v_val_2329_ = lean_ctor_get(v_a_2325_, 0);
lean_inc(v_val_2329_);
lean_dec_ref_known(v_a_2325_, 1);
v___x_2330_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2329_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v___x_2332_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc_n(v_a_2331_, 2);
lean_dec_ref_known(v___x_2330_, 1);
v___x_2332_ = l_Lean_Meta_Sym_mkEqRefl(v_a_2331_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2332_) == 0)
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2342_; 
v_a_2333_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2335_ = v___x_2332_;
v_isShared_2336_ = v_isSharedCheck_2342_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2332_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2342_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
uint8_t v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2340_; 
v___x_2337_ = 0;
v___x_2338_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2338_, 0, v_a_2331_);
lean_ctor_set(v___x_2338_, 1, v_a_2333_);
lean_ctor_set_uint8(v___x_2338_, sizeof(void*)*2, v_contextDependent_2317_);
lean_ctor_set_uint8(v___x_2338_, sizeof(void*)*2 + 1, v___x_2337_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 0, v___x_2338_);
v___x_2340_ = v___x_2335_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2338_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec(v_a_2331_);
v_a_2343_ = lean_ctor_get(v___x_2332_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2332_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2332_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2332_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
v_a_2351_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2330_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2330_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
}
else
{
uint8_t v___x_2359_; lean_object* v___x_2361_; 
lean_dec(v_a_2325_);
v___x_2359_ = 1;
if (v_isShared_2320_ == 0)
{
v___x_2361_ = v___x_2319_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v_reuseFailAlloc_2365_, 1, v_contextDependent_2317_);
v___x_2361_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
lean_object* v___x_2363_; 
lean_ctor_set_uint8(v___x_2361_, 0, v___x_2359_);
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 0, v___x_2361_);
v___x_2363_ = v___x_2327_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2361_);
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
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
lean_del_object(v___x_2319_);
v_a_2367_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2324_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2324_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
}
else
{
lean_object* v_e_x27_2376_; lean_object* v_proof_2377_; uint8_t v_contextDependent_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2546_; 
v_e_x27_2376_ = lean_ctor_get(v_res_2307_, 0);
v_proof_2377_ = lean_ctor_get(v_res_2307_, 1);
v_contextDependent_2378_ = lean_ctor_get_uint8(v_res_2307_, sizeof(void*)*2 + 1);
v_isSharedCheck_2546_ = !lean_is_exclusive(v_res_2307_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2380_ = v_res_2307_;
v_isShared_2381_ = v_isSharedCheck_2546_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_proof_2377_);
lean_inc(v_e_x27_2376_);
lean_dec(v_res_2307_);
v___x_2380_ = lean_box(0);
v_isShared_2381_ = v_isSharedCheck_2546_;
goto v_resetjp_2379_;
}
v_resetjp_2379_:
{
lean_object* v___x_2382_; 
lean_inc_ref(v_e_x27_2376_);
v___x_2382_ = l_Lean_Meta_Sym_inferType(v_e_x27_2376_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v_a_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
v_a_2383_ = lean_ctor_get(v___x_2382_, 0);
lean_inc(v_a_2383_);
lean_dec_ref_known(v___x_2382_, 1);
v___x_2384_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1));
v___x_2385_ = 0;
v___x_2386_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2);
lean_inc(v_idx_2304_);
lean_inc(v_typeName_2303_);
v___x_2387_ = l_Lean_Expr_proj___override(v_typeName_2303_, v_idx_2304_, v___x_2386_);
v___x_2388_ = l_Lean_mkLambda(v___x_2384_, v___x_2385_, v_a_2383_, v___x_2387_);
lean_inc_ref(v___x_2388_);
v___x_2389_ = l_Lean_Meta_Sym_inferType(v___x_2388_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; uint8_t v___x_2391_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc(v_a_2390_);
lean_dec_ref_known(v___x_2389_, 1);
v___x_2391_ = l_Lean_Expr_isArrow(v_a_2390_);
if (v___x_2391_ == 0)
{
uint8_t v___x_2392_; lean_object* v___x_2393_; lean_object* v___f_2394_; lean_object* v___x_2395_; 
lean_dec(v_a_2390_);
v___x_2392_ = 1;
v___x_2393_ = lean_box(v___x_2392_);
lean_inc_ref(v_e_2278_);
v___f_2394_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2394_, 0, v___x_2393_);
lean_closure_set(v___f_2394_, 1, v_e_2278_);
v___x_2395_ = l_Lean_Meta_Tactic_Cbv_withCbvOpaqueGuard___redArg(v___f_2394_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2395_) == 0)
{
lean_object* v_a_2396_; 
v_a_2396_ = lean_ctor_get(v___x_2395_, 0);
lean_inc(v_a_2396_);
lean_dec_ref_known(v___x_2395_, 1);
if (lean_obj_tag(v_a_2396_) == 0)
{
lean_object* v___x_2397_; 
lean_del_object(v___x_2380_);
lean_inc_ref(v_e_x27_2376_);
lean_inc_ref(v_struct_2305_);
v___x_2397_ = l_Lean_Meta_Sym_isDefEqI___redArg(v_struct_2305_, v_e_x27_2376_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2397_) == 0)
{
lean_object* v_a_2398_; lean_object* v___x_2400_; uint8_t v_isShared_2401_; uint8_t v_isSharedCheck_2441_; 
v_a_2398_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2400_ = v___x_2397_;
v_isShared_2401_ = v_isSharedCheck_2441_;
goto v_resetjp_2399_;
}
else
{
lean_inc(v_a_2398_);
lean_dec(v___x_2397_);
v___x_2400_ = lean_box(0);
v_isShared_2401_ = v_isSharedCheck_2441_;
goto v_resetjp_2399_;
}
v_resetjp_2399_:
{
uint8_t v___x_2402_; 
v___x_2402_ = lean_unbox(v_a_2398_);
lean_dec(v_a_2398_);
if (v___x_2402_ == 0)
{
uint8_t v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2406_; 
lean_dec_ref(v___x_2388_);
lean_dec_ref(v_proof_2377_);
lean_dec_ref(v_e_x27_2376_);
lean_dec_ref_known(v_e_2278_, 3);
v___x_2403_ = 1;
v___x_2404_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_2404_, 0, v___x_2403_);
lean_ctor_set_uint8(v___x_2404_, 1, v_contextDependent_2378_);
if (v_isShared_2401_ == 0)
{
lean_ctor_set(v___x_2400_, 0, v___x_2404_);
v___x_2406_ = v___x_2400_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2404_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
else
{
lean_object* v___x_2408_; 
lean_del_object(v___x_2400_);
v___x_2408_ = l_Lean_Meta_mkHCongr(v___x_2388_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2408_) == 0)
{
lean_object* v_a_2409_; lean_object* v_proof_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; 
v_a_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc(v_a_2409_);
lean_dec_ref_known(v___x_2408_, 1);
v_proof_2410_ = lean_ctor_get(v_a_2409_, 1);
lean_inc_ref(v_proof_2410_);
lean_dec(v_a_2409_);
lean_inc_ref(v_e_x27_2376_);
lean_inc_ref(v_struct_2305_);
v___x_2411_ = l_Lean_mkApp3(v_proof_2410_, v_struct_2305_, v_e_x27_2376_, v_proof_2377_);
v___x_2412_ = l_Lean_Meta_mkEqOfHEq(v___x_2411_, v___x_2391_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_object* v_a_2413_; uint8_t v___x_2414_; 
v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_a_2413_);
lean_dec_ref_known(v___x_2412_, 1);
v___x_2414_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2305_, v_e_x27_2376_);
if (v___x_2414_ == 0)
{
lean_object* v___x_2415_; 
lean_inc(v_idx_2304_);
lean_inc(v_typeName_2303_);
lean_dec_ref_known(v_e_2278_, 3);
v___x_2415_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2303_, v_idx_2304_, v_e_x27_2376_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_a_2416_);
lean_dec_ref_known(v___x_2415_, 1);
v___y_2290_ = v_a_2413_;
v___y_2291_ = v___x_2391_;
v___y_2292_ = v_contextDependent_2378_;
v_a_2293_ = v_a_2416_;
goto v___jp_2289_;
}
else
{
lean_object* v_a_2417_; lean_object* v___x_2419_; uint8_t v_isShared_2420_; uint8_t v_isSharedCheck_2424_; 
lean_dec(v_a_2413_);
v_a_2417_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2424_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2424_ == 0)
{
v___x_2419_ = v___x_2415_;
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
else
{
lean_inc(v_a_2417_);
lean_dec(v___x_2415_);
v___x_2419_ = lean_box(0);
v_isShared_2420_ = v_isSharedCheck_2424_;
goto v_resetjp_2418_;
}
v_resetjp_2418_:
{
lean_object* v___x_2422_; 
if (v_isShared_2420_ == 0)
{
v___x_2422_ = v___x_2419_;
goto v_reusejp_2421_;
}
else
{
lean_object* v_reuseFailAlloc_2423_; 
v_reuseFailAlloc_2423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2423_, 0, v_a_2417_);
v___x_2422_ = v_reuseFailAlloc_2423_;
goto v_reusejp_2421_;
}
v_reusejp_2421_:
{
return v___x_2422_;
}
}
}
}
else
{
lean_dec_ref(v_e_x27_2376_);
v___y_2290_ = v_a_2413_;
v___y_2291_ = v___x_2391_;
v___y_2292_ = v_contextDependent_2378_;
v_a_2293_ = v_e_2278_;
goto v___jp_2289_;
}
}
else
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2432_; 
lean_dec_ref(v_e_x27_2376_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2425_ = lean_ctor_get(v___x_2412_, 0);
v_isSharedCheck_2432_ = !lean_is_exclusive(v___x_2412_);
if (v_isSharedCheck_2432_ == 0)
{
v___x_2427_ = v___x_2412_;
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2412_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2432_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
lean_object* v___x_2430_; 
if (v_isShared_2428_ == 0)
{
v___x_2430_ = v___x_2427_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v_a_2425_);
v___x_2430_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
return v___x_2430_;
}
}
}
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_dec_ref(v_proof_2377_);
lean_dec_ref(v_e_x27_2376_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2433_ = lean_ctor_get(v___x_2408_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2408_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2408_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2408_);
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
}
}
else
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2449_; 
lean_dec_ref(v___x_2388_);
lean_dec_ref(v_proof_2377_);
lean_dec_ref(v_e_x27_2376_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2442_ = lean_ctor_get(v___x_2397_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2397_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2444_ = v___x_2397_;
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2397_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2447_; 
if (v_isShared_2445_ == 0)
{
v___x_2447_ = v___x_2444_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_a_2442_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
else
{
lean_object* v_val_2450_; lean_object* v___x_2451_; 
lean_dec_ref(v___x_2388_);
lean_dec_ref(v_proof_2377_);
lean_dec_ref(v_e_x27_2376_);
lean_dec_ref_known(v_e_2278_, 3);
v_val_2450_ = lean_ctor_get(v_a_2396_, 0);
lean_inc(v_val_2450_);
lean_dec_ref_known(v_a_2396_, 1);
v___x_2451_ = l_Lean_Meta_Sym_shareCommonInc(v_val_2450_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; lean_object* v___x_2453_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
lean_inc_n(v_a_2452_, 2);
lean_dec_ref_known(v___x_2451_, 1);
v___x_2453_ = l_Lean_Meta_Sym_mkEqRefl(v_a_2452_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2464_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2456_ = v___x_2453_;
v_isShared_2457_ = v_isSharedCheck_2464_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_a_2454_);
lean_dec(v___x_2453_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2464_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2459_; 
if (v_isShared_2381_ == 0)
{
lean_ctor_set(v___x_2380_, 1, v_a_2454_);
lean_ctor_set(v___x_2380_, 0, v_a_2452_);
v___x_2459_ = v___x_2380_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2452_);
lean_ctor_set(v_reuseFailAlloc_2463_, 1, v_a_2454_);
v___x_2459_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
lean_object* v___x_2461_; 
lean_ctor_set_uint8(v___x_2459_, sizeof(void*)*2, v_contextDependent_2378_);
lean_ctor_set_uint8(v___x_2459_, sizeof(void*)*2 + 1, v___x_2391_);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 0, v___x_2459_);
v___x_2461_ = v___x_2456_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2459_);
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
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec(v_a_2452_);
lean_del_object(v___x_2380_);
v_a_2465_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2453_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2453_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
lean_del_object(v___x_2380_);
v_a_2473_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2475_ = v___x_2451_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2451_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2473_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec_ref(v___x_2388_);
lean_del_object(v___x_2380_);
lean_dec_ref(v_proof_2377_);
lean_dec_ref(v_e_x27_2376_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2481_ = lean_ctor_get(v___x_2395_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2395_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2395_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2395_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
else
{
lean_del_object(v___x_2380_);
if (lean_obj_tag(v_a_2390_) == 7)
{
lean_object* v_binderType_2489_; lean_object* v_body_2490_; lean_object* v___x_2491_; 
v_binderType_2489_ = lean_ctor_get(v_a_2390_, 1);
lean_inc_ref_n(v_binderType_2489_, 2);
v_body_2490_ = lean_ctor_get(v_a_2390_, 2);
lean_inc_ref(v_body_2490_);
lean_dec_ref_known(v_a_2390_, 3);
v___x_2491_ = l_Lean_Meta_Sym_getLevel___redArg(v_binderType_2489_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v_a_2492_; lean_object* v___x_2493_; 
v_a_2492_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_a_2492_);
lean_dec_ref_known(v___x_2491_, 1);
lean_inc_ref(v_body_2490_);
v___x_2493_ = l_Lean_Meta_Sym_getLevel___redArg(v_body_2490_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2493_) == 0)
{
lean_object* v_a_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; uint8_t v___x_2501_; 
v_a_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_a_2494_);
lean_dec_ref_known(v___x_2493_, 1);
v___x_2495_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4));
v___x_2496_ = lean_box(0);
v___x_2497_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2497_, 0, v_a_2494_);
lean_ctor_set(v___x_2497_, 1, v___x_2496_);
v___x_2498_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2498_, 0, v_a_2492_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
v___x_2499_ = l_Lean_mkConst(v___x_2495_, v___x_2498_);
lean_inc_ref(v_e_x27_2376_);
lean_inc_ref(v_struct_2305_);
v___x_2500_ = l_Lean_mkApp6(v___x_2499_, v_binderType_2489_, v_body_2490_, v_struct_2305_, v_e_x27_2376_, v___x_2388_, v_proof_2377_);
v___x_2501_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_struct_2305_, v_e_x27_2376_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2502_; 
lean_inc(v_idx_2304_);
lean_inc(v_typeName_2303_);
lean_dec_ref_known(v_e_2278_, 3);
v___x_2502_ = l_Lean_Meta_Sym_Internal_mkProjS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__0___redArg(v_typeName_2303_, v_idx_2304_, v_e_x27_2376_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v_a_2503_; 
v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
lean_inc(v_a_2503_);
lean_dec_ref_known(v___x_2502_, 1);
v___y_2297_ = v___x_2500_;
v___y_2298_ = v_contextDependent_2378_;
v_a_2299_ = v_a_2503_;
goto v___jp_2296_;
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
lean_dec_ref(v___x_2500_);
v_a_2504_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2502_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2502_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2509_; 
if (v_isShared_2507_ == 0)
{
v___x_2509_ = v___x_2506_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2504_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
else
{
lean_dec_ref(v_e_x27_2376_);
v___y_2297_ = v___x_2500_;
v___y_2298_ = v_contextDependent_2378_;
v_a_2299_ = v_e_2278_;
goto v___jp_2296_;
}
}
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
lean_dec(v_a_2492_);
lean_dec_ref(v_body_2490_);
lean_dec_ref(v_binderType_2489_);
lean_dec_ref(v___x_2388_);
lean_dec_ref(v_proof_2377_);
lean_dec_ref(v_e_x27_2376_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2512_ = lean_ctor_get(v___x_2493_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2493_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2514_ = v___x_2493_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2493_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2517_; 
if (v_isShared_2515_ == 0)
{
v___x_2517_ = v___x_2514_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2512_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
lean_dec_ref(v_body_2490_);
lean_dec_ref(v_binderType_2489_);
lean_dec_ref(v___x_2388_);
lean_dec_ref(v_proof_2377_);
lean_dec_ref(v_e_x27_2376_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2520_ = lean_ctor_get(v___x_2491_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2491_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2491_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_a_2520_);
lean_dec(v___x_2491_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_a_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
else
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
lean_dec(v_a_2390_);
lean_dec_ref(v___x_2388_);
lean_dec_ref(v_proof_2377_);
lean_dec_ref(v_e_x27_2376_);
lean_dec_ref_known(v_e_2278_, 3);
v___x_2528_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__8);
v___x_2529_ = l_panic___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__1(v___x_2528_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
return v___x_2529_;
}
}
}
else
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2537_; 
lean_dec_ref(v___x_2388_);
lean_del_object(v___x_2380_);
lean_dec_ref(v_proof_2377_);
lean_dec_ref(v_e_x27_2376_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2530_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2532_ = v___x_2389_;
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2389_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2530_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_del_object(v___x_2380_);
lean_dec_ref(v_proof_2377_);
lean_dec_ref(v_e_x27_2376_);
lean_dec_ref_known(v_e_2278_, 3);
v_a_2538_ = lean_ctor_get(v___x_2382_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2382_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2382_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2382_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
lean_dec_ref(v_e_2278_);
v___x_2852_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2853_, 0, v___x_2852_);
return v___x_2853_;
}
v___jp_2289_:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; 
v___x_2294_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2294_, 0, v_a_2293_);
lean_ctor_set(v___x_2294_, 1, v___y_2290_);
lean_ctor_set_uint8(v___x_2294_, sizeof(void*)*2, v___y_2292_);
lean_ctor_set_uint8(v___x_2294_, sizeof(void*)*2 + 1, v___y_2291_);
v___x_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
return v___x_2295_;
}
v___jp_2296_:
{
uint8_t v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2300_ = 0;
v___x_2301_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_2301_, 0, v_a_2299_);
lean_ctor_set(v___x_2301_, 1, v___y_2297_);
lean_ctor_set_uint8(v___x_2301_, sizeof(void*)*2, v___y_2298_);
lean_ctor_set_uint8(v___x_2301_, sizeof(void*)*2 + 1, v___x_2300_);
v___x_2302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2301_);
return v___x_2302_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___boxed(lean_object* v_e_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(v_e_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_, v_a_2863_);
lean_dec(v_a_2863_);
lean_dec_ref(v_a_2862_);
lean_dec(v_a_2861_);
lean_dec_ref(v_a_2860_);
lean_dec(v_a_2859_);
lean_dec_ref(v_a_2858_);
lean_dec(v_a_2857_);
lean_dec_ref(v_a_2856_);
lean_dec(v_a_2855_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5(lean_object* v_00_u03b1_2866_, lean_object* v_x_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_, lean_object* v___y_2876_){
_start:
{
lean_object* v___x_2878_; 
v___x_2878_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___redArg(v_x_2867_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5___boxed(lean_object* v_00_u03b1_2879_, lean_object* v_x_2880_, lean_object* v___y_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__5(v_00_u03b1_2879_, v_x_2880_, v___y_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
lean_dec(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
lean_dec(v___y_2881_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4(lean_object* v_oldTraces_2892_, lean_object* v_data_2893_, lean_object* v_ref_2894_, lean_object* v_msg_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_){
_start:
{
lean_object* v___x_2906_; 
v___x_2906_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___redArg(v_oldTraces_2892_, v_data_2893_, v_ref_2894_, v_msg_2895_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4___boxed(lean_object* v_oldTraces_2907_, lean_object* v_data_2908_, lean_object* v_ref_2909_, lean_object* v_msg_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4(v_oldTraces_2907_, v_data_2908_, v_ref_2909_, v_msg_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg(lean_object* v_f_2922_, lean_object* v_a_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v___y_2932_; lean_object* v___x_2935_; uint8_t v_debug_2936_; 
v___x_2935_ = lean_st_ref_get(v___y_2925_);
v_debug_2936_ = lean_ctor_get_uint8(v___x_2935_, sizeof(void*)*10);
lean_dec(v___x_2935_);
if (v_debug_2936_ == 0)
{
v___y_2932_ = v___y_2925_;
goto v___jp_2931_;
}
else
{
lean_object* v___x_2937_; 
lean_inc_ref(v_f_2922_);
v___x_2937_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_f_2922_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v___x_2938_; 
lean_dec_ref_known(v___x_2937_, 1);
lean_inc_ref(v_a_2923_);
v___x_2938_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(v_a_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_dec_ref_known(v___x_2938_, 1);
v___y_2932_ = v___y_2925_;
goto v___jp_2931_;
}
else
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
lean_dec_ref(v_a_2923_);
lean_dec_ref(v_f_2922_);
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___x_2938_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2938_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
else
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
lean_dec_ref(v_a_2923_);
lean_dec_ref(v_f_2922_);
v_a_2947_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___x_2937_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2937_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
}
v___jp_2931_:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = l_Lean_Expr_app___override(v_f_2922_, v_a_2923_);
v___x_2934_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_2933_, v___y_2932_);
return v___x_2934_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_f_2955_, lean_object* v_a_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg(v_f_2955_, v_a_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_, v___y_2962_);
lean_dec(v___y_2962_);
lean_dec_ref(v___y_2961_);
lean_dec(v___y_2960_);
lean_dec_ref(v___y_2959_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0(lean_object* v_args_2965_, lean_object* v_endIdx_2966_, lean_object* v_b_2967_, lean_object* v_i_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_){
_start:
{
uint8_t v___x_2979_; 
v___x_2979_ = lean_nat_dec_le(v_endIdx_2966_, v_i_2968_);
if (v___x_2979_ == 0)
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v___x_2980_ = l_Lean_instInhabitedExpr;
v___x_2981_ = lean_array_get_borrowed(v___x_2980_, v_args_2965_, v_i_2968_);
lean_inc(v___x_2981_);
v___x_2982_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg(v_b_2967_, v___x_2981_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref_known(v___x_2982_, 1);
v___x_2984_ = lean_unsigned_to_nat(1u);
v___x_2985_ = lean_nat_add(v_i_2968_, v___x_2984_);
lean_dec(v_i_2968_);
v_b_2967_ = v_a_2983_;
v_i_2968_ = v___x_2985_;
goto _start;
}
else
{
lean_dec(v_i_2968_);
return v___x_2982_;
}
}
else
{
lean_object* v___x_2987_; 
lean_dec(v_i_2968_);
v___x_2987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2987_, 0, v_b_2967_);
return v___x_2987_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0___boxed(lean_object* v_args_2988_, lean_object* v_endIdx_2989_, lean_object* v_b_2990_, lean_object* v_i_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_, lean_object* v___y_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_){
_start:
{
lean_object* v_res_3002_; 
v_res_3002_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0(v_args_2988_, v_endIdx_2989_, v_b_2990_, v_i_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_, v___y_3000_);
lean_dec(v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec(v___y_2998_);
lean_dec_ref(v___y_2997_);
lean_dec(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v___y_2992_);
lean_dec(v_endIdx_2989_);
lean_dec_ref(v_args_2988_);
return v_res_3002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0(lean_object* v_f_3003_, lean_object* v_args_3004_, lean_object* v___y_3005_, lean_object* v___y_3006_, lean_object* v___y_3007_, lean_object* v___y_3008_, lean_object* v___y_3009_, lean_object* v___y_3010_, lean_object* v___y_3011_, lean_object* v___y_3012_, lean_object* v___y_3013_){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3015_ = lean_unsigned_to_nat(0u);
v___x_3016_ = lean_array_get_size(v_args_3004_);
v___x_3017_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0(v_args_3004_, v___x_3016_, v_f_3003_, v___x_3015_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0___boxed(lean_object* v_f_3018_, lean_object* v_args_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_){
_start:
{
lean_object* v_res_3030_; 
v_res_3030_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0(v_f_3018_, v_args_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_, v___y_3028_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v___y_3022_);
lean_dec_ref(v___y_3021_);
lean_dec(v___y_3020_);
lean_dec_ref(v_args_3019_);
return v_res_3030_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0(void){
_start:
{
lean_object* v___x_3031_; lean_object* v_dummy_3032_; 
v___x_3031_ = lean_box(0);
v_dummy_3032_ = l_Lean_Expr_sort___override(v___x_3031_);
return v_dummy_3032_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2(void){
_start:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3034_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__1));
v___x_3035_ = l_Lean_stringToMessageData(v___x_3034_);
return v___x_3035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(lean_object* v_e_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_, lean_object* v_a_3044_, lean_object* v_a_3045_){
_start:
{
uint8_t v___x_3050_; 
v___x_3050_ = l_Lean_Expr_isApp(v_e_3036_);
if (v___x_3050_ == 0)
{
lean_object* v___x_3051_; lean_object* v___x_3052_; 
lean_dec_ref(v_e_3036_);
v___x_3051_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3051_, 0, v___x_3050_);
lean_ctor_set_uint8(v___x_3051_, 1, v___x_3050_);
v___x_3052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3051_);
return v___x_3052_;
}
else
{
lean_object* v_fn_3053_; uint8_t v___x_3054_; 
v_fn_3053_ = l_Lean_Expr_getAppFn(v_e_3036_);
v___x_3054_ = l_Lean_Expr_isLambda(v_fn_3053_);
if (v___x_3054_ == 0)
{
uint8_t v___x_3055_; 
v___x_3055_ = l_Lean_Expr_isConst(v_fn_3053_);
if (v___x_3055_ == 0)
{
lean_object* v___x_3056_; 
lean_inc(v_a_3045_);
lean_inc_ref(v_a_3044_);
lean_inc(v_a_3043_);
lean_inc_ref(v_a_3042_);
lean_inc(v_a_3041_);
lean_inc_ref(v_a_3040_);
lean_inc(v_a_3039_);
lean_inc_ref(v_a_3038_);
lean_inc(v_a_3037_);
lean_inc_ref(v_fn_3053_);
v___x_3056_ = lean_sym_simp(v_fn_3053_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_a_3057_; 
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_a_3057_);
if (lean_obj_tag(v_a_3057_) == 0)
{
lean_dec_ref_known(v_a_3057_, 0);
lean_dec_ref(v_fn_3053_);
lean_dec_ref(v_e_3036_);
return v___x_3056_;
}
else
{
lean_object* v_e_x27_3058_; lean_object* v_proof_3059_; uint8_t v_contextDependent_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3164_; 
lean_dec_ref_known(v___x_3056_, 1);
v_e_x27_3058_ = lean_ctor_get(v_a_3057_, 0);
v_proof_3059_ = lean_ctor_get(v_a_3057_, 1);
v_contextDependent_3060_ = lean_ctor_get_uint8(v_a_3057_, sizeof(void*)*2 + 1);
v_isSharedCheck_3164_ = !lean_is_exclusive(v_a_3057_);
if (v_isSharedCheck_3164_ == 0)
{
v___x_3062_ = v_a_3057_;
v_isShared_3063_ = v_isSharedCheck_3164_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_proof_3059_);
lean_inc(v_e_x27_3058_);
lean_dec(v_a_3057_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3164_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3064_; 
lean_inc_ref(v_e_x27_3058_);
v___x_3064_ = l_Lean_Meta_Sym_inferType(v_e_x27_3058_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v_a_3065_; lean_object* v___x_3066_; lean_object* v_dummy_3067_; lean_object* v_nargs_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_a_3065_);
lean_dec_ref_known(v___x_3064_, 1);
v___x_3066_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__2);
v_dummy_3067_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__0);
v_nargs_3068_ = l_Lean_Expr_getAppNumArgs(v_e_3036_);
lean_inc(v_nargs_3068_);
v___x_3069_ = lean_mk_array(v_nargs_3068_, v_dummy_3067_);
v___x_3070_ = lean_unsigned_to_nat(1u);
v___x_3071_ = lean_nat_sub(v_nargs_3068_, v___x_3070_);
lean_dec(v_nargs_3068_);
lean_inc_ref(v_e_3036_);
v___x_3072_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3036_, v___x_3069_, v___x_3071_);
v___x_3073_ = l_Lean_mkAppN(v___x_3066_, v___x_3072_);
lean_inc_ref(v_e_x27_3058_);
v___x_3074_ = l_Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0(v_e_x27_3058_, v___x_3072_, v_a_3037_, v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_);
lean_dec_ref(v___x_3072_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v_a_3075_; lean_object* v___x_3076_; 
v_a_3075_ = lean_ctor_get(v___x_3074_, 0);
lean_inc(v_a_3075_);
lean_dec_ref_known(v___x_3074_, 1);
lean_inc_ref(v_e_3036_);
v___x_3076_ = l_Lean_Meta_Sym_inferType(v_e_3036_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v_a_3077_; lean_object* v___x_3078_; uint8_t v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; 
v_a_3077_ = lean_ctor_get(v___x_3076_, 0);
lean_inc(v_a_3077_);
lean_dec_ref_known(v___x_3076_, 1);
v___x_3078_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__1));
v___x_3079_ = 0;
lean_inc_n(v_a_3065_, 2);
v___x_3080_ = l_Lean_mkLambda(v___x_3078_, v___x_3079_, v_a_3065_, v___x_3073_);
v___x_3081_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_3065_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v_a_3082_; lean_object* v___x_3083_; 
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
lean_inc(v_a_3082_);
lean_dec_ref_known(v___x_3081_, 1);
lean_inc(v_a_3077_);
v___x_3083_ = l_Lean_Meta_Sym_getLevel___redArg(v_a_3077_, v_a_3041_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_);
if (lean_obj_tag(v___x_3083_) == 0)
{
lean_object* v_options_3084_; lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3123_; 
v_options_3084_ = lean_ctor_get(v_a_3044_, 2);
v_a_3085_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3087_ = v___x_3083_;
v_isShared_3088_ = v_isSharedCheck_3123_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3083_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3123_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v_inheritedTraceOptions_3089_; uint8_t v_hasTrace_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; 
v_inheritedTraceOptions_3089_ = lean_ctor_get(v_a_3044_, 13);
v_hasTrace_3090_ = lean_ctor_get_uint8(v_options_3084_, sizeof(void*)*1);
v___x_3091_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__4));
v___x_3092_ = lean_box(0);
v___x_3093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3093_, 0, v_a_3085_);
lean_ctor_set(v___x_3093_, 1, v___x_3092_);
v___x_3094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3094_, 0, v_a_3082_);
lean_ctor_set(v___x_3094_, 1, v___x_3093_);
v___x_3095_ = l_Lean_mkConst(v___x_3091_, v___x_3094_);
v___x_3096_ = l_Lean_mkApp6(v___x_3095_, v_a_3065_, v_a_3077_, v_fn_3053_, v_e_x27_3058_, v___x_3080_, v_proof_3059_);
if (v_hasTrace_3090_ == 0)
{
lean_dec_ref(v_e_3036_);
goto v___jp_3097_;
}
else
{
lean_object* v___x_3104_; lean_object* v___x_3105_; uint8_t v___x_3106_; 
v___x_3104_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__2));
v___x_3105_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_betaReduce___redArg___closed__3);
v___x_3106_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3089_, v_options_3084_, v___x_3105_);
if (v___x_3106_ == 0)
{
lean_dec_ref(v_e_3036_);
goto v___jp_3097_;
}
else
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3107_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___closed__2);
v___x_3108_ = l_Lean_indentExpr(v_e_3036_);
v___x_3109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3107_);
lean_ctor_set(v___x_3109_, 1, v___x_3108_);
v___x_3110_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_3111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3111_, 0, v___x_3109_);
lean_ctor_set(v___x_3111_, 1, v___x_3110_);
lean_inc(v_a_3075_);
v___x_3112_ = l_Lean_indentExpr(v_a_3075_);
v___x_3113_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3111_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v___x_3114_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_3104_, v___x_3113_, v_a_3042_, v_a_3043_, v_a_3044_, v_a_3045_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_dec_ref_known(v___x_3114_, 1);
goto v___jp_3097_;
}
else
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3122_; 
lean_dec_ref(v___x_3096_);
lean_del_object(v___x_3087_);
lean_dec(v_a_3075_);
lean_del_object(v___x_3062_);
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3117_ = v___x_3114_;
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3114_);
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
}
v___jp_3097_:
{
lean_object* v___x_3099_; 
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 1, v___x_3096_);
lean_ctor_set(v___x_3062_, 0, v_a_3075_);
v___x_3099_ = v___x_3062_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3075_);
lean_ctor_set(v_reuseFailAlloc_3103_, 1, v___x_3096_);
v___x_3099_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
lean_object* v___x_3101_; 
lean_ctor_set_uint8(v___x_3099_, sizeof(void*)*2, v_contextDependent_3060_);
lean_ctor_set_uint8(v___x_3099_, sizeof(void*)*2 + 1, v___x_3055_);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 0, v___x_3099_);
v___x_3101_ = v___x_3087_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3099_);
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
}
else
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3131_; 
lean_dec(v_a_3082_);
lean_dec_ref(v___x_3080_);
lean_dec(v_a_3077_);
lean_dec(v_a_3075_);
lean_dec(v_a_3065_);
lean_del_object(v___x_3062_);
lean_dec_ref(v_proof_3059_);
lean_dec_ref(v_e_x27_3058_);
lean_dec_ref(v_fn_3053_);
lean_dec_ref(v_e_3036_);
v_a_3124_ = lean_ctor_get(v___x_3083_, 0);
v_isSharedCheck_3131_ = !lean_is_exclusive(v___x_3083_);
if (v_isSharedCheck_3131_ == 0)
{
v___x_3126_ = v___x_3083_;
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3083_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3131_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3129_; 
if (v_isShared_3127_ == 0)
{
v___x_3129_ = v___x_3126_;
goto v_reusejp_3128_;
}
else
{
lean_object* v_reuseFailAlloc_3130_; 
v_reuseFailAlloc_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3130_, 0, v_a_3124_);
v___x_3129_ = v_reuseFailAlloc_3130_;
goto v_reusejp_3128_;
}
v_reusejp_3128_:
{
return v___x_3129_;
}
}
}
}
else
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3139_; 
lean_dec_ref(v___x_3080_);
lean_dec(v_a_3077_);
lean_dec(v_a_3075_);
lean_dec(v_a_3065_);
lean_del_object(v___x_3062_);
lean_dec_ref(v_proof_3059_);
lean_dec_ref(v_e_x27_3058_);
lean_dec_ref(v_fn_3053_);
lean_dec_ref(v_e_3036_);
v_a_3132_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3134_ = v___x_3081_;
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3081_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3139_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3137_; 
if (v_isShared_3135_ == 0)
{
v___x_3137_ = v___x_3134_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v_a_3132_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
}
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
lean_dec(v_a_3075_);
lean_dec_ref(v___x_3073_);
lean_dec(v_a_3065_);
lean_del_object(v___x_3062_);
lean_dec_ref(v_proof_3059_);
lean_dec_ref(v_e_x27_3058_);
lean_dec_ref(v_fn_3053_);
lean_dec_ref(v_e_3036_);
v_a_3140_ = lean_ctor_get(v___x_3076_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3076_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3076_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
lean_dec_ref(v___x_3073_);
lean_dec(v_a_3065_);
lean_del_object(v___x_3062_);
lean_dec_ref(v_proof_3059_);
lean_dec_ref(v_e_x27_3058_);
lean_dec_ref(v_fn_3053_);
lean_dec_ref(v_e_3036_);
v_a_3148_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3074_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3074_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_del_object(v___x_3062_);
lean_dec_ref(v_proof_3059_);
lean_dec_ref(v_e_x27_3058_);
lean_dec_ref(v_fn_3053_);
lean_dec_ref(v_e_3036_);
v_a_3156_ = lean_ctor_get(v___x_3064_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3064_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3064_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_fn_3053_);
lean_dec_ref(v_e_3036_);
return v___x_3056_;
}
}
else
{
lean_dec_ref(v_fn_3053_);
lean_dec_ref(v_e_3036_);
goto v___jp_3047_;
}
}
else
{
lean_dec_ref(v_fn_3053_);
lean_dec_ref(v_e_3036_);
goto v___jp_3047_;
}
}
v___jp_3047_:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3048_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
return v___x_3049_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn___boxed(lean_object* v_e_3165_, lean_object* v_a_3166_, lean_object* v_a_3167_, lean_object* v_a_3168_, lean_object* v_a_3169_, lean_object* v_a_3170_, lean_object* v_a_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_){
_start:
{
lean_object* v_res_3176_; 
v_res_3176_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(v_e_3165_, v_a_3166_, v_a_3167_, v_a_3168_, v_a_3169_, v_a_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_);
lean_dec(v_a_3174_);
lean_dec_ref(v_a_3173_);
lean_dec(v_a_3172_);
lean_dec_ref(v_a_3171_);
lean_dec(v_a_3170_);
lean_dec_ref(v_a_3169_);
lean_dec(v_a_3168_);
lean_dec_ref(v_a_3167_);
lean_dec(v_a_3166_);
return v_res_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1(lean_object* v_f_3177_, lean_object* v_a_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
lean_object* v___x_3189_; 
v___x_3189_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___redArg(v_f_3177_, v_a_3178_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1___boxed(lean_object* v_f_3190_, lean_object* v_a_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
lean_object* v_res_3202_; 
v_res_3202_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___at___00Lean_Meta_Sym_Internal_mkAppNS___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn_spec__0_spec__0_spec__1(v_f_3190_, v_a_3191_, v___y_3192_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
lean_dec(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec(v___y_3192_);
return v_res_3202_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1(void){
_start:
{
lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3204_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__0));
v___x_3205_ = l_Lean_stringToMessageData(v___x_3204_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(lean_object* v_e_3206_, lean_object* v_a_3207_, lean_object* v_a_3208_, lean_object* v_a_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_){
_start:
{
if (lean_obj_tag(v_e_3206_) == 4)
{
lean_object* v_declName_3217_; lean_object* v_us_3218_; lean_object* v___x_3219_; 
v_declName_3217_ = lean_ctor_get(v_e_3206_, 0);
v_us_3218_ = lean_ctor_get(v_e_3206_, 1);
lean_inc(v_declName_3217_);
v___x_3219_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp_spec__0(v_declName_3217_, v_a_3207_, v_a_3208_, v_a_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3347_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3222_ = v___x_3219_;
v_isShared_3223_ = v_isSharedCheck_3347_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_3219_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3347_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
uint8_t v___x_3224_; 
v___x_3224_ = l_Lean_ConstantInfo_isDefinition(v_a_3220_);
if (v___x_3224_ == 0)
{
lean_object* v___x_3225_; lean_object* v___x_3227_; 
lean_dec(v_a_3220_);
lean_dec_ref_known(v_e_3206_, 2);
v___x_3225_ = lean_alloc_ctor(0, 0, 2);
lean_ctor_set_uint8(v___x_3225_, 0, v___x_3224_);
lean_ctor_set_uint8(v___x_3225_, 1, v___x_3224_);
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 0, v___x_3225_);
v___x_3227_ = v___x_3222_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3228_; 
v_reuseFailAlloc_3228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3228_, 0, v___x_3225_);
v___x_3227_ = v_reuseFailAlloc_3228_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
return v___x_3227_;
}
}
else
{
lean_object* v___x_3229_; 
v___x_3229_ = l_Lean_ConstantInfo_type(v_a_3220_);
if (lean_obj_tag(v___x_3229_) == 7)
{
lean_object* v___x_3230_; lean_object* v___x_3232_; 
lean_dec_ref_known(v___x_3229_, 3);
lean_dec(v_a_3220_);
lean_dec_ref_known(v_e_3206_, 2);
v___x_3230_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 0, v___x_3230_);
v___x_3232_ = v___x_3222_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v___x_3230_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
else
{
lean_object* v___x_3234_; 
v___x_3234_ = l_Lean_Meta_whnfD(v___x_3229_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_);
if (lean_obj_tag(v___x_3234_) == 0)
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3338_; 
v_a_3235_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3237_ = v___x_3234_;
v_isShared_3238_ = v_isSharedCheck_3338_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3234_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3338_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
uint8_t v___x_3239_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; uint8_t v___y_3267_; 
v___x_3239_ = 0;
if (lean_obj_tag(v_a_3235_) == 7)
{
lean_object* v___x_3329_; lean_object* v___x_3331_; 
lean_dec_ref_known(v_a_3235_, 3);
lean_del_object(v___x_3237_);
lean_dec(v_a_3220_);
lean_dec_ref_known(v_e_3206_, 2);
v___x_3329_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 0, v___x_3329_);
v___x_3331_ = v___x_3222_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v___x_3329_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
else
{
uint8_t v___x_3333_; 
lean_dec(v_a_3235_);
lean_del_object(v___x_3222_);
v___x_3333_ = l_Lean_ConstantInfo_hasValue(v_a_3220_, v___x_3239_);
if (v___x_3333_ == 0)
{
v___y_3267_ = v___x_3333_;
goto v___jp_3266_;
}
else
{
lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; uint8_t v___x_3337_; 
v___x_3334_ = l_Lean_ConstantInfo_levelParams(v_a_3220_);
v___x_3335_ = l_List_lengthTR___redArg(v___x_3334_);
lean_dec(v___x_3334_);
v___x_3336_ = l_List_lengthTR___redArg(v_us_3218_);
v___x_3337_ = lean_nat_dec_eq(v___x_3335_, v___x_3336_);
lean_dec(v___x_3336_);
lean_dec(v___x_3335_);
v___y_3267_ = v___x_3337_;
goto v___jp_3266_;
}
}
v___jp_3240_:
{
lean_object* v___x_3248_; 
lean_inc_ref(v___y_3241_);
v___x_3248_ = l_Lean_Meta_Sym_mkEqRefl(v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3257_; 
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
v___x_3253_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3253_, 0, v___y_3241_);
lean_ctor_set(v___x_3253_, 1, v_a_3249_);
lean_ctor_set_uint8(v___x_3253_, sizeof(void*)*2, v___x_3239_);
lean_ctor_set_uint8(v___x_3253_, sizeof(void*)*2 + 1, v___x_3239_);
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 0, v___x_3253_);
v___x_3255_ = v___x_3251_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec_ref(v___y_3241_);
v_a_3258_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3248_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3248_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
v___jp_3266_:
{
if (v___y_3267_ == 0)
{
lean_object* v___x_3268_; lean_object* v___x_3270_; 
lean_dec(v_a_3220_);
lean_dec_ref_known(v_e_3206_, 2);
v___x_3268_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
if (v_isShared_3238_ == 0)
{
lean_ctor_set(v___x_3237_, 0, v___x_3268_);
v___x_3270_ = v___x_3237_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v___x_3268_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
else
{
lean_object* v___x_3272_; 
lean_del_object(v___x_3237_);
lean_inc(v_us_3218_);
v___x_3272_ = l_Lean_Core_instantiateValueLevelParams(v_a_3220_, v_us_3218_, v___x_3239_, v_a_3214_, v_a_3215_);
lean_dec(v_a_3220_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_object* v_a_3273_; lean_object* v___x_3274_; 
v_a_3273_ = lean_ctor_get(v___x_3272_, 0);
lean_inc(v_a_3273_);
lean_dec_ref_known(v___x_3272_, 1);
v___x_3274_ = l_Lean_Meta_Sym_unfoldReducible(v_a_3273_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3276_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___x_3274_, 1);
v___x_3276_ = l_Lean_Meta_Sym_shareCommonInc(v_a_3275_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_options_3277_; uint8_t v_hasTrace_3278_; 
v_options_3277_ = lean_ctor_get(v_a_3214_, 2);
v_hasTrace_3278_ = lean_ctor_get_uint8(v_options_3277_, sizeof(void*)*1);
if (v_hasTrace_3278_ == 0)
{
lean_object* v_a_3279_; 
lean_dec_ref_known(v_e_3206_, 2);
v_a_3279_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_a_3279_);
lean_dec_ref_known(v___x_3276_, 1);
v___y_3241_ = v_a_3279_;
v___y_3242_ = v_a_3210_;
v___y_3243_ = v_a_3211_;
v___y_3244_ = v_a_3212_;
v___y_3245_ = v_a_3213_;
v___y_3246_ = v_a_3214_;
v___y_3247_ = v_a_3215_;
goto v___jp_3240_;
}
else
{
lean_object* v_a_3280_; lean_object* v_inheritedTraceOptions_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; uint8_t v___x_3284_; 
v_a_3280_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_a_3280_);
lean_dec_ref_known(v___x_3276_, 1);
v_inheritedTraceOptions_3281_ = lean_ctor_get(v_a_3214_, 13);
v___x_3282_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__1));
v___x_3283_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryUnfold___closed__2);
v___x_3284_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3281_, v_options_3277_, v___x_3283_);
if (v___x_3284_ == 0)
{
lean_dec_ref_known(v_e_3206_, 2);
v___y_3241_ = v_a_3280_;
v___y_3242_ = v_a_3210_;
v___y_3243_ = v_a_3211_;
v___y_3244_ = v_a_3212_;
v___y_3245_ = v_a_3213_;
v___y_3246_ = v_a_3214_;
v___y_3247_ = v_a_3215_;
goto v___jp_3240_;
}
else
{
lean_object* v___x_3285_; lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3285_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___closed__1);
lean_inc(v_declName_3217_);
v___x_3286_ = l_Lean_MessageData_ofName(v_declName_3217_);
v___x_3287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3287_, 0, v___x_3285_);
lean_ctor_set(v___x_3287_, 1, v___x_3286_);
v___x_3288_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8);
v___x_3289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3287_);
lean_ctor_set(v___x_3289_, 1, v___x_3288_);
v___x_3290_ = l_Lean_indentExpr(v_e_3206_);
v___x_3291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3289_);
lean_ctor_set(v___x_3291_, 1, v___x_3290_);
v___x_3292_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_3293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3293_, 0, v___x_3291_);
lean_ctor_set(v___x_3293_, 1, v___x_3292_);
lean_inc(v_a_3280_);
v___x_3294_ = l_Lean_indentExpr(v_a_3280_);
v___x_3295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3293_);
lean_ctor_set(v___x_3295_, 1, v___x_3294_);
v___x_3296_ = l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg(v___x_3282_, v___x_3295_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_dec_ref_known(v___x_3296_, 1);
v___y_3241_ = v_a_3280_;
v___y_3242_ = v_a_3210_;
v___y_3243_ = v_a_3211_;
v___y_3244_ = v_a_3212_;
v___y_3245_ = v_a_3213_;
v___y_3246_ = v_a_3214_;
v___y_3247_ = v_a_3215_;
goto v___jp_3240_;
}
else
{
lean_object* v_a_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3304_; 
lean_dec(v_a_3280_);
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3299_ = v___x_3296_;
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_a_3297_);
lean_dec(v___x_3296_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3302_; 
if (v_isShared_3300_ == 0)
{
v___x_3302_ = v___x_3299_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3297_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
}
}
else
{
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3312_; 
lean_dec_ref_known(v_e_3206_, 2);
v_a_3305_ = lean_ctor_get(v___x_3276_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3307_ = v___x_3276_;
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3276_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3310_; 
if (v_isShared_3308_ == 0)
{
v___x_3310_ = v___x_3307_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3305_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
}
else
{
lean_object* v_a_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3320_; 
lean_dec_ref_known(v_e_3206_, 2);
v_a_3313_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3315_ = v___x_3274_;
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_a_3313_);
lean_dec(v___x_3274_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3318_; 
if (v_isShared_3316_ == 0)
{
v___x_3318_ = v___x_3315_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_a_3313_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
}
else
{
lean_object* v_a_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3328_; 
lean_dec_ref_known(v_e_3206_, 2);
v_a_3321_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3323_ = v___x_3272_;
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_a_3321_);
lean_dec(v___x_3272_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3326_; 
if (v_isShared_3324_ == 0)
{
v___x_3326_ = v___x_3323_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_a_3321_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3346_; 
lean_del_object(v___x_3222_);
lean_dec(v_a_3220_);
lean_dec_ref_known(v_e_3206_, 2);
v_a_3339_ = lean_ctor_get(v___x_3234_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3234_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3341_ = v___x_3234_;
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___x_3234_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3344_; 
if (v_isShared_3342_ == 0)
{
v___x_3344_ = v___x_3341_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3339_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3355_; 
lean_dec_ref_known(v_e_3206_, 2);
v_a_3348_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3355_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3355_ == 0)
{
v___x_3350_ = v___x_3219_;
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3219_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3355_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3353_; 
if (v_isShared_3351_ == 0)
{
v___x_3353_ = v___x_3350_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3354_; 
v_reuseFailAlloc_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3354_, 0, v_a_3348_);
v___x_3353_ = v_reuseFailAlloc_3354_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
return v___x_3353_;
}
}
}
}
else
{
lean_object* v___x_3356_; lean_object* v___x_3357_; 
lean_dec_ref(v_e_3206_);
v___x_3356_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_3357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3356_);
return v___x_3357_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst___boxed(lean_object* v_e_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_){
_start:
{
lean_object* v_res_3369_; 
v_res_3369_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(v_e_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_);
lean_dec(v_a_3367_);
lean_dec_ref(v_a_3366_);
lean_dec(v_a_3365_);
lean_dec_ref(v_a_3364_);
lean_dec(v_a_3363_);
lean_dec_ref(v_a_3362_);
lean_dec(v_a_3361_);
lean_dec_ref(v_a_3360_);
lean_dec(v_a_3359_);
return v_res_3369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(lean_object* v_x_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v___x_3382_; 
lean_inc_ref(v___y_3371_);
v___x_3382_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryCbvTheorems(v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_a_3383_);
if (lean_obj_tag(v_a_3383_) == 0)
{
uint8_t v_done_3384_; 
v_done_3384_ = lean_ctor_get_uint8(v_a_3383_, 0);
if (v_done_3384_ == 0)
{
uint8_t v_contextDependent_3385_; lean_object* v___x_3386_; 
lean_dec_ref_known(v___x_3382_, 1);
v_contextDependent_3385_ = lean_ctor_get_uint8(v_a_3383_, 1);
lean_dec_ref_known(v_a_3383_, 0);
v___x_3386_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleConst(v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; uint8_t v___y_3389_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3387_);
if (v_contextDependent_3385_ == 0)
{
lean_dec(v_a_3387_);
return v___x_3386_;
}
else
{
if (lean_obj_tag(v_a_3387_) == 0)
{
uint8_t v_contextDependent_3399_; 
v_contextDependent_3399_ = lean_ctor_get_uint8(v_a_3387_, 1);
v___y_3389_ = v_contextDependent_3399_;
goto v___jp_3388_;
}
else
{
uint8_t v___x_3400_; 
v___x_3400_ = 0;
v___y_3389_ = v___x_3400_;
goto v___jp_3388_;
}
}
v___jp_3388_:
{
if (v___y_3389_ == 0)
{
lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3397_; 
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3397_ == 0)
{
lean_object* v_unused_3398_; 
v_unused_3398_ = lean_ctor_get(v___x_3386_, 0);
lean_dec(v_unused_3398_);
v___x_3391_ = v___x_3386_;
v_isShared_3392_ = v_isSharedCheck_3397_;
goto v_resetjp_3390_;
}
else
{
lean_dec(v___x_3386_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3397_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3393_; lean_object* v___x_3395_; 
v___x_3393_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3387_);
if (v_isShared_3392_ == 0)
{
lean_ctor_set(v___x_3391_, 0, v___x_3393_);
v___x_3395_ = v___x_3391_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3393_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
return v___x_3395_;
}
}
}
else
{
lean_dec(v_a_3387_);
return v___x_3386_;
}
}
}
else
{
return v___x_3386_;
}
}
else
{
lean_dec_ref_known(v_a_3383_, 0);
lean_dec_ref(v___y_3371_);
return v___x_3382_;
}
}
else
{
lean_dec_ref_known(v_a_3383_, 2);
lean_dec_ref(v___y_3371_);
return v___x_3382_;
}
}
else
{
lean_dec_ref(v___y_3371_);
return v___x_3382_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0___boxed(lean_object* v_x_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v_x_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
lean_dec(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v___y_3403_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(lean_object* v_e_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_){
_start:
{
switch(lean_obj_tag(v_e_3417_))
{
case 9:
{
lean_object* v___x_3431_; 
v___x_3431_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_foldLit___redArg(v_e_3417_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_);
return v___x_3431_;
}
case 11:
{
lean_object* v___x_3432_; 
v___x_3432_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj(v_e_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_);
return v___x_3432_;
}
case 4:
{
lean_object* v___x_3433_; 
lean_inc_ref(v_e_3417_);
v___x_3433_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleOpaqueConst(v_e_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_object* v_a_3434_; lean_object* v___x_3435_; 
v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
lean_inc(v_a_3434_);
v___x_3435_ = lean_box(0);
if (lean_obj_tag(v_a_3434_) == 0)
{
uint8_t v_done_3436_; 
v_done_3436_ = lean_ctor_get_uint8(v_a_3434_, 0);
if (v_done_3436_ == 0)
{
uint8_t v_contextDependent_3437_; lean_object* v___x_3438_; 
lean_dec_ref_known(v___x_3433_, 1);
v_contextDependent_3437_ = lean_ctor_get_uint8(v_a_3434_, 1);
lean_dec_ref_known(v_a_3434_, 0);
v___x_3438_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v___x_3435_, v_e_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3439_; uint8_t v___y_3441_; 
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
lean_inc(v_a_3439_);
if (v_contextDependent_3437_ == 0)
{
lean_dec(v_a_3439_);
return v___x_3438_;
}
else
{
if (lean_obj_tag(v_a_3439_) == 0)
{
uint8_t v_contextDependent_3451_; 
v_contextDependent_3451_ = lean_ctor_get_uint8(v_a_3439_, 1);
v___y_3441_ = v_contextDependent_3451_;
goto v___jp_3440_;
}
else
{
uint8_t v_contextDependent_3452_; 
v_contextDependent_3452_ = lean_ctor_get_uint8(v_a_3439_, sizeof(void*)*2 + 1);
v___y_3441_ = v_contextDependent_3452_;
goto v___jp_3440_;
}
}
v___jp_3440_:
{
if (v___y_3441_ == 0)
{
lean_object* v___x_3443_; uint8_t v_isShared_3444_; uint8_t v_isSharedCheck_3449_; 
v_isSharedCheck_3449_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3449_ == 0)
{
lean_object* v_unused_3450_; 
v_unused_3450_ = lean_ctor_get(v___x_3438_, 0);
lean_dec(v_unused_3450_);
v___x_3443_ = v___x_3438_;
v_isShared_3444_ = v_isSharedCheck_3449_;
goto v_resetjp_3442_;
}
else
{
lean_dec(v___x_3438_);
v___x_3443_ = lean_box(0);
v_isShared_3444_ = v_isSharedCheck_3449_;
goto v_resetjp_3442_;
}
v_resetjp_3442_:
{
lean_object* v___x_3445_; lean_object* v___x_3447_; 
v___x_3445_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3439_);
if (v_isShared_3444_ == 0)
{
lean_ctor_set(v___x_3443_, 0, v___x_3445_);
v___x_3447_ = v___x_3443_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v___x_3445_);
v___x_3447_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
return v___x_3447_;
}
}
}
else
{
lean_dec(v_a_3439_);
return v___x_3438_;
}
}
}
else
{
return v___x_3438_;
}
}
else
{
lean_dec_ref_known(v_a_3434_, 0);
lean_dec_ref_known(v_e_3417_, 2);
return v___x_3433_;
}
}
else
{
uint8_t v_done_3453_; 
v_done_3453_ = lean_ctor_get_uint8(v_a_3434_, sizeof(void*)*2);
if (v_done_3453_ == 0)
{
lean_object* v_e_x27_3454_; lean_object* v_proof_3455_; uint8_t v_contextDependent_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3506_; 
lean_dec_ref_known(v___x_3433_, 1);
v_e_x27_3454_ = lean_ctor_get(v_a_3434_, 0);
v_proof_3455_ = lean_ctor_get(v_a_3434_, 1);
v_contextDependent_3456_ = lean_ctor_get_uint8(v_a_3434_, sizeof(void*)*2 + 1);
v_isSharedCheck_3506_ = !lean_is_exclusive(v_a_3434_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3458_ = v_a_3434_;
v_isShared_3459_ = v_isSharedCheck_3506_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_proof_3455_);
lean_inc(v_e_x27_3454_);
lean_dec(v_a_3434_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3506_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3460_; 
lean_inc_ref(v_e_x27_3454_);
v___x_3460_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___lam__0(v___x_3435_, v_e_x27_3454_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3505_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3463_ = v___x_3460_;
v_isShared_3464_ = v_isSharedCheck_3505_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3460_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3505_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
if (lean_obj_tag(v_a_3461_) == 0)
{
uint8_t v_done_3465_; uint8_t v_contextDependent_3466_; uint8_t v___y_3468_; 
lean_dec_ref_known(v_e_3417_, 2);
v_done_3465_ = lean_ctor_get_uint8(v_a_3461_, 0);
v_contextDependent_3466_ = lean_ctor_get_uint8(v_a_3461_, 1);
lean_dec_ref_known(v_a_3461_, 0);
if (v_contextDependent_3456_ == 0)
{
v___y_3468_ = v_contextDependent_3466_;
goto v___jp_3467_;
}
else
{
v___y_3468_ = v_contextDependent_3456_;
goto v___jp_3467_;
}
v___jp_3467_:
{
lean_object* v___x_3470_; 
if (v_isShared_3459_ == 0)
{
v___x_3470_ = v___x_3458_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_e_x27_3454_);
lean_ctor_set(v_reuseFailAlloc_3474_, 1, v_proof_3455_);
v___x_3470_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
lean_object* v___x_3472_; 
lean_ctor_set_uint8(v___x_3470_, sizeof(void*)*2, v_done_3465_);
lean_ctor_set_uint8(v___x_3470_, sizeof(void*)*2 + 1, v___y_3468_);
if (v_isShared_3464_ == 0)
{
lean_ctor_set(v___x_3463_, 0, v___x_3470_);
v___x_3472_ = v___x_3463_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3470_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
}
else
{
lean_object* v_e_x27_3475_; lean_object* v_proof_3476_; uint8_t v_done_3477_; uint8_t v_contextDependent_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3504_; 
lean_del_object(v___x_3463_);
lean_del_object(v___x_3458_);
v_e_x27_3475_ = lean_ctor_get(v_a_3461_, 0);
v_proof_3476_ = lean_ctor_get(v_a_3461_, 1);
v_done_3477_ = lean_ctor_get_uint8(v_a_3461_, sizeof(void*)*2);
v_contextDependent_3478_ = lean_ctor_get_uint8(v_a_3461_, sizeof(void*)*2 + 1);
v_isSharedCheck_3504_ = !lean_is_exclusive(v_a_3461_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3480_ = v_a_3461_;
v_isShared_3481_ = v_isSharedCheck_3504_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_proof_3476_);
lean_inc(v_e_x27_3475_);
lean_dec(v_a_3461_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3504_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3482_; 
lean_inc_ref(v_e_x27_3475_);
v___x_3482_ = l_Lean_Meta_Sym_Simp_mkEqTrans(v_e_3417_, v_e_x27_3454_, v_proof_3455_, v_e_x27_3475_, v_proof_3476_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_);
if (lean_obj_tag(v___x_3482_) == 0)
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3495_; 
v_a_3483_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3485_ = v___x_3482_;
v_isShared_3486_ = v_isSharedCheck_3495_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3482_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3495_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
uint8_t v___y_3488_; 
if (v_contextDependent_3456_ == 0)
{
v___y_3488_ = v_contextDependent_3478_;
goto v___jp_3487_;
}
else
{
v___y_3488_ = v_contextDependent_3456_;
goto v___jp_3487_;
}
v___jp_3487_:
{
lean_object* v___x_3490_; 
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 1, v_a_3483_);
v___x_3490_ = v___x_3480_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_e_x27_3475_);
lean_ctor_set(v_reuseFailAlloc_3494_, 1, v_a_3483_);
lean_ctor_set_uint8(v_reuseFailAlloc_3494_, sizeof(void*)*2, v_done_3477_);
v___x_3490_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
lean_object* v___x_3492_; 
lean_ctor_set_uint8(v___x_3490_, sizeof(void*)*2 + 1, v___y_3488_);
if (v_isShared_3486_ == 0)
{
lean_ctor_set(v___x_3485_, 0, v___x_3490_);
v___x_3492_ = v___x_3485_;
goto v_reusejp_3491_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v___x_3490_);
v___x_3492_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3491_;
}
v_reusejp_3491_:
{
return v___x_3492_;
}
}
}
}
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
lean_del_object(v___x_3480_);
lean_dec_ref(v_e_x27_3475_);
v_a_3496_ = lean_ctor_get(v___x_3482_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_3482_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3482_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3501_; 
if (v_isShared_3499_ == 0)
{
v___x_3501_ = v___x_3498_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
}
}
}
else
{
lean_del_object(v___x_3458_);
lean_dec_ref(v_proof_3455_);
lean_dec_ref(v_e_x27_3454_);
lean_dec_ref_known(v_e_3417_, 2);
return v___x_3460_;
}
}
}
else
{
lean_dec_ref_known(v_a_3434_, 2);
lean_dec_ref_known(v_e_3417_, 2);
return v___x_3433_;
}
}
}
else
{
lean_dec_ref_known(v_e_3417_, 2);
return v___x_3433_;
}
}
case 5:
{
lean_object* v___x_3507_; 
lean_inc_ref(v_e_3417_);
v___x_3507_ = l_Lean_Meta_Tactic_Cbv_tryMatcher(v_e_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v_a_3508_; 
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
lean_inc(v_a_3508_);
if (lean_obj_tag(v_a_3508_) == 0)
{
uint8_t v_done_3509_; 
v_done_3509_ = lean_ctor_get_uint8(v_a_3508_, 0);
if (v_done_3509_ == 0)
{
uint8_t v_contextDependent_3510_; lean_object* v___x_3511_; 
lean_dec_ref_known(v___x_3507_, 1);
v_contextDependent_3510_ = lean_ctor_get_uint8(v_a_3508_, 1);
lean_dec_ref_known(v_a_3508_, 0);
v___x_3511_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_simplifyAppFn(v_e_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; uint8_t v___y_3514_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_a_3512_);
if (v_contextDependent_3510_ == 0)
{
lean_dec(v_a_3512_);
return v___x_3511_;
}
else
{
if (lean_obj_tag(v_a_3512_) == 0)
{
uint8_t v_contextDependent_3524_; 
v_contextDependent_3524_ = lean_ctor_get_uint8(v_a_3512_, 1);
v___y_3514_ = v_contextDependent_3524_;
goto v___jp_3513_;
}
else
{
uint8_t v_contextDependent_3525_; 
v_contextDependent_3525_ = lean_ctor_get_uint8(v_a_3512_, sizeof(void*)*2 + 1);
v___y_3514_ = v_contextDependent_3525_;
goto v___jp_3513_;
}
}
v___jp_3513_:
{
if (v___y_3514_ == 0)
{
lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3522_; 
v_isSharedCheck_3522_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3522_ == 0)
{
lean_object* v_unused_3523_; 
v_unused_3523_ = lean_ctor_get(v___x_3511_, 0);
lean_dec(v_unused_3523_);
v___x_3516_ = v___x_3511_;
v_isShared_3517_ = v_isSharedCheck_3522_;
goto v_resetjp_3515_;
}
else
{
lean_dec(v___x_3511_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3522_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3518_; lean_object* v___x_3520_; 
v___x_3518_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3512_);
if (v_isShared_3517_ == 0)
{
lean_ctor_set(v___x_3516_, 0, v___x_3518_);
v___x_3520_ = v___x_3516_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3521_; 
v_reuseFailAlloc_3521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3521_, 0, v___x_3518_);
v___x_3520_ = v_reuseFailAlloc_3521_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
return v___x_3520_;
}
}
}
else
{
lean_dec(v_a_3512_);
return v___x_3511_;
}
}
}
else
{
return v___x_3511_;
}
}
else
{
lean_dec_ref_known(v_a_3508_, 0);
lean_dec_ref_known(v_e_3417_, 2);
return v___x_3507_;
}
}
else
{
lean_dec_ref_known(v_a_3508_, 2);
lean_dec_ref_known(v_e_3417_, 2);
return v___x_3507_;
}
}
else
{
lean_dec_ref_known(v_e_3417_, 2);
return v___x_3507_;
}
}
case 8:
{
uint8_t v___x_3526_; 
v___x_3526_ = l_Lean_Expr_letNondep_x21(v_e_3417_);
if (v___x_3526_ == 0)
{
lean_object* v___x_3527_; 
v___x_3527_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_zetaReduce___redArg(v_e_3417_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_);
return v___x_3527_;
}
else
{
lean_object* v___x_3528_; 
v___x_3528_ = l_Lean_Meta_Sym_Simp_toBetaApp(v_e_3417_, v_a_3421_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3540_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3531_ = v___x_3528_;
v_isShared_3532_ = v_isSharedCheck_3540_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3528_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3540_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v_e_3533_; lean_object* v_h_3534_; uint8_t v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3538_; 
v_e_3533_ = lean_ctor_get(v_a_3529_, 2);
lean_inc_ref(v_e_3533_);
v_h_3534_ = lean_ctor_get(v_a_3529_, 3);
lean_inc_ref(v_h_3534_);
lean_dec(v_a_3529_);
v___x_3535_ = 0;
v___x_3536_ = lean_alloc_ctor(1, 2, 2);
lean_ctor_set(v___x_3536_, 0, v_e_3533_);
lean_ctor_set(v___x_3536_, 1, v_h_3534_);
lean_ctor_set_uint8(v___x_3536_, sizeof(void*)*2, v___x_3535_);
lean_ctor_set_uint8(v___x_3536_, sizeof(void*)*2 + 1, v___x_3535_);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v___x_3536_);
v___x_3538_ = v___x_3531_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v___x_3536_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
else
{
lean_object* v_a_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3548_; 
v_a_3541_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3543_ = v___x_3528_;
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_a_3541_);
lean_dec(v___x_3528_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3546_; 
if (v_isShared_3544_ == 0)
{
v___x_3546_ = v___x_3543_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3541_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
}
case 7:
{
lean_dec_ref_known(v_e_3417_, 3);
goto v___jp_3428_;
}
case 6:
{
lean_dec_ref_known(v_e_3417_, 3);
goto v___jp_3428_;
}
case 1:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
lean_dec_ref_known(v_e_3417_, 1);
v___x_3549_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3550_, 0, v___x_3549_);
return v___x_3550_;
}
case 2:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; 
lean_dec_ref_known(v_e_3417_, 1);
v___x_3551_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3551_);
return v___x_3552_;
}
case 0:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; 
lean_dec_ref_known(v_e_3417_, 1);
v___x_3553_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3553_);
return v___x_3554_;
}
case 3:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; 
lean_dec_ref_known(v_e_3417_, 1);
v___x_3555_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3556_, 0, v___x_3555_);
return v___x_3556_;
}
default: 
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
lean_dec_ref(v_e_3417_);
v___x_3557_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__12));
v___x_3558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3558_, 0, v___x_3557_);
return v___x_3558_;
}
}
v___jp_3428_:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3429_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___closed__0));
v___x_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3429_);
return v___x_3430_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep___boxed(lean_object* v_e_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_){
_start:
{
lean_object* v_res_3570_; 
v_res_3570_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(v_e_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_);
lean_dec(v_a_3568_);
lean_dec_ref(v_a_3567_);
lean_dec(v_a_3566_);
lean_dec_ref(v_a_3565_);
lean_dec(v_a_3564_);
lean_dec_ref(v_a_3563_);
lean_dec(v_a_3562_);
lean_dec_ref(v_a_3561_);
lean_dec(v_a_3560_);
return v_res_3570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre(lean_object* v_simprocs_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_){
_start:
{
lean_object* v___y_3584_; lean_object* v___y_3585_; uint8_t v___y_3586_; lean_object* v___x_3589_; 
lean_inc_ref(v_a_3572_);
v___x_3589_ = l_Lean_Meta_Tactic_Cbv_isBuiltinValue___redArg(v_a_3572_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v_a_3590_; 
v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
lean_inc(v_a_3590_);
if (lean_obj_tag(v_a_3590_) == 0)
{
uint8_t v_done_3591_; uint8_t v_contextDependent_3592_; lean_object* v___y_3594_; lean_object* v_a_3595_; lean_object* v___y_3599_; lean_object* v___y_3600_; uint8_t v___y_3601_; lean_object* v___y_3605_; 
v_done_3591_ = lean_ctor_get_uint8(v_a_3590_, 0);
v_contextDependent_3592_ = lean_ctor_get_uint8(v_a_3590_, 1);
lean_dec_ref_known(v_a_3590_, 0);
if (v_done_3591_ == 0)
{
lean_object* v___x_3607_; 
lean_dec_ref_known(v___x_3589_, 1);
lean_inc_ref(v_a_3572_);
v___x_3607_ = l_Lean_Meta_Tactic_Cbv_isProofTerm___redArg(v_a_3572_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc(v_a_3608_);
if (lean_obj_tag(v_a_3608_) == 0)
{
uint8_t v_done_3609_; uint8_t v_contextDependent_3610_; lean_object* v___y_3612_; lean_object* v_a_3613_; lean_object* v___y_3617_; 
v_done_3609_ = lean_ctor_get_uint8(v_a_3608_, 0);
v_contextDependent_3610_ = lean_ctor_get_uint8(v_a_3608_, 1);
lean_dec_ref_known(v_a_3608_, 0);
if (v_done_3609_ == 0)
{
lean_object* v_pre_3619_; lean_object* v_erased_3620_; lean_object* v___x_3621_; 
lean_dec_ref_known(v___x_3607_, 1);
v_pre_3619_ = lean_ctor_get(v_simprocs_3571_, 0);
v_erased_3620_ = lean_ctor_get(v_simprocs_3571_, 4);
lean_inc_ref(v_a_3572_);
v___x_3621_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_pre_3619_, v_erased_3620_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_);
if (lean_obj_tag(v___x_3621_) == 0)
{
lean_object* v_a_3622_; 
v_a_3622_ = lean_ctor_get(v___x_3621_, 0);
lean_inc(v_a_3622_);
if (lean_obj_tag(v_a_3622_) == 0)
{
uint8_t v_done_3623_; 
v_done_3623_ = lean_ctor_get_uint8(v_a_3622_, 0);
if (v_done_3623_ == 0)
{
uint8_t v_contextDependent_3624_; lean_object* v___x_3625_; 
lean_dec_ref_known(v___x_3621_, 1);
v_contextDependent_3624_ = lean_ctor_get_uint8(v_a_3622_, 1);
lean_dec_ref_known(v_a_3622_, 0);
v___x_3625_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPreStep(v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_object* v_a_3626_; uint8_t v___y_3628_; 
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
lean_inc(v_a_3626_);
if (v_contextDependent_3624_ == 0)
{
lean_dec(v_a_3626_);
v___y_3617_ = v___x_3625_;
goto v___jp_3616_;
}
else
{
if (lean_obj_tag(v_a_3626_) == 0)
{
uint8_t v_contextDependent_3638_; 
v_contextDependent_3638_ = lean_ctor_get_uint8(v_a_3626_, 1);
v___y_3628_ = v_contextDependent_3638_;
goto v___jp_3627_;
}
else
{
uint8_t v_contextDependent_3639_; 
v_contextDependent_3639_ = lean_ctor_get_uint8(v_a_3626_, sizeof(void*)*2 + 1);
v___y_3628_ = v_contextDependent_3639_;
goto v___jp_3627_;
}
}
v___jp_3627_:
{
if (v___y_3628_ == 0)
{
lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3636_; 
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3636_ == 0)
{
lean_object* v_unused_3637_; 
v_unused_3637_ = lean_ctor_get(v___x_3625_, 0);
lean_dec(v_unused_3637_);
v___x_3630_ = v___x_3625_;
v_isShared_3631_ = v_isSharedCheck_3636_;
goto v_resetjp_3629_;
}
else
{
lean_dec(v___x_3625_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3636_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3632_; lean_object* v___x_3634_; 
v___x_3632_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3626_);
lean_inc_ref(v___x_3632_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 0, v___x_3632_);
v___x_3634_ = v___x_3630_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v___x_3632_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
v___y_3612_ = v___x_3634_;
v_a_3613_ = v___x_3632_;
goto v___jp_3611_;
}
}
}
else
{
lean_dec(v_a_3626_);
v___y_3617_ = v___x_3625_;
goto v___jp_3616_;
}
}
}
else
{
v___y_3617_ = v___x_3625_;
goto v___jp_3616_;
}
}
else
{
lean_dec_ref_known(v_a_3622_, 0);
lean_dec_ref(v_a_3572_);
v___y_3617_ = v___x_3621_;
goto v___jp_3616_;
}
}
else
{
lean_dec_ref_known(v_a_3622_, 2);
lean_dec_ref(v_a_3572_);
v___y_3617_ = v___x_3621_;
goto v___jp_3616_;
}
}
else
{
lean_dec_ref(v_a_3572_);
v___y_3617_ = v___x_3621_;
goto v___jp_3616_;
}
}
else
{
lean_dec_ref(v_a_3572_);
v___y_3605_ = v___x_3607_;
goto v___jp_3604_;
}
v___jp_3611_:
{
if (v_contextDependent_3610_ == 0)
{
v___y_3594_ = v___y_3612_;
v_a_3595_ = v_a_3613_;
goto v___jp_3593_;
}
else
{
if (lean_obj_tag(v_a_3613_) == 0)
{
uint8_t v_contextDependent_3614_; 
v_contextDependent_3614_ = lean_ctor_get_uint8(v_a_3613_, 1);
v___y_3599_ = v_a_3613_;
v___y_3600_ = v___y_3612_;
v___y_3601_ = v_contextDependent_3614_;
goto v___jp_3598_;
}
else
{
uint8_t v_contextDependent_3615_; 
v_contextDependent_3615_ = lean_ctor_get_uint8(v_a_3613_, sizeof(void*)*2 + 1);
v___y_3599_ = v_a_3613_;
v___y_3600_ = v___y_3612_;
v___y_3601_ = v_contextDependent_3615_;
goto v___jp_3598_;
}
}
}
v___jp_3616_:
{
if (lean_obj_tag(v___y_3617_) == 0)
{
lean_object* v_a_3618_; 
v_a_3618_ = lean_ctor_get(v___y_3617_, 0);
lean_inc(v_a_3618_);
v___y_3612_ = v___y_3617_;
v_a_3613_ = v_a_3618_;
goto v___jp_3611_;
}
else
{
return v___y_3617_;
}
}
}
else
{
lean_dec_ref_known(v_a_3608_, 2);
lean_dec_ref(v_a_3572_);
v___y_3605_ = v___x_3607_;
goto v___jp_3604_;
}
}
else
{
lean_dec_ref(v_a_3572_);
v___y_3605_ = v___x_3607_;
goto v___jp_3604_;
}
}
else
{
lean_dec_ref(v_a_3572_);
return v___x_3589_;
}
v___jp_3593_:
{
if (v_contextDependent_3592_ == 0)
{
lean_dec_ref(v_a_3595_);
return v___y_3594_;
}
else
{
if (lean_obj_tag(v_a_3595_) == 0)
{
uint8_t v_contextDependent_3596_; 
v_contextDependent_3596_ = lean_ctor_get_uint8(v_a_3595_, 1);
v___y_3584_ = v___y_3594_;
v___y_3585_ = v_a_3595_;
v___y_3586_ = v_contextDependent_3596_;
goto v___jp_3583_;
}
else
{
uint8_t v_contextDependent_3597_; 
v_contextDependent_3597_ = lean_ctor_get_uint8(v_a_3595_, sizeof(void*)*2 + 1);
v___y_3584_ = v___y_3594_;
v___y_3585_ = v_a_3595_;
v___y_3586_ = v_contextDependent_3597_;
goto v___jp_3583_;
}
}
}
v___jp_3598_:
{
if (v___y_3601_ == 0)
{
lean_object* v___x_3602_; lean_object* v___x_3603_; 
lean_dec_ref(v___y_3600_);
v___x_3602_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3599_);
lean_inc_ref(v___x_3602_);
v___x_3603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
v___y_3594_ = v___x_3603_;
v_a_3595_ = v___x_3602_;
goto v___jp_3593_;
}
else
{
v___y_3594_ = v___y_3600_;
v_a_3595_ = v___y_3599_;
goto v___jp_3593_;
}
}
v___jp_3604_:
{
if (lean_obj_tag(v___y_3605_) == 0)
{
lean_object* v_a_3606_; 
v_a_3606_ = lean_ctor_get(v___y_3605_, 0);
lean_inc(v_a_3606_);
v___y_3594_ = v___y_3605_;
v_a_3595_ = v_a_3606_;
goto v___jp_3593_;
}
else
{
return v___y_3605_;
}
}
}
else
{
lean_dec_ref_known(v_a_3590_, 2);
lean_dec_ref(v_a_3572_);
return v___x_3589_;
}
}
else
{
lean_dec_ref(v_a_3572_);
return v___x_3589_;
}
v___jp_3583_:
{
if (v___y_3586_ == 0)
{
lean_object* v___x_3587_; lean_object* v___x_3588_; 
lean_dec_ref(v___y_3584_);
v___x_3587_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3585_);
v___x_3588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3587_);
return v___x_3588_;
}
else
{
lean_dec_ref(v___y_3585_);
return v___y_3584_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre___boxed(lean_object* v_simprocs_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_, lean_object* v_a_3650_, lean_object* v_a_3651_){
_start:
{
lean_object* v_res_3652_; 
v_res_3652_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre(v_simprocs_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, v_a_3650_);
lean_dec(v_a_3650_);
lean_dec_ref(v_a_3649_);
lean_dec(v_a_3648_);
lean_dec_ref(v_a_3647_);
lean_dec(v_a_3646_);
lean_dec_ref(v_a_3645_);
lean_dec(v_a_3644_);
lean_dec_ref(v_a_3643_);
lean_dec(v_a_3642_);
lean_dec_ref(v_simprocs_3640_);
return v_res_3652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost(lean_object* v_simprocs_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_, lean_object* v_a_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_){
_start:
{
lean_object* v___y_3666_; lean_object* v___y_3667_; uint8_t v___y_3668_; lean_object* v___x_3671_; lean_object* v___x_3672_; 
v___x_3671_ = lean_unsigned_to_nat(255u);
lean_inc_ref(v_a_3654_);
v___x_3672_ = l_Lean_Meta_Sym_Simp_evalGround___redArg(v___x_3671_, v_a_3654_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v_a_3673_; 
v_a_3673_ = lean_ctor_get(v___x_3672_, 0);
lean_inc(v_a_3673_);
if (lean_obj_tag(v_a_3673_) == 0)
{
uint8_t v_done_3674_; uint8_t v_contextDependent_3675_; lean_object* v___y_3677_; lean_object* v_a_3678_; lean_object* v___y_3682_; lean_object* v___y_3683_; uint8_t v___y_3684_; lean_object* v___y_3688_; 
v_done_3674_ = lean_ctor_get_uint8(v_a_3673_, 0);
v_contextDependent_3675_ = lean_ctor_get_uint8(v_a_3673_, 1);
lean_dec_ref_known(v_a_3673_, 0);
if (v_done_3674_ == 0)
{
lean_object* v_eval_3690_; lean_object* v_post_3691_; lean_object* v_erased_3692_; lean_object* v___x_3693_; 
lean_dec_ref_known(v___x_3672_, 1);
v_eval_3690_ = lean_ctor_get(v_simprocs_3653_, 1);
v_post_3691_ = lean_ctor_get(v_simprocs_3653_, 2);
v_erased_3692_ = lean_ctor_get(v_simprocs_3653_, 4);
lean_inc_ref(v_a_3654_);
v___x_3693_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_eval_3690_, v_erased_3692_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v_a_3694_; 
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_a_3694_);
if (lean_obj_tag(v_a_3694_) == 0)
{
uint8_t v_done_3695_; uint8_t v_contextDependent_3696_; lean_object* v___y_3698_; lean_object* v_a_3699_; lean_object* v___y_3703_; 
v_done_3695_ = lean_ctor_get_uint8(v_a_3694_, 0);
v_contextDependent_3696_ = lean_ctor_get_uint8(v_a_3694_, 1);
lean_dec_ref_known(v_a_3694_, 0);
if (v_done_3695_ == 0)
{
lean_object* v___x_3705_; 
lean_dec_ref_known(v___x_3693_, 1);
lean_inc_ref(v_a_3654_);
v___x_3705_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleApp(v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
if (lean_obj_tag(v___x_3705_) == 0)
{
lean_object* v_a_3706_; 
v_a_3706_ = lean_ctor_get(v___x_3705_, 0);
lean_inc(v_a_3706_);
if (lean_obj_tag(v_a_3706_) == 0)
{
uint8_t v_done_3707_; 
v_done_3707_ = lean_ctor_get_uint8(v_a_3706_, 0);
if (v_done_3707_ == 0)
{
uint8_t v_contextDependent_3708_; lean_object* v___x_3709_; 
lean_dec_ref_known(v___x_3705_, 1);
v_contextDependent_3708_ = lean_ctor_get_uint8(v_a_3706_, 1);
lean_dec_ref_known(v_a_3706_, 0);
v___x_3709_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(v_post_3691_, v_erased_3692_, v_a_3654_, v_a_3655_, v_a_3656_, v_a_3657_, v_a_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_);
if (lean_obj_tag(v___x_3709_) == 0)
{
lean_object* v_a_3710_; uint8_t v___y_3712_; 
v_a_3710_ = lean_ctor_get(v___x_3709_, 0);
lean_inc(v_a_3710_);
if (v_contextDependent_3708_ == 0)
{
lean_dec(v_a_3710_);
v___y_3703_ = v___x_3709_;
goto v___jp_3702_;
}
else
{
if (lean_obj_tag(v_a_3710_) == 0)
{
uint8_t v_contextDependent_3722_; 
v_contextDependent_3722_ = lean_ctor_get_uint8(v_a_3710_, 1);
v___y_3712_ = v_contextDependent_3722_;
goto v___jp_3711_;
}
else
{
uint8_t v_contextDependent_3723_; 
v_contextDependent_3723_ = lean_ctor_get_uint8(v_a_3710_, sizeof(void*)*2 + 1);
v___y_3712_ = v_contextDependent_3723_;
goto v___jp_3711_;
}
}
v___jp_3711_:
{
if (v___y_3712_ == 0)
{
lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3720_; 
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3709_);
if (v_isSharedCheck_3720_ == 0)
{
lean_object* v_unused_3721_; 
v_unused_3721_ = lean_ctor_get(v___x_3709_, 0);
lean_dec(v_unused_3721_);
v___x_3714_ = v___x_3709_;
v_isShared_3715_ = v_isSharedCheck_3720_;
goto v_resetjp_3713_;
}
else
{
lean_dec(v___x_3709_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3720_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3716_; lean_object* v___x_3718_; 
v___x_3716_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v_a_3710_);
lean_inc_ref(v___x_3716_);
if (v_isShared_3715_ == 0)
{
lean_ctor_set(v___x_3714_, 0, v___x_3716_);
v___x_3718_ = v___x_3714_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v___x_3716_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
v___y_3698_ = v___x_3718_;
v_a_3699_ = v___x_3716_;
goto v___jp_3697_;
}
}
}
else
{
lean_dec(v_a_3710_);
v___y_3703_ = v___x_3709_;
goto v___jp_3702_;
}
}
}
else
{
v___y_3703_ = v___x_3709_;
goto v___jp_3702_;
}
}
else
{
lean_dec_ref_known(v_a_3706_, 0);
lean_dec_ref(v_a_3654_);
v___y_3703_ = v___x_3705_;
goto v___jp_3702_;
}
}
else
{
lean_dec_ref_known(v_a_3706_, 2);
lean_dec_ref(v_a_3654_);
v___y_3703_ = v___x_3705_;
goto v___jp_3702_;
}
}
else
{
lean_dec_ref(v_a_3654_);
v___y_3703_ = v___x_3705_;
goto v___jp_3702_;
}
}
else
{
lean_dec_ref(v_a_3654_);
v___y_3688_ = v___x_3693_;
goto v___jp_3687_;
}
v___jp_3697_:
{
if (v_contextDependent_3696_ == 0)
{
v___y_3677_ = v___y_3698_;
v_a_3678_ = v_a_3699_;
goto v___jp_3676_;
}
else
{
if (lean_obj_tag(v_a_3699_) == 0)
{
uint8_t v_contextDependent_3700_; 
v_contextDependent_3700_ = lean_ctor_get_uint8(v_a_3699_, 1);
v___y_3682_ = v_a_3699_;
v___y_3683_ = v___y_3698_;
v___y_3684_ = v_contextDependent_3700_;
goto v___jp_3681_;
}
else
{
uint8_t v_contextDependent_3701_; 
v_contextDependent_3701_ = lean_ctor_get_uint8(v_a_3699_, sizeof(void*)*2 + 1);
v___y_3682_ = v_a_3699_;
v___y_3683_ = v___y_3698_;
v___y_3684_ = v_contextDependent_3701_;
goto v___jp_3681_;
}
}
}
v___jp_3702_:
{
if (lean_obj_tag(v___y_3703_) == 0)
{
lean_object* v_a_3704_; 
v_a_3704_ = lean_ctor_get(v___y_3703_, 0);
lean_inc(v_a_3704_);
v___y_3698_ = v___y_3703_;
v_a_3699_ = v_a_3704_;
goto v___jp_3697_;
}
else
{
return v___y_3703_;
}
}
}
else
{
lean_dec_ref_known(v_a_3694_, 2);
lean_dec_ref(v_a_3654_);
v___y_3688_ = v___x_3693_;
goto v___jp_3687_;
}
}
else
{
lean_dec_ref(v_a_3654_);
v___y_3688_ = v___x_3693_;
goto v___jp_3687_;
}
}
else
{
lean_dec_ref(v_a_3654_);
return v___x_3672_;
}
v___jp_3676_:
{
if (v_contextDependent_3675_ == 0)
{
lean_dec_ref(v_a_3678_);
return v___y_3677_;
}
else
{
if (lean_obj_tag(v_a_3678_) == 0)
{
uint8_t v_contextDependent_3679_; 
v_contextDependent_3679_ = lean_ctor_get_uint8(v_a_3678_, 1);
v___y_3666_ = v___y_3677_;
v___y_3667_ = v_a_3678_;
v___y_3668_ = v_contextDependent_3679_;
goto v___jp_3665_;
}
else
{
uint8_t v_contextDependent_3680_; 
v_contextDependent_3680_ = lean_ctor_get_uint8(v_a_3678_, sizeof(void*)*2 + 1);
v___y_3666_ = v___y_3677_;
v___y_3667_ = v_a_3678_;
v___y_3668_ = v_contextDependent_3680_;
goto v___jp_3665_;
}
}
}
v___jp_3681_:
{
if (v___y_3684_ == 0)
{
lean_object* v___x_3685_; lean_object* v___x_3686_; 
lean_dec_ref(v___y_3683_);
v___x_3685_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3682_);
lean_inc_ref(v___x_3685_);
v___x_3686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3685_);
v___y_3677_ = v___x_3686_;
v_a_3678_ = v___x_3685_;
goto v___jp_3676_;
}
else
{
v___y_3677_ = v___y_3683_;
v_a_3678_ = v___y_3682_;
goto v___jp_3676_;
}
}
v___jp_3687_:
{
if (lean_obj_tag(v___y_3688_) == 0)
{
lean_object* v_a_3689_; 
v_a_3689_ = lean_ctor_get(v___y_3688_, 0);
lean_inc(v_a_3689_);
v___y_3677_ = v___y_3688_;
v_a_3678_ = v_a_3689_;
goto v___jp_3676_;
}
else
{
return v___y_3688_;
}
}
}
else
{
lean_dec_ref_known(v_a_3673_, 2);
lean_dec_ref(v_a_3654_);
return v___x_3672_;
}
}
else
{
lean_dec_ref(v_a_3654_);
return v___x_3672_;
}
v___jp_3665_:
{
if (v___y_3668_ == 0)
{
lean_object* v___x_3669_; lean_object* v___x_3670_; 
lean_dec_ref(v___y_3666_);
v___x_3669_ = l_Lean_Meta_Sym_Simp_Result_withContextDependent(v___y_3667_);
v___x_3670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3669_);
return v___x_3670_;
}
else
{
lean_dec_ref(v___y_3667_);
return v___y_3666_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost___boxed(lean_object* v_simprocs_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_){
_start:
{
lean_object* v_res_3736_; 
v_res_3736_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost(v_simprocs_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_);
lean_dec(v_a_3734_);
lean_dec_ref(v_a_3733_);
lean_dec(v_a_3732_);
lean_dec_ref(v_a_3731_);
lean_dec(v_a_3730_);
lean_dec_ref(v_a_3729_);
lean_dec(v_a_3728_);
lean_dec_ref(v_a_3727_);
lean_dec(v_a_3726_);
lean_dec_ref(v_simprocs_3724_);
return v_res_3736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(lean_object* v_simprocs_3737_){
_start:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
lean_inc_ref(v_simprocs_3737_);
v___x_3738_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPre___boxed), 12, 1);
lean_closure_set(v___x_3738_, 0, v_simprocs_3737_);
v___x_3739_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvPost___boxed), 12, 1);
lean_closure_set(v___x_3739_, 0, v_simprocs_3737_);
v___x_3740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3738_);
lean_ctor_set(v___x_3740_, 1, v___x_3739_);
return v___x_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg(lean_object* v_x_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v_config_3749_; lean_object* v_sharedExprs_3750_; uint8_t v_verbose_3751_; uint8_t v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v_config_3749_ = lean_ctor_get(v___y_3742_, 1);
v_sharedExprs_3750_ = lean_ctor_get(v___y_3742_, 0);
v_verbose_3751_ = lean_ctor_get_uint8(v_config_3749_, 0);
v___x_3752_ = 0;
v___x_3753_ = lean_alloc_ctor(0, 0, 3);
lean_ctor_set_uint8(v___x_3753_, 0, v_verbose_3751_);
lean_ctor_set_uint8(v___x_3753_, 1, v___x_3752_);
lean_ctor_set_uint8(v___x_3753_, 2, v___x_3752_);
lean_inc_ref(v_sharedExprs_3750_);
v___x_3754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3754_, 0, v_sharedExprs_3750_);
lean_ctor_set(v___x_3754_, 1, v___x_3753_);
lean_inc(v___y_3747_);
lean_inc_ref(v___y_3746_);
lean_inc(v___y_3745_);
lean_inc_ref(v___y_3744_);
lean_inc(v___y_3743_);
v___x_3755_ = lean_apply_7(v_x_3741_, v___x_3754_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, lean_box(0));
return v___x_3755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg___boxed(lean_object* v_x_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_, lean_object* v___y_3763_){
_start:
{
lean_object* v_res_3764_; 
v_res_3764_ = l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg(v_x_3756_, v___y_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_);
lean_dec(v___y_3762_);
lean_dec_ref(v___y_3761_);
lean_dec(v___y_3760_);
lean_dec_ref(v___y_3759_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
return v_res_3764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0(lean_object* v_00_u03b1_3765_, lean_object* v_x_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_){
_start:
{
lean_object* v___x_3774_; 
v___x_3774_ = l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg(v_x_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_, v___y_3771_, v___y_3772_);
return v___x_3774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___boxed(lean_object* v_00_u03b1_3775_, lean_object* v_x_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
lean_object* v_res_3784_; 
v_res_3784_ = l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0(v_00_u03b1_3775_, v_x_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec(v___y_3778_);
lean_dec_ref(v___y_3777_);
return v_res_3784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___lam__0(lean_object* v_e_3785_, lean_object* v_config_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
lean_object* v___x_3794_; 
v___x_3794_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v___y_3792_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_object* v_a_3795_; lean_object* v_methods_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v_a_3795_ = lean_ctor_get(v___x_3794_, 0);
lean_inc(v_a_3795_);
lean_dec_ref_known(v___x_3794_, 1);
v_methods_3796_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_3795_);
v___x_3797_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3797_, 0, v_e_3785_);
v___x_3798_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_3797_, v_methods_3796_, v_config_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
return v___x_3798_;
}
else
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3806_; 
lean_dec_ref(v_config_3786_);
lean_dec_ref(v_e_3785_);
v_a_3799_ = lean_ctor_get(v___x_3794_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3794_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3801_ = v___x_3794_;
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3794_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3804_; 
if (v_isShared_3802_ == 0)
{
v___x_3804_ = v___x_3801_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3799_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___lam__0___boxed(lean_object* v_e_3807_, lean_object* v_config_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_){
_start:
{
lean_object* v_res_3816_; 
v_res_3816_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___lam__0(v_e_3807_, v_config_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
return v_res_3816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(lean_object* v_e_3817_, lean_object* v_config_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_, lean_object* v_a_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_){
_start:
{
lean_object* v___f_3826_; lean_object* v___x_3827_; 
v___f_3826_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3826_, 0, v_e_3817_);
lean_closure_set(v___f_3826_, 1, v_config_3818_);
v___x_3827_ = l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg(v___f_3826_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_);
return v___x_3827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore___boxed(lean_object* v_e_3828_, lean_object* v_config_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_e_3828_, v_config_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_);
lean_dec(v_a_3835_);
lean_dec_ref(v_a_3834_);
lean_dec(v_a_3833_);
lean_dec_ref(v_a_3832_);
lean_dec(v_a_3831_);
lean_dec_ref(v_a_3830_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(lean_object* v___y_3838_){
_start:
{
lean_object* v___x_3840_; lean_object* v_traceState_3841_; lean_object* v_traces_3842_; lean_object* v___x_3843_; lean_object* v_traceState_3844_; lean_object* v_env_3845_; lean_object* v_nextMacroScope_3846_; lean_object* v_ngen_3847_; lean_object* v_auxDeclNGen_3848_; lean_object* v_cache_3849_; lean_object* v_messages_3850_; lean_object* v_infoState_3851_; lean_object* v_snapshotTasks_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3873_; 
v___x_3840_ = lean_st_ref_get(v___y_3838_);
v_traceState_3841_ = lean_ctor_get(v___x_3840_, 4);
lean_inc_ref(v_traceState_3841_);
lean_dec(v___x_3840_);
v_traces_3842_ = lean_ctor_get(v_traceState_3841_, 0);
lean_inc_ref(v_traces_3842_);
lean_dec_ref(v_traceState_3841_);
v___x_3843_ = lean_st_ref_take(v___y_3838_);
v_traceState_3844_ = lean_ctor_get(v___x_3843_, 4);
v_env_3845_ = lean_ctor_get(v___x_3843_, 0);
v_nextMacroScope_3846_ = lean_ctor_get(v___x_3843_, 1);
v_ngen_3847_ = lean_ctor_get(v___x_3843_, 2);
v_auxDeclNGen_3848_ = lean_ctor_get(v___x_3843_, 3);
v_cache_3849_ = lean_ctor_get(v___x_3843_, 5);
v_messages_3850_ = lean_ctor_get(v___x_3843_, 6);
v_infoState_3851_ = lean_ctor_get(v___x_3843_, 7);
v_snapshotTasks_3852_ = lean_ctor_get(v___x_3843_, 8);
v_isSharedCheck_3873_ = !lean_is_exclusive(v___x_3843_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3854_ = v___x_3843_;
v_isShared_3855_ = v_isSharedCheck_3873_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_snapshotTasks_3852_);
lean_inc(v_infoState_3851_);
lean_inc(v_messages_3850_);
lean_inc(v_cache_3849_);
lean_inc(v_traceState_3844_);
lean_inc(v_auxDeclNGen_3848_);
lean_inc(v_ngen_3847_);
lean_inc(v_nextMacroScope_3846_);
lean_inc(v_env_3845_);
lean_dec(v___x_3843_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3873_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
uint64_t v_tid_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3871_; 
v_tid_3856_ = lean_ctor_get_uint64(v_traceState_3844_, sizeof(void*)*1);
v_isSharedCheck_3871_ = !lean_is_exclusive(v_traceState_3844_);
if (v_isSharedCheck_3871_ == 0)
{
lean_object* v_unused_3872_; 
v_unused_3872_ = lean_ctor_get(v_traceState_3844_, 0);
lean_dec(v_unused_3872_);
v___x_3858_ = v_traceState_3844_;
v_isShared_3859_ = v_isSharedCheck_3871_;
goto v_resetjp_3857_;
}
else
{
lean_dec(v_traceState_3844_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3871_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3864_; 
v___x_3860_ = lean_unsigned_to_nat(32u);
v___x_3861_ = lean_mk_empty_array_with_capacity(v___x_3860_);
lean_dec_ref(v___x_3861_);
v___x_3862_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1);
if (v_isShared_3859_ == 0)
{
lean_ctor_set(v___x_3858_, 0, v___x_3862_);
v___x_3864_ = v___x_3858_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v___x_3862_);
lean_ctor_set_uint64(v_reuseFailAlloc_3870_, sizeof(void*)*1, v_tid_3856_);
v___x_3864_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
lean_object* v___x_3866_; 
if (v_isShared_3855_ == 0)
{
lean_ctor_set(v___x_3854_, 4, v___x_3864_);
v___x_3866_ = v___x_3854_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3869_; 
v_reuseFailAlloc_3869_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_env_3845_);
lean_ctor_set(v_reuseFailAlloc_3869_, 1, v_nextMacroScope_3846_);
lean_ctor_set(v_reuseFailAlloc_3869_, 2, v_ngen_3847_);
lean_ctor_set(v_reuseFailAlloc_3869_, 3, v_auxDeclNGen_3848_);
lean_ctor_set(v_reuseFailAlloc_3869_, 4, v___x_3864_);
lean_ctor_set(v_reuseFailAlloc_3869_, 5, v_cache_3849_);
lean_ctor_set(v_reuseFailAlloc_3869_, 6, v_messages_3850_);
lean_ctor_set(v_reuseFailAlloc_3869_, 7, v_infoState_3851_);
lean_ctor_set(v_reuseFailAlloc_3869_, 8, v_snapshotTasks_3852_);
v___x_3866_ = v_reuseFailAlloc_3869_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; 
v___x_3867_ = lean_st_ref_set(v___y_3838_, v___x_3866_);
v___x_3868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3868_, 0, v_traces_3842_);
return v___x_3868_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg___boxed(lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
lean_object* v_res_3876_; 
v_res_3876_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v___y_3874_);
lean_dec(v___y_3874_);
return v_res_3876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0(lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_){
_start:
{
lean_object* v___x_3882_; 
v___x_3882_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v___y_3880_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___boxed(lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
lean_object* v_res_3888_; 
v_res_3888_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0(v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
return v_res_3888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0(lean_object* v_a_3889_, lean_object* v___x_3890_, lean_object* v___x_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_){
_start:
{
lean_object* v___x_3899_; 
v___x_3899_ = l_Lean_Meta_Sym_shareCommon(v_a_3889_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_a_3900_);
lean_dec_ref_known(v___x_3899_, 1);
v___x_3901_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_Simp_simp___boxed), 11, 1);
lean_closure_set(v___x_3901_, 0, v_a_3900_);
v___x_3902_ = l_Lean_Meta_Sym_Simp_SimpM_run_x27___redArg(v___x_3901_, v___x_3890_, v___x_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
return v___x_3902_;
}
else
{
lean_object* v_a_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3910_; 
lean_dec_ref(v___x_3891_);
lean_dec_ref(v___x_3890_);
v_a_3903_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3910_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3910_ == 0)
{
v___x_3905_ = v___x_3899_;
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_a_3903_);
lean_dec(v___x_3899_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3910_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v___x_3908_; 
if (v_isShared_3906_ == 0)
{
v___x_3908_ = v___x_3905_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_a_3903_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
return v___x_3908_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed(lean_object* v_a_3911_, lean_object* v___x_3912_, lean_object* v___x_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_){
_start:
{
lean_object* v_res_3921_; 
v_res_3921_ = l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0(v_a_3911_, v___x_3912_, v___x_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
lean_dec(v___y_3917_);
lean_dec_ref(v___y_3916_);
lean_dec(v___y_3915_);
lean_dec_ref(v___y_3914_);
return v_res_3921_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3923_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__0));
v___x_3924_ = l_Lean_stringToMessageData(v___x_3923_);
return v___x_3924_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3(void){
_start:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; 
v___x_3926_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__2));
v___x_3927_ = l_Lean_stringToMessageData(v___x_3926_);
return v___x_3927_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5(void){
_start:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3929_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__4));
v___x_3930_ = l_Lean_stringToMessageData(v___x_3929_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1(lean_object* v_e_3931_, lean_object* v_x_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_){
_start:
{
if (lean_obj_tag(v_x_3932_) == 0)
{
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3948_; 
lean_dec_ref(v_e_3931_);
v_a_3938_ = lean_ctor_get(v_x_3932_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v_x_3932_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3940_ = v_x_3932_;
v_isShared_3941_ = v_isSharedCheck_3948_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v_x_3932_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3948_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3946_; 
v___x_3942_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__1);
v___x_3943_ = l_Lean_Exception_toMessageData(v_a_3938_);
v___x_3944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3942_);
lean_ctor_set(v___x_3944_, 1, v___x_3943_);
if (v_isShared_3941_ == 0)
{
lean_ctor_set(v___x_3940_, 0, v___x_3944_);
v___x_3946_ = v___x_3940_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3944_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
}
else
{
lean_object* v_a_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3970_; 
v_a_3949_ = lean_ctor_get(v_x_3932_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v_x_3932_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3951_ = v_x_3932_;
v_isShared_3952_ = v_isSharedCheck_3970_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_a_3949_);
lean_dec(v_x_3932_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3970_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
if (lean_obj_tag(v_a_3949_) == 0)
{
lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3957_; 
lean_dec_ref_known(v_a_3949_, 0);
v___x_3953_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__3);
v___x_3954_ = l_Lean_indentExpr(v_e_3931_);
v___x_3955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3953_);
lean_ctor_set(v___x_3955_, 1, v___x_3954_);
if (v_isShared_3952_ == 0)
{
lean_ctor_set_tag(v___x_3951_, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3955_);
v___x_3957_ = v___x_3951_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v___x_3955_);
v___x_3957_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
return v___x_3957_;
}
}
else
{
lean_object* v_e_x27_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3968_; 
v_e_x27_3959_ = lean_ctor_get(v_a_3949_, 0);
lean_inc_ref(v_e_x27_3959_);
lean_dec_ref_known(v_a_3949_, 2);
v___x_3960_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5, &l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___closed__5);
v___x_3961_ = l_Lean_indentExpr(v_e_3931_);
v___x_3962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3960_);
lean_ctor_set(v___x_3962_, 1, v___x_3961_);
v___x_3963_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_3964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3962_);
lean_ctor_set(v___x_3964_, 1, v___x_3963_);
v___x_3965_ = l_Lean_indentExpr(v_e_x27_3959_);
v___x_3966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3966_, 0, v___x_3964_);
lean_ctor_set(v___x_3966_, 1, v___x_3965_);
if (v_isShared_3952_ == 0)
{
lean_ctor_set_tag(v___x_3951_, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3966_);
v___x_3968_ = v___x_3951_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v___x_3966_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___boxed(lean_object* v_e_3971_, lean_object* v_x_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_){
_start:
{
lean_object* v_res_3978_; 
v_res_3978_ = l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1(v_e_3971_, v_x_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
return v_res_3978_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(lean_object* v_x_3979_){
_start:
{
if (lean_obj_tag(v_x_3979_) == 0)
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
v_a_3981_ = lean_ctor_get(v_x_3979_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v_x_3979_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v_x_3979_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v_x_3979_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
lean_ctor_set_tag(v___x_3983_, 1);
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3981_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
else
{
lean_object* v_a_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_3996_; 
v_a_3989_ = lean_ctor_get(v_x_3979_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v_x_3979_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3991_ = v_x_3979_;
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_a_3989_);
lean_dec(v_x_3979_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3994_; 
if (v_isShared_3992_ == 0)
{
lean_ctor_set_tag(v___x_3991_, 0);
v___x_3994_ = v___x_3991_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_a_3989_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg___boxed(lean_object* v_x_3997_, lean_object* v___y_3998_){
_start:
{
lean_object* v_res_3999_; 
v_res_3999_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_x_3997_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(lean_object* v_oldTraces_4000_, lean_object* v_data_4001_, lean_object* v_ref_4002_, lean_object* v_msg_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_){
_start:
{
lean_object* v_fileName_4009_; lean_object* v_fileMap_4010_; lean_object* v_options_4011_; lean_object* v_currRecDepth_4012_; lean_object* v_maxRecDepth_4013_; lean_object* v_ref_4014_; lean_object* v_currNamespace_4015_; lean_object* v_openDecls_4016_; lean_object* v_initHeartbeats_4017_; lean_object* v_maxHeartbeats_4018_; lean_object* v_quotContext_4019_; lean_object* v_currMacroScope_4020_; uint8_t v_diag_4021_; lean_object* v_cancelTk_x3f_4022_; uint8_t v_suppressElabErrors_4023_; lean_object* v_inheritedTraceOptions_4024_; lean_object* v___x_4025_; lean_object* v_traceState_4026_; lean_object* v_traces_4027_; lean_object* v_ref_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; size_t v_sz_4031_; size_t v___x_4032_; lean_object* v___x_4033_; lean_object* v_msg_4034_; lean_object* v___x_4035_; lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4073_; 
v_fileName_4009_ = lean_ctor_get(v___y_4006_, 0);
v_fileMap_4010_ = lean_ctor_get(v___y_4006_, 1);
v_options_4011_ = lean_ctor_get(v___y_4006_, 2);
v_currRecDepth_4012_ = lean_ctor_get(v___y_4006_, 3);
v_maxRecDepth_4013_ = lean_ctor_get(v___y_4006_, 4);
v_ref_4014_ = lean_ctor_get(v___y_4006_, 5);
v_currNamespace_4015_ = lean_ctor_get(v___y_4006_, 6);
v_openDecls_4016_ = lean_ctor_get(v___y_4006_, 7);
v_initHeartbeats_4017_ = lean_ctor_get(v___y_4006_, 8);
v_maxHeartbeats_4018_ = lean_ctor_get(v___y_4006_, 9);
v_quotContext_4019_ = lean_ctor_get(v___y_4006_, 10);
v_currMacroScope_4020_ = lean_ctor_get(v___y_4006_, 11);
v_diag_4021_ = lean_ctor_get_uint8(v___y_4006_, sizeof(void*)*14);
v_cancelTk_x3f_4022_ = lean_ctor_get(v___y_4006_, 12);
v_suppressElabErrors_4023_ = lean_ctor_get_uint8(v___y_4006_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4024_ = lean_ctor_get(v___y_4006_, 13);
v___x_4025_ = lean_st_ref_get(v___y_4007_);
v_traceState_4026_ = lean_ctor_get(v___x_4025_, 4);
lean_inc_ref(v_traceState_4026_);
lean_dec(v___x_4025_);
v_traces_4027_ = lean_ctor_get(v_traceState_4026_, 0);
lean_inc_ref(v_traces_4027_);
lean_dec_ref(v_traceState_4026_);
v_ref_4028_ = l_Lean_replaceRef(v_ref_4002_, v_ref_4014_);
lean_inc_ref(v_inheritedTraceOptions_4024_);
lean_inc(v_cancelTk_x3f_4022_);
lean_inc(v_currMacroScope_4020_);
lean_inc(v_quotContext_4019_);
lean_inc(v_maxHeartbeats_4018_);
lean_inc(v_initHeartbeats_4017_);
lean_inc(v_openDecls_4016_);
lean_inc(v_currNamespace_4015_);
lean_inc(v_maxRecDepth_4013_);
lean_inc(v_currRecDepth_4012_);
lean_inc_ref(v_options_4011_);
lean_inc_ref(v_fileMap_4010_);
lean_inc_ref(v_fileName_4009_);
v___x_4029_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4029_, 0, v_fileName_4009_);
lean_ctor_set(v___x_4029_, 1, v_fileMap_4010_);
lean_ctor_set(v___x_4029_, 2, v_options_4011_);
lean_ctor_set(v___x_4029_, 3, v_currRecDepth_4012_);
lean_ctor_set(v___x_4029_, 4, v_maxRecDepth_4013_);
lean_ctor_set(v___x_4029_, 5, v_ref_4028_);
lean_ctor_set(v___x_4029_, 6, v_currNamespace_4015_);
lean_ctor_set(v___x_4029_, 7, v_openDecls_4016_);
lean_ctor_set(v___x_4029_, 8, v_initHeartbeats_4017_);
lean_ctor_set(v___x_4029_, 9, v_maxHeartbeats_4018_);
lean_ctor_set(v___x_4029_, 10, v_quotContext_4019_);
lean_ctor_set(v___x_4029_, 11, v_currMacroScope_4020_);
lean_ctor_set(v___x_4029_, 12, v_cancelTk_x3f_4022_);
lean_ctor_set(v___x_4029_, 13, v_inheritedTraceOptions_4024_);
lean_ctor_set_uint8(v___x_4029_, sizeof(void*)*14, v_diag_4021_);
lean_ctor_set_uint8(v___x_4029_, sizeof(void*)*14 + 1, v_suppressElabErrors_4023_);
v___x_4030_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4027_);
lean_dec_ref(v_traces_4027_);
v_sz_4031_ = lean_array_size(v___x_4030_);
v___x_4032_ = ((size_t)0ULL);
v___x_4033_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5(v_sz_4031_, v___x_4032_, v___x_4030_);
v_msg_4034_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4034_, 0, v_data_4001_);
lean_ctor_set(v_msg_4034_, 1, v_msg_4003_);
lean_ctor_set(v_msg_4034_, 2, v___x_4033_);
v___x_4035_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_4034_, v___y_4004_, v___y_4005_, v___x_4029_, v___y_4007_);
lean_dec_ref_known(v___x_4029_, 14);
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4073_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4073_ == 0)
{
v___x_4038_ = v___x_4035_;
v_isShared_4039_ = v_isSharedCheck_4073_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_4035_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4073_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4040_; lean_object* v_traceState_4041_; lean_object* v_env_4042_; lean_object* v_nextMacroScope_4043_; lean_object* v_ngen_4044_; lean_object* v_auxDeclNGen_4045_; lean_object* v_cache_4046_; lean_object* v_messages_4047_; lean_object* v_infoState_4048_; lean_object* v_snapshotTasks_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4072_; 
v___x_4040_ = lean_st_ref_take(v___y_4007_);
v_traceState_4041_ = lean_ctor_get(v___x_4040_, 4);
v_env_4042_ = lean_ctor_get(v___x_4040_, 0);
v_nextMacroScope_4043_ = lean_ctor_get(v___x_4040_, 1);
v_ngen_4044_ = lean_ctor_get(v___x_4040_, 2);
v_auxDeclNGen_4045_ = lean_ctor_get(v___x_4040_, 3);
v_cache_4046_ = lean_ctor_get(v___x_4040_, 5);
v_messages_4047_ = lean_ctor_get(v___x_4040_, 6);
v_infoState_4048_ = lean_ctor_get(v___x_4040_, 7);
v_snapshotTasks_4049_ = lean_ctor_get(v___x_4040_, 8);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4040_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4051_ = v___x_4040_;
v_isShared_4052_ = v_isSharedCheck_4072_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_snapshotTasks_4049_);
lean_inc(v_infoState_4048_);
lean_inc(v_messages_4047_);
lean_inc(v_cache_4046_);
lean_inc(v_traceState_4041_);
lean_inc(v_auxDeclNGen_4045_);
lean_inc(v_ngen_4044_);
lean_inc(v_nextMacroScope_4043_);
lean_inc(v_env_4042_);
lean_dec(v___x_4040_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4072_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
uint64_t v_tid_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4070_; 
v_tid_4053_ = lean_ctor_get_uint64(v_traceState_4041_, sizeof(void*)*1);
v_isSharedCheck_4070_ = !lean_is_exclusive(v_traceState_4041_);
if (v_isSharedCheck_4070_ == 0)
{
lean_object* v_unused_4071_; 
v_unused_4071_ = lean_ctor_get(v_traceState_4041_, 0);
lean_dec(v_unused_4071_);
v___x_4055_ = v_traceState_4041_;
v_isShared_4056_ = v_isSharedCheck_4070_;
goto v_resetjp_4054_;
}
else
{
lean_dec(v_traceState_4041_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4070_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4060_; 
v___x_4057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4057_, 0, v_ref_4002_);
lean_ctor_set(v___x_4057_, 1, v_a_4036_);
v___x_4058_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4000_, v___x_4057_);
if (v_isShared_4056_ == 0)
{
lean_ctor_set(v___x_4055_, 0, v___x_4058_);
v___x_4060_ = v___x_4055_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4069_; 
v_reuseFailAlloc_4069_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4069_, 0, v___x_4058_);
lean_ctor_set_uint64(v_reuseFailAlloc_4069_, sizeof(void*)*1, v_tid_4053_);
v___x_4060_ = v_reuseFailAlloc_4069_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
lean_object* v___x_4062_; 
if (v_isShared_4052_ == 0)
{
lean_ctor_set(v___x_4051_, 4, v___x_4060_);
v___x_4062_ = v___x_4051_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_env_4042_);
lean_ctor_set(v_reuseFailAlloc_4068_, 1, v_nextMacroScope_4043_);
lean_ctor_set(v_reuseFailAlloc_4068_, 2, v_ngen_4044_);
lean_ctor_set(v_reuseFailAlloc_4068_, 3, v_auxDeclNGen_4045_);
lean_ctor_set(v_reuseFailAlloc_4068_, 4, v___x_4060_);
lean_ctor_set(v_reuseFailAlloc_4068_, 5, v_cache_4046_);
lean_ctor_set(v_reuseFailAlloc_4068_, 6, v_messages_4047_);
lean_ctor_set(v_reuseFailAlloc_4068_, 7, v_infoState_4048_);
lean_ctor_set(v_reuseFailAlloc_4068_, 8, v_snapshotTasks_4049_);
v___x_4062_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4066_; 
v___x_4063_ = lean_st_ref_set(v___y_4007_, v___x_4062_);
v___x_4064_ = lean_box(0);
if (v_isShared_4039_ == 0)
{
lean_ctor_set(v___x_4038_, 0, v___x_4064_);
v___x_4066_ = v___x_4038_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v___x_4064_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1___boxed(lean_object* v_oldTraces_4074_, lean_object* v_data_4075_, lean_object* v_ref_4076_, lean_object* v_msg_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
lean_object* v_res_4083_; 
v_res_4083_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(v_oldTraces_4074_, v_data_4075_, v_ref_4076_, v_msg_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
lean_dec(v___y_4081_);
lean_dec_ref(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
return v_res_4083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(lean_object* v_cls_4084_, uint8_t v_collapsed_4085_, lean_object* v_tag_4086_, lean_object* v_opts_4087_, uint8_t v_clsEnabled_4088_, lean_object* v_oldTraces_4089_, lean_object* v_msg_4090_, lean_object* v_resStartStop_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_){
_start:
{
lean_object* v_fst_4097_; lean_object* v_snd_4098_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v_data_4102_; lean_object* v_fst_4113_; lean_object* v_snd_4114_; lean_object* v___x_4115_; uint8_t v___x_4116_; lean_object* v___y_4118_; lean_object* v_a_4119_; uint8_t v___y_4134_; double v___y_4165_; 
v_fst_4097_ = lean_ctor_get(v_resStartStop_4091_, 0);
lean_inc(v_fst_4097_);
v_snd_4098_ = lean_ctor_get(v_resStartStop_4091_, 1);
lean_inc(v_snd_4098_);
lean_dec_ref(v_resStartStop_4091_);
v_fst_4113_ = lean_ctor_get(v_snd_4098_, 0);
lean_inc(v_fst_4113_);
v_snd_4114_ = lean_ctor_get(v_snd_4098_, 1);
lean_inc(v_snd_4114_);
lean_dec(v_snd_4098_);
v___x_4115_ = l_Lean_trace_profiler;
v___x_4116_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4087_, v___x_4115_);
if (v___x_4116_ == 0)
{
v___y_4134_ = v___x_4116_;
goto v___jp_4133_;
}
else
{
lean_object* v___x_4170_; uint8_t v___x_4171_; 
v___x_4170_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4171_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4087_, v___x_4170_);
if (v___x_4171_ == 0)
{
lean_object* v___x_4172_; lean_object* v___x_4173_; double v___x_4174_; double v___x_4175_; double v___x_4176_; 
v___x_4172_ = l_Lean_trace_profiler_threshold;
v___x_4173_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4087_, v___x_4172_);
v___x_4174_ = lean_float_of_nat(v___x_4173_);
v___x_4175_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2);
v___x_4176_ = lean_float_div(v___x_4174_, v___x_4175_);
v___y_4165_ = v___x_4176_;
goto v___jp_4164_;
}
else
{
lean_object* v___x_4177_; lean_object* v___x_4178_; double v___x_4179_; 
v___x_4177_ = l_Lean_trace_profiler_threshold;
v___x_4178_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4087_, v___x_4177_);
v___x_4179_ = lean_float_of_nat(v___x_4178_);
v___y_4165_ = v___x_4179_;
goto v___jp_4164_;
}
}
v___jp_4099_:
{
lean_object* v___x_4103_; 
lean_inc(v___y_4100_);
v___x_4103_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(v_oldTraces_4089_, v_data_4102_, v___y_4100_, v___y_4101_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_);
if (lean_obj_tag(v___x_4103_) == 0)
{
lean_object* v___x_4104_; 
lean_dec_ref_known(v___x_4103_, 1);
v___x_4104_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_4097_);
return v___x_4104_;
}
else
{
lean_object* v_a_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4112_; 
lean_dec(v_fst_4097_);
v_a_4105_ = lean_ctor_get(v___x_4103_, 0);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4107_ = v___x_4103_;
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_a_4105_);
lean_dec(v___x_4103_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4110_; 
if (v_isShared_4108_ == 0)
{
v___x_4110_ = v___x_4107_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_a_4105_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
}
}
v___jp_4117_:
{
uint8_t v_result_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; double v___x_4123_; lean_object* v_data_4124_; 
v_result_4120_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(v_fst_4097_);
v___x_4121_ = lean_box(v_result_4120_);
v___x_4122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4121_);
v___x_4123_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_4086_);
lean_inc_ref(v___x_4122_);
lean_inc(v_cls_4084_);
v_data_4124_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4124_, 0, v_cls_4084_);
lean_ctor_set(v_data_4124_, 1, v___x_4122_);
lean_ctor_set(v_data_4124_, 2, v_tag_4086_);
lean_ctor_set_float(v_data_4124_, sizeof(void*)*3, v___x_4123_);
lean_ctor_set_float(v_data_4124_, sizeof(void*)*3 + 8, v___x_4123_);
lean_ctor_set_uint8(v_data_4124_, sizeof(void*)*3 + 16, v_collapsed_4085_);
if (v___x_4116_ == 0)
{
lean_dec_ref_known(v___x_4122_, 1);
lean_dec(v_snd_4114_);
lean_dec(v_fst_4113_);
lean_dec_ref(v_tag_4086_);
lean_dec(v_cls_4084_);
v___y_4100_ = v___y_4118_;
v___y_4101_ = v_a_4119_;
v_data_4102_ = v_data_4124_;
goto v___jp_4099_;
}
else
{
lean_object* v_data_4125_; double v___x_4126_; double v___x_4127_; 
lean_dec_ref_known(v_data_4124_, 3);
v_data_4125_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4125_, 0, v_cls_4084_);
lean_ctor_set(v_data_4125_, 1, v___x_4122_);
lean_ctor_set(v_data_4125_, 2, v_tag_4086_);
v___x_4126_ = lean_unbox_float(v_fst_4113_);
lean_dec(v_fst_4113_);
lean_ctor_set_float(v_data_4125_, sizeof(void*)*3, v___x_4126_);
v___x_4127_ = lean_unbox_float(v_snd_4114_);
lean_dec(v_snd_4114_);
lean_ctor_set_float(v_data_4125_, sizeof(void*)*3 + 8, v___x_4127_);
lean_ctor_set_uint8(v_data_4125_, sizeof(void*)*3 + 16, v_collapsed_4085_);
v___y_4100_ = v___y_4118_;
v___y_4101_ = v_a_4119_;
v_data_4102_ = v_data_4125_;
goto v___jp_4099_;
}
}
v___jp_4128_:
{
lean_object* v_ref_4129_; lean_object* v___x_4130_; 
v_ref_4129_ = lean_ctor_get(v___y_4094_, 5);
lean_inc(v___y_4095_);
lean_inc_ref(v___y_4094_);
lean_inc(v___y_4093_);
lean_inc_ref(v___y_4092_);
lean_inc(v_fst_4097_);
v___x_4130_ = lean_apply_6(v_msg_4090_, v_fst_4097_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, lean_box(0));
if (lean_obj_tag(v___x_4130_) == 0)
{
lean_object* v_a_4131_; 
v_a_4131_ = lean_ctor_get(v___x_4130_, 0);
lean_inc(v_a_4131_);
lean_dec_ref_known(v___x_4130_, 1);
v___y_4118_ = v_ref_4129_;
v_a_4119_ = v_a_4131_;
goto v___jp_4117_;
}
else
{
lean_object* v___x_4132_; 
lean_dec_ref_known(v___x_4130_, 1);
v___x_4132_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
v___y_4118_ = v_ref_4129_;
v_a_4119_ = v___x_4132_;
goto v___jp_4117_;
}
}
v___jp_4133_:
{
if (v_clsEnabled_4088_ == 0)
{
if (v___y_4134_ == 0)
{
lean_object* v___x_4135_; lean_object* v_traceState_4136_; lean_object* v_env_4137_; lean_object* v_nextMacroScope_4138_; lean_object* v_ngen_4139_; lean_object* v_auxDeclNGen_4140_; lean_object* v_cache_4141_; lean_object* v_messages_4142_; lean_object* v_infoState_4143_; lean_object* v_snapshotTasks_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4163_; 
lean_dec(v_snd_4114_);
lean_dec(v_fst_4113_);
lean_dec_ref(v_msg_4090_);
lean_dec_ref(v_tag_4086_);
lean_dec(v_cls_4084_);
v___x_4135_ = lean_st_ref_take(v___y_4095_);
v_traceState_4136_ = lean_ctor_get(v___x_4135_, 4);
v_env_4137_ = lean_ctor_get(v___x_4135_, 0);
v_nextMacroScope_4138_ = lean_ctor_get(v___x_4135_, 1);
v_ngen_4139_ = lean_ctor_get(v___x_4135_, 2);
v_auxDeclNGen_4140_ = lean_ctor_get(v___x_4135_, 3);
v_cache_4141_ = lean_ctor_get(v___x_4135_, 5);
v_messages_4142_ = lean_ctor_get(v___x_4135_, 6);
v_infoState_4143_ = lean_ctor_get(v___x_4135_, 7);
v_snapshotTasks_4144_ = lean_ctor_get(v___x_4135_, 8);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4146_ = v___x_4135_;
v_isShared_4147_ = v_isSharedCheck_4163_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_snapshotTasks_4144_);
lean_inc(v_infoState_4143_);
lean_inc(v_messages_4142_);
lean_inc(v_cache_4141_);
lean_inc(v_traceState_4136_);
lean_inc(v_auxDeclNGen_4140_);
lean_inc(v_ngen_4139_);
lean_inc(v_nextMacroScope_4138_);
lean_inc(v_env_4137_);
lean_dec(v___x_4135_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4163_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
uint64_t v_tid_4148_; lean_object* v_traces_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4162_; 
v_tid_4148_ = lean_ctor_get_uint64(v_traceState_4136_, sizeof(void*)*1);
v_traces_4149_ = lean_ctor_get(v_traceState_4136_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v_traceState_4136_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4151_ = v_traceState_4136_;
v_isShared_4152_ = v_isSharedCheck_4162_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_traces_4149_);
lean_dec(v_traceState_4136_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4162_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4153_; lean_object* v___x_4155_; 
v___x_4153_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4089_, v_traces_4149_);
lean_dec_ref(v_traces_4149_);
if (v_isShared_4152_ == 0)
{
lean_ctor_set(v___x_4151_, 0, v___x_4153_);
v___x_4155_ = v___x_4151_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v___x_4153_);
lean_ctor_set_uint64(v_reuseFailAlloc_4161_, sizeof(void*)*1, v_tid_4148_);
v___x_4155_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
lean_object* v___x_4157_; 
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 4, v___x_4155_);
v___x_4157_ = v___x_4146_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_env_4137_);
lean_ctor_set(v_reuseFailAlloc_4160_, 1, v_nextMacroScope_4138_);
lean_ctor_set(v_reuseFailAlloc_4160_, 2, v_ngen_4139_);
lean_ctor_set(v_reuseFailAlloc_4160_, 3, v_auxDeclNGen_4140_);
lean_ctor_set(v_reuseFailAlloc_4160_, 4, v___x_4155_);
lean_ctor_set(v_reuseFailAlloc_4160_, 5, v_cache_4141_);
lean_ctor_set(v_reuseFailAlloc_4160_, 6, v_messages_4142_);
lean_ctor_set(v_reuseFailAlloc_4160_, 7, v_infoState_4143_);
lean_ctor_set(v_reuseFailAlloc_4160_, 8, v_snapshotTasks_4144_);
v___x_4157_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
lean_object* v___x_4158_; lean_object* v___x_4159_; 
v___x_4158_ = lean_st_ref_set(v___y_4095_, v___x_4157_);
v___x_4159_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_4097_);
return v___x_4159_;
}
}
}
}
}
else
{
goto v___jp_4128_;
}
}
else
{
goto v___jp_4128_;
}
}
v___jp_4164_:
{
double v___x_4166_; double v___x_4167_; double v___x_4168_; uint8_t v___x_4169_; 
v___x_4166_ = lean_unbox_float(v_snd_4114_);
v___x_4167_ = lean_unbox_float(v_fst_4113_);
v___x_4168_ = lean_float_sub(v___x_4166_, v___x_4167_);
v___x_4169_ = lean_float_decLt(v___y_4165_, v___x_4168_);
v___y_4134_ = v___x_4169_;
goto v___jp_4133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1___boxed(lean_object* v_cls_4180_, lean_object* v_collapsed_4181_, lean_object* v_tag_4182_, lean_object* v_opts_4183_, lean_object* v_clsEnabled_4184_, lean_object* v_oldTraces_4185_, lean_object* v_msg_4186_, lean_object* v_resStartStop_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_){
_start:
{
uint8_t v_collapsed_boxed_4193_; uint8_t v_clsEnabled_boxed_4194_; lean_object* v_res_4195_; 
v_collapsed_boxed_4193_ = lean_unbox(v_collapsed_4181_);
v_clsEnabled_boxed_4194_ = lean_unbox(v_clsEnabled_4184_);
v_res_4195_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(v_cls_4180_, v_collapsed_boxed_4193_, v_tag_4182_, v_opts_4183_, v_clsEnabled_boxed_4194_, v_oldTraces_4185_, v_msg_4186_, v_resStartStop_4187_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_);
lean_dec(v___y_4191_);
lean_dec_ref(v___y_4190_);
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
lean_dec_ref(v_opts_4183_);
return v_res_4195_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1(void){
_start:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; 
v___x_4200_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_4201_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
v___x_4202_ = l_Lean_Name_append(v___x_4201_, v___x_4200_);
return v___x_4202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry(lean_object* v_e_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_){
_start:
{
lean_object* v_options_4209_; uint8_t v_hasTrace_4210_; 
v_options_4209_ = lean_ctor_get(v_a_4206_, 2);
v_hasTrace_4210_ = lean_ctor_get_uint8(v_options_4209_, sizeof(void*)*1);
if (v_hasTrace_4210_ == 0)
{
lean_object* v___x_4211_; 
v___x_4211_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4207_);
if (lean_obj_tag(v___x_4211_) == 0)
{
lean_object* v_a_4212_; lean_object* v___x_4213_; 
v_a_4212_ = lean_ctor_get(v___x_4211_, 0);
lean_inc(v_a_4212_);
lean_dec_ref_known(v___x_4211_, 1);
v___x_4213_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_);
if (lean_obj_tag(v___x_4213_) == 0)
{
lean_object* v_a_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___f_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; 
v_a_4214_ = lean_ctor_get(v___x_4213_, 0);
lean_inc(v_a_4214_);
lean_dec_ref_known(v___x_4213_, 1);
v___x_4215_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4216_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4209_, v___x_4215_);
v___x_4217_ = lean_unsigned_to_nat(2u);
v___x_4218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4218_, 0, v___x_4216_);
lean_ctor_set(v___x_4218_, 1, v___x_4217_);
v___x_4219_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4212_);
v___f_4220_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4220_, 0, v_a_4214_);
lean_closure_set(v___f_4220_, 1, v___x_4219_);
lean_closure_set(v___f_4220_, 2, v___x_4218_);
v___x_4221_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_4221_, 0, lean_box(0));
lean_closure_set(v___x_4221_, 1, v___f_4220_);
v___x_4222_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_4221_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_);
return v___x_4222_;
}
else
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4230_; 
lean_dec(v_a_4212_);
v_a_4223_ = lean_ctor_get(v___x_4213_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_4213_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4225_ = v___x_4213_;
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4213_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4228_; 
if (v_isShared_4226_ == 0)
{
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
return v___x_4228_;
}
}
}
}
else
{
lean_object* v_a_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4238_; 
lean_dec_ref(v_e_4203_);
v_a_4231_ = lean_ctor_get(v___x_4211_, 0);
v_isSharedCheck_4238_ = !lean_is_exclusive(v___x_4211_);
if (v_isSharedCheck_4238_ == 0)
{
v___x_4233_ = v___x_4211_;
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_a_4231_);
lean_dec(v___x_4211_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___x_4236_; 
if (v_isShared_4234_ == 0)
{
v___x_4236_ = v___x_4233_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_a_4231_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_4239_; lean_object* v___f_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; uint8_t v___x_4244_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v_a_4248_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v_a_4263_; lean_object* v___y_4266_; lean_object* v___y_4267_; lean_object* v_a_4268_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v_a_4280_; 
v_inheritedTraceOptions_4239_ = lean_ctor_get(v_a_4206_, 13);
lean_inc_ref(v_e_4203_);
v___f_4240_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__1___boxed), 7, 1);
lean_closure_set(v___f_4240_, 0, v_e_4203_);
v___x_4241_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_4242_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_4243_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_4244_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4239_, v_options_4209_, v___x_4243_);
if (v___x_4244_ == 0)
{
lean_object* v___x_4335_; uint8_t v___x_4336_; 
v___x_4335_ = l_Lean_trace_profiler;
v___x_4336_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_4209_, v___x_4335_);
if (v___x_4336_ == 0)
{
lean_object* v___x_4337_; 
lean_dec_ref(v___f_4240_);
v___x_4337_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4207_);
if (lean_obj_tag(v___x_4337_) == 0)
{
lean_object* v_a_4338_; lean_object* v___x_4339_; 
v_a_4338_ = lean_ctor_get(v___x_4337_, 0);
lean_inc(v_a_4338_);
lean_dec_ref_known(v___x_4337_, 1);
v___x_4339_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_);
if (lean_obj_tag(v___x_4339_) == 0)
{
lean_object* v_a_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___f_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; 
v_a_4340_ = lean_ctor_get(v___x_4339_, 0);
lean_inc(v_a_4340_);
lean_dec_ref_known(v___x_4339_, 1);
v___x_4341_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4342_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4209_, v___x_4341_);
v___x_4343_ = lean_unsigned_to_nat(2u);
v___x_4344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4344_, 0, v___x_4342_);
lean_ctor_set(v___x_4344_, 1, v___x_4343_);
v___x_4345_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4338_);
v___f_4346_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4346_, 0, v_a_4340_);
lean_closure_set(v___f_4346_, 1, v___x_4345_);
lean_closure_set(v___f_4346_, 2, v___x_4344_);
v___x_4347_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_4347_, 0, lean_box(0));
lean_closure_set(v___x_4347_, 1, v___f_4346_);
v___x_4348_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_4347_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_);
return v___x_4348_;
}
else
{
lean_object* v_a_4349_; lean_object* v___x_4351_; uint8_t v_isShared_4352_; uint8_t v_isSharedCheck_4356_; 
lean_dec(v_a_4338_);
v_a_4349_ = lean_ctor_get(v___x_4339_, 0);
v_isSharedCheck_4356_ = !lean_is_exclusive(v___x_4339_);
if (v_isSharedCheck_4356_ == 0)
{
v___x_4351_ = v___x_4339_;
v_isShared_4352_ = v_isSharedCheck_4356_;
goto v_resetjp_4350_;
}
else
{
lean_inc(v_a_4349_);
lean_dec(v___x_4339_);
v___x_4351_ = lean_box(0);
v_isShared_4352_ = v_isSharedCheck_4356_;
goto v_resetjp_4350_;
}
v_resetjp_4350_:
{
lean_object* v___x_4354_; 
if (v_isShared_4352_ == 0)
{
v___x_4354_ = v___x_4351_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v_a_4349_);
v___x_4354_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
return v___x_4354_;
}
}
}
}
else
{
lean_object* v_a_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4364_; 
lean_dec_ref(v_e_4203_);
v_a_4357_ = lean_ctor_get(v___x_4337_, 0);
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4337_);
if (v_isSharedCheck_4364_ == 0)
{
v___x_4359_ = v___x_4337_;
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_a_4357_);
lean_dec(v___x_4337_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
lean_object* v___x_4362_; 
if (v_isShared_4360_ == 0)
{
v___x_4362_ = v___x_4359_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v_a_4357_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
return v___x_4362_;
}
}
}
}
else
{
goto v___jp_4282_;
}
}
else
{
goto v___jp_4282_;
}
v___jp_4245_:
{
lean_object* v___x_4249_; double v___x_4250_; double v___x_4251_; double v___x_4252_; double v___x_4253_; double v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; 
v___x_4249_ = lean_io_mono_nanos_now();
v___x_4250_ = lean_float_of_nat(v___y_4247_);
v___x_4251_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_4252_ = lean_float_div(v___x_4250_, v___x_4251_);
v___x_4253_ = lean_float_of_nat(v___x_4249_);
v___x_4254_ = lean_float_div(v___x_4253_, v___x_4251_);
v___x_4255_ = lean_box_float(v___x_4252_);
v___x_4256_ = lean_box_float(v___x_4254_);
v___x_4257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4257_, 0, v___x_4255_);
lean_ctor_set(v___x_4257_, 1, v___x_4256_);
v___x_4258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4258_, 0, v_a_4248_);
lean_ctor_set(v___x_4258_, 1, v___x_4257_);
v___x_4259_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(v___x_4241_, v_hasTrace_4210_, v___x_4242_, v_options_4209_, v___x_4244_, v___y_4246_, v___f_4240_, v___x_4258_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_);
return v___x_4259_;
}
v___jp_4260_:
{
lean_object* v___x_4264_; 
v___x_4264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4264_, 0, v_a_4263_);
v___y_4246_ = v___y_4261_;
v___y_4247_ = v___y_4262_;
v_a_4248_ = v___x_4264_;
goto v___jp_4245_;
}
v___jp_4265_:
{
lean_object* v___x_4269_; double v___x_4270_; double v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; 
v___x_4269_ = lean_io_get_num_heartbeats();
v___x_4270_ = lean_float_of_nat(v___y_4267_);
v___x_4271_ = lean_float_of_nat(v___x_4269_);
v___x_4272_ = lean_box_float(v___x_4270_);
v___x_4273_ = lean_box_float(v___x_4271_);
v___x_4274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4274_, 0, v___x_4272_);
lean_ctor_set(v___x_4274_, 1, v___x_4273_);
v___x_4275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4275_, 0, v_a_4268_);
lean_ctor_set(v___x_4275_, 1, v___x_4274_);
v___x_4276_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1(v___x_4241_, v_hasTrace_4210_, v___x_4242_, v_options_4209_, v___x_4244_, v___y_4266_, v___f_4240_, v___x_4275_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_);
return v___x_4276_;
}
v___jp_4277_:
{
lean_object* v___x_4281_; 
v___x_4281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4281_, 0, v_a_4280_);
v___y_4266_ = v___y_4278_;
v___y_4267_ = v___y_4279_;
v_a_4268_ = v___x_4281_;
goto v___jp_4265_;
}
v___jp_4282_:
{
lean_object* v___x_4283_; lean_object* v_a_4284_; lean_object* v___x_4285_; uint8_t v___x_4286_; 
v___x_4283_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v_a_4207_);
v_a_4284_ = lean_ctor_get(v___x_4283_, 0);
lean_inc(v_a_4284_);
lean_dec_ref(v___x_4283_);
v___x_4285_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4286_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_4209_, v___x_4285_);
if (v___x_4286_ == 0)
{
lean_object* v___x_4287_; lean_object* v___x_4288_; 
v___x_4287_ = lean_io_mono_nanos_now();
v___x_4288_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4207_);
if (lean_obj_tag(v___x_4288_) == 0)
{
lean_object* v_a_4289_; lean_object* v___x_4290_; 
v_a_4289_ = lean_ctor_get(v___x_4288_, 0);
lean_inc(v_a_4289_);
lean_dec_ref_known(v___x_4288_, 1);
v___x_4290_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_);
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_object* v_a_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___f_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; 
v_a_4291_ = lean_ctor_get(v___x_4290_, 0);
lean_inc(v_a_4291_);
lean_dec_ref_known(v___x_4290_, 1);
v___x_4292_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4293_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4209_, v___x_4292_);
v___x_4294_ = lean_unsigned_to_nat(2u);
v___x_4295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4295_, 0, v___x_4293_);
lean_ctor_set(v___x_4295_, 1, v___x_4294_);
v___x_4296_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4289_);
v___f_4297_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4297_, 0, v_a_4291_);
lean_closure_set(v___f_4297_, 1, v___x_4296_);
lean_closure_set(v___f_4297_, 2, v___x_4295_);
v___x_4298_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_4298_, 0, lean_box(0));
lean_closure_set(v___x_4298_, 1, v___f_4297_);
v___x_4299_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_4298_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4307_; 
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4302_ = v___x_4299_;
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4299_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4305_; 
if (v_isShared_4303_ == 0)
{
lean_ctor_set_tag(v___x_4302_, 1);
v___x_4305_ = v___x_4302_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_a_4300_);
v___x_4305_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
v___y_4246_ = v_a_4284_;
v___y_4247_ = v___x_4287_;
v_a_4248_ = v___x_4305_;
goto v___jp_4245_;
}
}
}
else
{
lean_object* v_a_4308_; 
v_a_4308_ = lean_ctor_get(v___x_4299_, 0);
lean_inc(v_a_4308_);
lean_dec_ref_known(v___x_4299_, 1);
v___y_4261_ = v_a_4284_;
v___y_4262_ = v___x_4287_;
v_a_4263_ = v_a_4308_;
goto v___jp_4260_;
}
}
else
{
lean_object* v_a_4309_; 
lean_dec(v_a_4289_);
v_a_4309_ = lean_ctor_get(v___x_4290_, 0);
lean_inc(v_a_4309_);
lean_dec_ref_known(v___x_4290_, 1);
v___y_4261_ = v_a_4284_;
v___y_4262_ = v___x_4287_;
v_a_4263_ = v_a_4309_;
goto v___jp_4260_;
}
}
else
{
lean_object* v_a_4310_; 
lean_dec_ref(v_e_4203_);
v_a_4310_ = lean_ctor_get(v___x_4288_, 0);
lean_inc(v_a_4310_);
lean_dec_ref_known(v___x_4288_, 1);
v___y_4261_ = v_a_4284_;
v___y_4262_ = v___x_4287_;
v_a_4263_ = v_a_4310_;
goto v___jp_4260_;
}
}
else
{
lean_object* v___x_4311_; lean_object* v___x_4312_; 
v___x_4311_ = lean_io_get_num_heartbeats();
v___x_4312_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_4207_);
if (lean_obj_tag(v___x_4312_) == 0)
{
lean_object* v_a_4313_; lean_object* v___x_4314_; 
v_a_4313_ = lean_ctor_get(v___x_4312_, 0);
lean_inc(v_a_4313_);
lean_dec_ref_known(v___x_4312_, 1);
v___x_4314_ = l_Lean_Meta_Sym_unfoldReducible(v_e_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v_a_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___f_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; 
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
lean_inc(v_a_4315_);
lean_dec_ref_known(v___x_4314_, 1);
v___x_4316_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_4317_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_4209_, v___x_4316_);
v___x_4318_ = lean_unsigned_to_nat(2u);
v___x_4319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4319_, 0, v___x_4317_);
lean_ctor_set(v___x_4319_, 1, v___x_4318_);
v___x_4320_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_mkCbvMethods(v_a_4313_);
v___f_4321_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4321_, 0, v_a_4315_);
lean_closure_set(v___f_4321_, 1, v___x_4320_);
lean_closure_set(v___f_4321_, 2, v___x_4319_);
v___x_4322_ = lean_alloc_closure((void*)(l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_4322_, 0, lean_box(0));
lean_closure_set(v___x_4322_, 1, v___f_4321_);
v___x_4323_ = l_Lean_Meta_Sym_SymM_run___redArg(v___x_4322_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_);
if (lean_obj_tag(v___x_4323_) == 0)
{
lean_object* v_a_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4331_; 
v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
v_isSharedCheck_4331_ = !lean_is_exclusive(v___x_4323_);
if (v_isSharedCheck_4331_ == 0)
{
v___x_4326_ = v___x_4323_;
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_a_4324_);
lean_dec(v___x_4323_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4329_; 
if (v_isShared_4327_ == 0)
{
lean_ctor_set_tag(v___x_4326_, 1);
v___x_4329_ = v___x_4326_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v_a_4324_);
v___x_4329_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
v___y_4266_ = v_a_4284_;
v___y_4267_ = v___x_4311_;
v_a_4268_ = v___x_4329_;
goto v___jp_4265_;
}
}
}
else
{
lean_object* v_a_4332_; 
v_a_4332_ = lean_ctor_get(v___x_4323_, 0);
lean_inc(v_a_4332_);
lean_dec_ref_known(v___x_4323_, 1);
v___y_4278_ = v_a_4284_;
v___y_4279_ = v___x_4311_;
v_a_4280_ = v_a_4332_;
goto v___jp_4277_;
}
}
else
{
lean_object* v_a_4333_; 
lean_dec(v_a_4313_);
v_a_4333_ = lean_ctor_get(v___x_4314_, 0);
lean_inc(v_a_4333_);
lean_dec_ref_known(v___x_4314_, 1);
v___y_4278_ = v_a_4284_;
v___y_4279_ = v___x_4311_;
v_a_4280_ = v_a_4333_;
goto v___jp_4277_;
}
}
else
{
lean_object* v_a_4334_; 
lean_dec_ref(v_e_4203_);
v_a_4334_ = lean_ctor_get(v___x_4312_, 0);
lean_inc(v_a_4334_);
lean_dec_ref_known(v___x_4312_, 1);
v___y_4278_ = v_a_4284_;
v___y_4279_ = v___x_4311_;
v_a_4280_ = v_a_4334_;
goto v___jp_4277_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvEntry___boxed(lean_object* v_e_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_){
_start:
{
lean_object* v_res_4371_; 
v_res_4371_ = l_Lean_Meta_Tactic_Cbv_cbvEntry(v_e_4365_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_);
lean_dec(v_a_4369_);
lean_dec_ref(v_a_4368_);
lean_dec(v_a_4367_);
lean_dec_ref(v_a_4366_);
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2(lean_object* v_00_u03b1_4372_, lean_object* v_x_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_){
_start:
{
lean_object* v___x_4379_; 
v___x_4379_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_x_4373_);
return v___x_4379_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___boxed(lean_object* v_00_u03b1_4380_, lean_object* v_x_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_){
_start:
{
lean_object* v_res_4387_; 
v_res_4387_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2(v_00_u03b1_4380_, v_x_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_);
lean_dec(v___y_4385_);
lean_dec_ref(v___y_4384_);
lean_dec(v___y_4383_);
lean_dec_ref(v___y_4382_);
return v_res_4387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(lean_object* v___y_4388_){
_start:
{
lean_object* v___x_4390_; lean_object* v_traceState_4391_; lean_object* v_traces_4392_; lean_object* v___x_4393_; lean_object* v_traceState_4394_; lean_object* v_env_4395_; lean_object* v_nextMacroScope_4396_; lean_object* v_ngen_4397_; lean_object* v_auxDeclNGen_4398_; lean_object* v_cache_4399_; lean_object* v_messages_4400_; lean_object* v_infoState_4401_; lean_object* v_snapshotTasks_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4423_; 
v___x_4390_ = lean_st_ref_get(v___y_4388_);
v_traceState_4391_ = lean_ctor_get(v___x_4390_, 4);
lean_inc_ref(v_traceState_4391_);
lean_dec(v___x_4390_);
v_traces_4392_ = lean_ctor_get(v_traceState_4391_, 0);
lean_inc_ref(v_traces_4392_);
lean_dec_ref(v_traceState_4391_);
v___x_4393_ = lean_st_ref_take(v___y_4388_);
v_traceState_4394_ = lean_ctor_get(v___x_4393_, 4);
v_env_4395_ = lean_ctor_get(v___x_4393_, 0);
v_nextMacroScope_4396_ = lean_ctor_get(v___x_4393_, 1);
v_ngen_4397_ = lean_ctor_get(v___x_4393_, 2);
v_auxDeclNGen_4398_ = lean_ctor_get(v___x_4393_, 3);
v_cache_4399_ = lean_ctor_get(v___x_4393_, 5);
v_messages_4400_ = lean_ctor_get(v___x_4393_, 6);
v_infoState_4401_ = lean_ctor_get(v___x_4393_, 7);
v_snapshotTasks_4402_ = lean_ctor_get(v___x_4393_, 8);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4393_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4404_ = v___x_4393_;
v_isShared_4405_ = v_isSharedCheck_4423_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_snapshotTasks_4402_);
lean_inc(v_infoState_4401_);
lean_inc(v_messages_4400_);
lean_inc(v_cache_4399_);
lean_inc(v_traceState_4394_);
lean_inc(v_auxDeclNGen_4398_);
lean_inc(v_ngen_4397_);
lean_inc(v_nextMacroScope_4396_);
lean_inc(v_env_4395_);
lean_dec(v___x_4393_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4423_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
uint64_t v_tid_4406_; lean_object* v___x_4408_; uint8_t v_isShared_4409_; uint8_t v_isSharedCheck_4421_; 
v_tid_4406_ = lean_ctor_get_uint64(v_traceState_4394_, sizeof(void*)*1);
v_isSharedCheck_4421_ = !lean_is_exclusive(v_traceState_4394_);
if (v_isSharedCheck_4421_ == 0)
{
lean_object* v_unused_4422_; 
v_unused_4422_ = lean_ctor_get(v_traceState_4394_, 0);
lean_dec(v_unused_4422_);
v___x_4408_ = v_traceState_4394_;
v_isShared_4409_ = v_isSharedCheck_4421_;
goto v_resetjp_4407_;
}
else
{
lean_dec(v_traceState_4394_);
v___x_4408_ = lean_box(0);
v_isShared_4409_ = v_isSharedCheck_4421_;
goto v_resetjp_4407_;
}
v_resetjp_4407_:
{
lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4414_; 
v___x_4410_ = lean_unsigned_to_nat(32u);
v___x_4411_ = lean_mk_empty_array_with_capacity(v___x_4410_);
lean_dec_ref(v___x_4411_);
v___x_4412_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__2___redArg___closed__1);
if (v_isShared_4409_ == 0)
{
lean_ctor_set(v___x_4408_, 0, v___x_4412_);
v___x_4414_ = v___x_4408_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v___x_4412_);
lean_ctor_set_uint64(v_reuseFailAlloc_4420_, sizeof(void*)*1, v_tid_4406_);
v___x_4414_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
lean_object* v___x_4416_; 
if (v_isShared_4405_ == 0)
{
lean_ctor_set(v___x_4404_, 4, v___x_4414_);
v___x_4416_ = v___x_4404_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4419_; 
v_reuseFailAlloc_4419_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4419_, 0, v_env_4395_);
lean_ctor_set(v_reuseFailAlloc_4419_, 1, v_nextMacroScope_4396_);
lean_ctor_set(v_reuseFailAlloc_4419_, 2, v_ngen_4397_);
lean_ctor_set(v_reuseFailAlloc_4419_, 3, v_auxDeclNGen_4398_);
lean_ctor_set(v_reuseFailAlloc_4419_, 4, v___x_4414_);
lean_ctor_set(v_reuseFailAlloc_4419_, 5, v_cache_4399_);
lean_ctor_set(v_reuseFailAlloc_4419_, 6, v_messages_4400_);
lean_ctor_set(v_reuseFailAlloc_4419_, 7, v_infoState_4401_);
lean_ctor_set(v_reuseFailAlloc_4419_, 8, v_snapshotTasks_4402_);
v___x_4416_ = v_reuseFailAlloc_4419_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
lean_object* v___x_4417_; lean_object* v___x_4418_; 
v___x_4417_ = lean_st_ref_set(v___y_4388_, v___x_4416_);
v___x_4418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4418_, 0, v_traces_4392_);
return v___x_4418_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg___boxed(lean_object* v___y_4424_, lean_object* v___y_4425_){
_start:
{
lean_object* v_res_4426_; 
v_res_4426_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(v___y_4424_);
lean_dec(v___y_4424_);
return v_res_4426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1(lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_){
_start:
{
lean_object* v___x_4434_; 
v___x_4434_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(v___y_4432_);
return v___x_4434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___boxed(lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_){
_start:
{
lean_object* v_res_4442_; 
v_res_4442_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1(v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_);
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec(v___y_4436_);
lean_dec_ref(v___y_4435_);
return v_res_4442_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0(lean_object* v_x_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_){
_start:
{
lean_object* v___x_4451_; 
lean_inc(v___y_4445_);
lean_inc_ref(v___y_4444_);
v___x_4451_ = lean_apply_7(v_x_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, lean_box(0));
return v___x_4451_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0___boxed(lean_object* v_x_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_){
_start:
{
lean_object* v_res_4460_; 
v_res_4460_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0(v_x_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg(lean_object* v_mvarId_4461_, lean_object* v_x_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_){
_start:
{
lean_object* v___f_4470_; lean_object* v___x_4471_; 
lean_inc(v___y_4464_);
lean_inc_ref(v___y_4463_);
v___f_4470_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4470_, 0, v_x_4462_);
lean_closure_set(v___f_4470_, 1, v___y_4463_);
lean_closure_set(v___f_4470_, 2, v___y_4464_);
v___x_4471_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_4461_, v___f_4470_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_);
if (lean_obj_tag(v___x_4471_) == 0)
{
return v___x_4471_;
}
else
{
lean_object* v_a_4472_; lean_object* v___x_4474_; uint8_t v_isShared_4475_; uint8_t v_isSharedCheck_4479_; 
v_a_4472_ = lean_ctor_get(v___x_4471_, 0);
v_isSharedCheck_4479_ = !lean_is_exclusive(v___x_4471_);
if (v_isSharedCheck_4479_ == 0)
{
v___x_4474_ = v___x_4471_;
v_isShared_4475_ = v_isSharedCheck_4479_;
goto v_resetjp_4473_;
}
else
{
lean_inc(v_a_4472_);
lean_dec(v___x_4471_);
v___x_4474_ = lean_box(0);
v_isShared_4475_ = v_isSharedCheck_4479_;
goto v_resetjp_4473_;
}
v_resetjp_4473_:
{
lean_object* v___x_4477_; 
if (v_isShared_4475_ == 0)
{
v___x_4477_ = v___x_4474_;
goto v_reusejp_4476_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v_a_4472_);
v___x_4477_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4476_;
}
v_reusejp_4476_:
{
return v___x_4477_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg___boxed(lean_object* v_mvarId_4480_, lean_object* v_x_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_){
_start:
{
lean_object* v_res_4489_; 
v_res_4489_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg(v_mvarId_4480_, v_x_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
lean_dec(v___y_4485_);
lean_dec_ref(v___y_4484_);
lean_dec(v___y_4483_);
lean_dec_ref(v___y_4482_);
return v_res_4489_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4(lean_object* v_00_u03b1_4490_, lean_object* v_mvarId_4491_, lean_object* v_x_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_){
_start:
{
lean_object* v___x_4500_; 
v___x_4500_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg(v_mvarId_4491_, v_x_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_);
return v___x_4500_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___boxed(lean_object* v_00_u03b1_4501_, lean_object* v_mvarId_4502_, lean_object* v_x_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_){
_start:
{
lean_object* v_res_4511_; 
v_res_4511_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4(v_00_u03b1_4501_, v_mvarId_4502_, v_x_4503_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_);
lean_dec(v___y_4509_);
lean_dec_ref(v___y_4508_);
lean_dec(v___y_4507_);
lean_dec_ref(v___y_4506_);
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
return v_res_4511_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4513_; lean_object* v___x_4514_; 
v___x_4513_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__0));
v___x_4514_ = l_Lean_stringToMessageData(v___x_4513_);
return v___x_4514_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4516_; lean_object* v___x_4517_; 
v___x_4516_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__2));
v___x_4517_ = l_Lean_stringToMessageData(v___x_4516_);
return v___x_4517_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4519_; lean_object* v___x_4520_; 
v___x_4519_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__4));
v___x_4520_ = l_Lean_stringToMessageData(v___x_4519_);
return v___x_4520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0(lean_object* v_a_4521_, lean_object* v_x_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_){
_start:
{
if (lean_obj_tag(v_x_4522_) == 0)
{
lean_object* v_a_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4540_; 
lean_dec_ref(v_a_4521_);
v_a_4530_ = lean_ctor_get(v_x_4522_, 0);
v_isSharedCheck_4540_ = !lean_is_exclusive(v_x_4522_);
if (v_isSharedCheck_4540_ == 0)
{
v___x_4532_ = v_x_4522_;
v_isShared_4533_ = v_isSharedCheck_4540_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_a_4530_);
lean_dec(v_x_4522_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4540_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4538_; 
v___x_4534_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__1);
v___x_4535_ = l_Lean_Exception_toMessageData(v_a_4530_);
v___x_4536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4536_, 0, v___x_4534_);
lean_ctor_set(v___x_4536_, 1, v___x_4535_);
if (v_isShared_4533_ == 0)
{
lean_ctor_set(v___x_4532_, 0, v___x_4536_);
v___x_4538_ = v___x_4532_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v___x_4536_);
v___x_4538_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
return v___x_4538_;
}
}
}
else
{
lean_object* v_a_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4560_; 
v_a_4541_ = lean_ctor_get(v_x_4522_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v_x_4522_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4543_ = v_x_4522_;
v_isShared_4544_ = v_isSharedCheck_4560_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_a_4541_);
lean_dec(v_x_4522_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4560_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
if (lean_obj_tag(v_a_4541_) == 0)
{
lean_object* v___x_4545_; lean_object* v___x_4547_; 
lean_dec_ref_known(v_a_4541_, 0);
lean_dec_ref(v_a_4521_);
v___x_4545_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__3);
if (v_isShared_4544_ == 0)
{
lean_ctor_set_tag(v___x_4543_, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4545_);
v___x_4547_ = v___x_4543_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v___x_4545_);
v___x_4547_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
return v___x_4547_;
}
}
else
{
lean_object* v_e_x27_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4558_; 
v_e_x27_4549_ = lean_ctor_get(v_a_4541_, 0);
lean_inc_ref(v_e_x27_4549_);
lean_dec_ref_known(v_a_4541_, 2);
v___x_4550_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5, &l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5_once, _init_l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___closed__5);
v___x_4551_ = l_Lean_indentExpr(v_a_4521_);
v___x_4552_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4552_, 0, v___x_4550_);
lean_ctor_set(v___x_4552_, 1, v___x_4551_);
v___x_4553_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_4554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4554_, 0, v___x_4552_);
lean_ctor_set(v___x_4554_, 1, v___x_4553_);
v___x_4555_ = l_Lean_indentExpr(v_e_x27_4549_);
v___x_4556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4556_, 0, v___x_4554_);
lean_ctor_set(v___x_4556_, 1, v___x_4555_);
if (v_isShared_4544_ == 0)
{
lean_ctor_set_tag(v___x_4543_, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4556_);
v___x_4558_ = v___x_4543_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___boxed(lean_object* v_a_4561_, lean_object* v_x_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_){
_start:
{
lean_object* v_res_4570_; 
v_res_4570_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0(v_a_4561_, v_x_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
lean_dec(v___y_4568_);
lean_dec_ref(v___y_4567_);
lean_dec(v___y_4566_);
lean_dec_ref(v___y_4565_);
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg(lean_object* v_oldTraces_4571_, lean_object* v_data_4572_, lean_object* v_ref_4573_, lean_object* v_msg_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_){
_start:
{
lean_object* v_fileName_4580_; lean_object* v_fileMap_4581_; lean_object* v_options_4582_; lean_object* v_currRecDepth_4583_; lean_object* v_maxRecDepth_4584_; lean_object* v_ref_4585_; lean_object* v_currNamespace_4586_; lean_object* v_openDecls_4587_; lean_object* v_initHeartbeats_4588_; lean_object* v_maxHeartbeats_4589_; lean_object* v_quotContext_4590_; lean_object* v_currMacroScope_4591_; uint8_t v_diag_4592_; lean_object* v_cancelTk_x3f_4593_; uint8_t v_suppressElabErrors_4594_; lean_object* v_inheritedTraceOptions_4595_; lean_object* v___x_4596_; lean_object* v_traceState_4597_; lean_object* v_traces_4598_; lean_object* v_ref_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; size_t v_sz_4602_; size_t v___x_4603_; lean_object* v___x_4604_; lean_object* v_msg_4605_; lean_object* v___x_4606_; lean_object* v_a_4607_; lean_object* v___x_4609_; uint8_t v_isShared_4610_; uint8_t v_isSharedCheck_4644_; 
v_fileName_4580_ = lean_ctor_get(v___y_4577_, 0);
v_fileMap_4581_ = lean_ctor_get(v___y_4577_, 1);
v_options_4582_ = lean_ctor_get(v___y_4577_, 2);
v_currRecDepth_4583_ = lean_ctor_get(v___y_4577_, 3);
v_maxRecDepth_4584_ = lean_ctor_get(v___y_4577_, 4);
v_ref_4585_ = lean_ctor_get(v___y_4577_, 5);
v_currNamespace_4586_ = lean_ctor_get(v___y_4577_, 6);
v_openDecls_4587_ = lean_ctor_get(v___y_4577_, 7);
v_initHeartbeats_4588_ = lean_ctor_get(v___y_4577_, 8);
v_maxHeartbeats_4589_ = lean_ctor_get(v___y_4577_, 9);
v_quotContext_4590_ = lean_ctor_get(v___y_4577_, 10);
v_currMacroScope_4591_ = lean_ctor_get(v___y_4577_, 11);
v_diag_4592_ = lean_ctor_get_uint8(v___y_4577_, sizeof(void*)*14);
v_cancelTk_x3f_4593_ = lean_ctor_get(v___y_4577_, 12);
v_suppressElabErrors_4594_ = lean_ctor_get_uint8(v___y_4577_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4595_ = lean_ctor_get(v___y_4577_, 13);
v___x_4596_ = lean_st_ref_get(v___y_4578_);
v_traceState_4597_ = lean_ctor_get(v___x_4596_, 4);
lean_inc_ref(v_traceState_4597_);
lean_dec(v___x_4596_);
v_traces_4598_ = lean_ctor_get(v_traceState_4597_, 0);
lean_inc_ref(v_traces_4598_);
lean_dec_ref(v_traceState_4597_);
v_ref_4599_ = l_Lean_replaceRef(v_ref_4573_, v_ref_4585_);
lean_inc_ref(v_inheritedTraceOptions_4595_);
lean_inc(v_cancelTk_x3f_4593_);
lean_inc(v_currMacroScope_4591_);
lean_inc(v_quotContext_4590_);
lean_inc(v_maxHeartbeats_4589_);
lean_inc(v_initHeartbeats_4588_);
lean_inc(v_openDecls_4587_);
lean_inc(v_currNamespace_4586_);
lean_inc(v_maxRecDepth_4584_);
lean_inc(v_currRecDepth_4583_);
lean_inc_ref(v_options_4582_);
lean_inc_ref(v_fileMap_4581_);
lean_inc_ref(v_fileName_4580_);
v___x_4600_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4600_, 0, v_fileName_4580_);
lean_ctor_set(v___x_4600_, 1, v_fileMap_4581_);
lean_ctor_set(v___x_4600_, 2, v_options_4582_);
lean_ctor_set(v___x_4600_, 3, v_currRecDepth_4583_);
lean_ctor_set(v___x_4600_, 4, v_maxRecDepth_4584_);
lean_ctor_set(v___x_4600_, 5, v_ref_4599_);
lean_ctor_set(v___x_4600_, 6, v_currNamespace_4586_);
lean_ctor_set(v___x_4600_, 7, v_openDecls_4587_);
lean_ctor_set(v___x_4600_, 8, v_initHeartbeats_4588_);
lean_ctor_set(v___x_4600_, 9, v_maxHeartbeats_4589_);
lean_ctor_set(v___x_4600_, 10, v_quotContext_4590_);
lean_ctor_set(v___x_4600_, 11, v_currMacroScope_4591_);
lean_ctor_set(v___x_4600_, 12, v_cancelTk_x3f_4593_);
lean_ctor_set(v___x_4600_, 13, v_inheritedTraceOptions_4595_);
lean_ctor_set_uint8(v___x_4600_, sizeof(void*)*14, v_diag_4592_);
lean_ctor_set_uint8(v___x_4600_, sizeof(void*)*14 + 1, v_suppressElabErrors_4594_);
v___x_4601_ = l_Lean_PersistentArray_toArray___redArg(v_traces_4598_);
lean_dec_ref(v_traces_4598_);
v_sz_4602_ = lean_array_size(v___x_4601_);
v___x_4603_ = ((size_t)0ULL);
v___x_4604_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__4_spec__5(v_sz_4602_, v___x_4603_, v___x_4601_);
v_msg_4605_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_4605_, 0, v_data_4572_);
lean_ctor_set(v_msg_4605_, 1, v_msg_4574_);
lean_ctor_set(v_msg_4605_, 2, v___x_4604_);
v___x_4606_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_4605_, v___y_4575_, v___y_4576_, v___x_4600_, v___y_4578_);
lean_dec_ref_known(v___x_4600_, 14);
v_a_4607_ = lean_ctor_get(v___x_4606_, 0);
v_isSharedCheck_4644_ = !lean_is_exclusive(v___x_4606_);
if (v_isSharedCheck_4644_ == 0)
{
v___x_4609_ = v___x_4606_;
v_isShared_4610_ = v_isSharedCheck_4644_;
goto v_resetjp_4608_;
}
else
{
lean_inc(v_a_4607_);
lean_dec(v___x_4606_);
v___x_4609_ = lean_box(0);
v_isShared_4610_ = v_isSharedCheck_4644_;
goto v_resetjp_4608_;
}
v_resetjp_4608_:
{
lean_object* v___x_4611_; lean_object* v_traceState_4612_; lean_object* v_env_4613_; lean_object* v_nextMacroScope_4614_; lean_object* v_ngen_4615_; lean_object* v_auxDeclNGen_4616_; lean_object* v_cache_4617_; lean_object* v_messages_4618_; lean_object* v_infoState_4619_; lean_object* v_snapshotTasks_4620_; lean_object* v___x_4622_; uint8_t v_isShared_4623_; uint8_t v_isSharedCheck_4643_; 
v___x_4611_ = lean_st_ref_take(v___y_4578_);
v_traceState_4612_ = lean_ctor_get(v___x_4611_, 4);
v_env_4613_ = lean_ctor_get(v___x_4611_, 0);
v_nextMacroScope_4614_ = lean_ctor_get(v___x_4611_, 1);
v_ngen_4615_ = lean_ctor_get(v___x_4611_, 2);
v_auxDeclNGen_4616_ = lean_ctor_get(v___x_4611_, 3);
v_cache_4617_ = lean_ctor_get(v___x_4611_, 5);
v_messages_4618_ = lean_ctor_get(v___x_4611_, 6);
v_infoState_4619_ = lean_ctor_get(v___x_4611_, 7);
v_snapshotTasks_4620_ = lean_ctor_get(v___x_4611_, 8);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4622_ = v___x_4611_;
v_isShared_4623_ = v_isSharedCheck_4643_;
goto v_resetjp_4621_;
}
else
{
lean_inc(v_snapshotTasks_4620_);
lean_inc(v_infoState_4619_);
lean_inc(v_messages_4618_);
lean_inc(v_cache_4617_);
lean_inc(v_traceState_4612_);
lean_inc(v_auxDeclNGen_4616_);
lean_inc(v_ngen_4615_);
lean_inc(v_nextMacroScope_4614_);
lean_inc(v_env_4613_);
lean_dec(v___x_4611_);
v___x_4622_ = lean_box(0);
v_isShared_4623_ = v_isSharedCheck_4643_;
goto v_resetjp_4621_;
}
v_resetjp_4621_:
{
uint64_t v_tid_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4641_; 
v_tid_4624_ = lean_ctor_get_uint64(v_traceState_4612_, sizeof(void*)*1);
v_isSharedCheck_4641_ = !lean_is_exclusive(v_traceState_4612_);
if (v_isSharedCheck_4641_ == 0)
{
lean_object* v_unused_4642_; 
v_unused_4642_ = lean_ctor_get(v_traceState_4612_, 0);
lean_dec(v_unused_4642_);
v___x_4626_ = v_traceState_4612_;
v_isShared_4627_ = v_isSharedCheck_4641_;
goto v_resetjp_4625_;
}
else
{
lean_dec(v_traceState_4612_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4641_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4631_; 
v___x_4628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4628_, 0, v_ref_4573_);
lean_ctor_set(v___x_4628_, 1, v_a_4607_);
v___x_4629_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_4571_, v___x_4628_);
if (v_isShared_4627_ == 0)
{
lean_ctor_set(v___x_4626_, 0, v___x_4629_);
v___x_4631_ = v___x_4626_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4640_; 
v_reuseFailAlloc_4640_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4640_, 0, v___x_4629_);
lean_ctor_set_uint64(v_reuseFailAlloc_4640_, sizeof(void*)*1, v_tid_4624_);
v___x_4631_ = v_reuseFailAlloc_4640_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
lean_object* v___x_4633_; 
if (v_isShared_4623_ == 0)
{
lean_ctor_set(v___x_4622_, 4, v___x_4631_);
v___x_4633_ = v___x_4622_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v_env_4613_);
lean_ctor_set(v_reuseFailAlloc_4639_, 1, v_nextMacroScope_4614_);
lean_ctor_set(v_reuseFailAlloc_4639_, 2, v_ngen_4615_);
lean_ctor_set(v_reuseFailAlloc_4639_, 3, v_auxDeclNGen_4616_);
lean_ctor_set(v_reuseFailAlloc_4639_, 4, v___x_4631_);
lean_ctor_set(v_reuseFailAlloc_4639_, 5, v_cache_4617_);
lean_ctor_set(v_reuseFailAlloc_4639_, 6, v_messages_4618_);
lean_ctor_set(v_reuseFailAlloc_4639_, 7, v_infoState_4619_);
lean_ctor_set(v_reuseFailAlloc_4639_, 8, v_snapshotTasks_4620_);
v___x_4633_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4637_; 
v___x_4634_ = lean_st_ref_set(v___y_4578_, v___x_4633_);
v___x_4635_ = lean_box(0);
if (v_isShared_4610_ == 0)
{
lean_ctor_set(v___x_4609_, 0, v___x_4635_);
v___x_4637_ = v___x_4609_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v___x_4635_);
v___x_4637_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
return v___x_4637_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg___boxed(lean_object* v_oldTraces_4645_, lean_object* v_data_4646_, lean_object* v_ref_4647_, lean_object* v_msg_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_){
_start:
{
lean_object* v_res_4654_; 
v_res_4654_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg(v_oldTraces_4645_, v_data_4646_, v_ref_4647_, v_msg_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_);
lean_dec(v___y_4652_);
lean_dec_ref(v___y_4651_);
lean_dec(v___y_4650_);
lean_dec_ref(v___y_4649_);
return v_res_4654_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(lean_object* v_x_4655_){
_start:
{
if (lean_obj_tag(v_x_4655_) == 0)
{
lean_object* v_a_4657_; lean_object* v___x_4659_; uint8_t v_isShared_4660_; uint8_t v_isSharedCheck_4664_; 
v_a_4657_ = lean_ctor_get(v_x_4655_, 0);
v_isSharedCheck_4664_ = !lean_is_exclusive(v_x_4655_);
if (v_isSharedCheck_4664_ == 0)
{
v___x_4659_ = v_x_4655_;
v_isShared_4660_ = v_isSharedCheck_4664_;
goto v_resetjp_4658_;
}
else
{
lean_inc(v_a_4657_);
lean_dec(v_x_4655_);
v___x_4659_ = lean_box(0);
v_isShared_4660_ = v_isSharedCheck_4664_;
goto v_resetjp_4658_;
}
v_resetjp_4658_:
{
lean_object* v___x_4662_; 
if (v_isShared_4660_ == 0)
{
lean_ctor_set_tag(v___x_4659_, 1);
v___x_4662_ = v___x_4659_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v_a_4657_);
v___x_4662_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
return v___x_4662_;
}
}
}
else
{
lean_object* v_a_4665_; lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4672_; 
v_a_4665_ = lean_ctor_get(v_x_4655_, 0);
v_isSharedCheck_4672_ = !lean_is_exclusive(v_x_4655_);
if (v_isSharedCheck_4672_ == 0)
{
v___x_4667_ = v_x_4655_;
v_isShared_4668_ = v_isSharedCheck_4672_;
goto v_resetjp_4666_;
}
else
{
lean_inc(v_a_4665_);
lean_dec(v_x_4655_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4672_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
lean_object* v___x_4670_; 
if (v_isShared_4668_ == 0)
{
lean_ctor_set_tag(v___x_4667_, 0);
v___x_4670_ = v___x_4667_;
goto v_reusejp_4669_;
}
else
{
lean_object* v_reuseFailAlloc_4671_; 
v_reuseFailAlloc_4671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4671_, 0, v_a_4665_);
v___x_4670_ = v_reuseFailAlloc_4671_;
goto v_reusejp_4669_;
}
v_reusejp_4669_:
{
return v___x_4670_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg___boxed(lean_object* v_x_4673_, lean_object* v___y_4674_){
_start:
{
lean_object* v_res_4675_; 
v_res_4675_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(v_x_4673_);
return v_res_4675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(lean_object* v_cls_4676_, uint8_t v_collapsed_4677_, lean_object* v_tag_4678_, lean_object* v_opts_4679_, uint8_t v_clsEnabled_4680_, lean_object* v_oldTraces_4681_, lean_object* v_msg_4682_, lean_object* v_resStartStop_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_){
_start:
{
lean_object* v_fst_4691_; lean_object* v_snd_4692_; lean_object* v___y_4694_; lean_object* v___y_4695_; lean_object* v_data_4696_; lean_object* v_fst_4707_; lean_object* v_snd_4708_; lean_object* v___x_4709_; uint8_t v___x_4710_; lean_object* v___y_4712_; lean_object* v_a_4713_; uint8_t v___y_4728_; double v___y_4759_; 
v_fst_4691_ = lean_ctor_get(v_resStartStop_4683_, 0);
lean_inc(v_fst_4691_);
v_snd_4692_ = lean_ctor_get(v_resStartStop_4683_, 1);
lean_inc(v_snd_4692_);
lean_dec_ref(v_resStartStop_4683_);
v_fst_4707_ = lean_ctor_get(v_snd_4692_, 0);
lean_inc(v_fst_4707_);
v_snd_4708_ = lean_ctor_get(v_snd_4692_, 1);
lean_inc(v_snd_4708_);
lean_dec(v_snd_4692_);
v___x_4709_ = l_Lean_trace_profiler;
v___x_4710_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4679_, v___x_4709_);
if (v___x_4710_ == 0)
{
v___y_4728_ = v___x_4710_;
goto v___jp_4727_;
}
else
{
lean_object* v___x_4764_; uint8_t v___x_4765_; 
v___x_4764_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4765_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_4679_, v___x_4764_);
if (v___x_4765_ == 0)
{
lean_object* v___x_4766_; lean_object* v___x_4767_; double v___x_4768_; double v___x_4769_; double v___x_4770_; 
v___x_4766_ = l_Lean_trace_profiler_threshold;
v___x_4767_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4679_, v___x_4766_);
v___x_4768_ = lean_float_of_nat(v___x_4767_);
v___x_4769_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2);
v___x_4770_ = lean_float_div(v___x_4768_, v___x_4769_);
v___y_4759_ = v___x_4770_;
goto v___jp_4758_;
}
else
{
lean_object* v___x_4771_; lean_object* v___x_4772_; double v___x_4773_; 
v___x_4771_ = l_Lean_trace_profiler_threshold;
v___x_4772_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_4679_, v___x_4771_);
v___x_4773_ = lean_float_of_nat(v___x_4772_);
v___y_4759_ = v___x_4773_;
goto v___jp_4758_;
}
}
v___jp_4693_:
{
lean_object* v___x_4697_; 
lean_inc(v___y_4694_);
v___x_4697_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg(v_oldTraces_4681_, v_data_4696_, v___y_4694_, v___y_4695_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_);
if (lean_obj_tag(v___x_4697_) == 0)
{
lean_object* v___x_4698_; 
lean_dec_ref_known(v___x_4697_, 1);
v___x_4698_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(v_fst_4691_);
return v___x_4698_;
}
else
{
lean_object* v_a_4699_; lean_object* v___x_4701_; uint8_t v_isShared_4702_; uint8_t v_isSharedCheck_4706_; 
lean_dec(v_fst_4691_);
v_a_4699_ = lean_ctor_get(v___x_4697_, 0);
v_isSharedCheck_4706_ = !lean_is_exclusive(v___x_4697_);
if (v_isSharedCheck_4706_ == 0)
{
v___x_4701_ = v___x_4697_;
v_isShared_4702_ = v_isSharedCheck_4706_;
goto v_resetjp_4700_;
}
else
{
lean_inc(v_a_4699_);
lean_dec(v___x_4697_);
v___x_4701_ = lean_box(0);
v_isShared_4702_ = v_isSharedCheck_4706_;
goto v_resetjp_4700_;
}
v_resetjp_4700_:
{
lean_object* v___x_4704_; 
if (v_isShared_4702_ == 0)
{
v___x_4704_ = v___x_4701_;
goto v_reusejp_4703_;
}
else
{
lean_object* v_reuseFailAlloc_4705_; 
v_reuseFailAlloc_4705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4705_, 0, v_a_4699_);
v___x_4704_ = v_reuseFailAlloc_4705_;
goto v_reusejp_4703_;
}
v_reusejp_4703_:
{
return v___x_4704_;
}
}
}
}
v___jp_4711_:
{
uint8_t v_result_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; double v___x_4717_; lean_object* v_data_4718_; 
v_result_4714_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__6(v_fst_4691_);
v___x_4715_ = lean_box(v_result_4714_);
v___x_4716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4716_, 0, v___x_4715_);
v___x_4717_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_4678_);
lean_inc_ref(v___x_4716_);
lean_inc(v_cls_4676_);
v_data_4718_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4718_, 0, v_cls_4676_);
lean_ctor_set(v_data_4718_, 1, v___x_4716_);
lean_ctor_set(v_data_4718_, 2, v_tag_4678_);
lean_ctor_set_float(v_data_4718_, sizeof(void*)*3, v___x_4717_);
lean_ctor_set_float(v_data_4718_, sizeof(void*)*3 + 8, v___x_4717_);
lean_ctor_set_uint8(v_data_4718_, sizeof(void*)*3 + 16, v_collapsed_4677_);
if (v___x_4710_ == 0)
{
lean_dec_ref_known(v___x_4716_, 1);
lean_dec(v_snd_4708_);
lean_dec(v_fst_4707_);
lean_dec_ref(v_tag_4678_);
lean_dec(v_cls_4676_);
v___y_4694_ = v___y_4712_;
v___y_4695_ = v_a_4713_;
v_data_4696_ = v_data_4718_;
goto v___jp_4693_;
}
else
{
lean_object* v_data_4719_; double v___x_4720_; double v___x_4721_; 
lean_dec_ref_known(v_data_4718_, 3);
v_data_4719_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_4719_, 0, v_cls_4676_);
lean_ctor_set(v_data_4719_, 1, v___x_4716_);
lean_ctor_set(v_data_4719_, 2, v_tag_4678_);
v___x_4720_ = lean_unbox_float(v_fst_4707_);
lean_dec(v_fst_4707_);
lean_ctor_set_float(v_data_4719_, sizeof(void*)*3, v___x_4720_);
v___x_4721_ = lean_unbox_float(v_snd_4708_);
lean_dec(v_snd_4708_);
lean_ctor_set_float(v_data_4719_, sizeof(void*)*3 + 8, v___x_4721_);
lean_ctor_set_uint8(v_data_4719_, sizeof(void*)*3 + 16, v_collapsed_4677_);
v___y_4694_ = v___y_4712_;
v___y_4695_ = v_a_4713_;
v_data_4696_ = v_data_4719_;
goto v___jp_4693_;
}
}
v___jp_4722_:
{
lean_object* v_ref_4723_; lean_object* v___x_4724_; 
v_ref_4723_ = lean_ctor_get(v___y_4688_, 5);
lean_inc(v___y_4689_);
lean_inc_ref(v___y_4688_);
lean_inc(v___y_4687_);
lean_inc_ref(v___y_4686_);
lean_inc(v___y_4685_);
lean_inc_ref(v___y_4684_);
lean_inc(v_fst_4691_);
v___x_4724_ = lean_apply_8(v_msg_4682_, v_fst_4691_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, lean_box(0));
if (lean_obj_tag(v___x_4724_) == 0)
{
lean_object* v_a_4725_; 
v_a_4725_ = lean_ctor_get(v___x_4724_, 0);
lean_inc(v_a_4725_);
lean_dec_ref_known(v___x_4724_, 1);
v___y_4712_ = v_ref_4723_;
v_a_4713_ = v_a_4725_;
goto v___jp_4711_;
}
else
{
lean_object* v___x_4726_; 
lean_dec_ref_known(v___x_4724_, 1);
v___x_4726_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
v___y_4712_ = v_ref_4723_;
v_a_4713_ = v___x_4726_;
goto v___jp_4711_;
}
}
v___jp_4727_:
{
if (v_clsEnabled_4680_ == 0)
{
if (v___y_4728_ == 0)
{
lean_object* v___x_4729_; lean_object* v_traceState_4730_; lean_object* v_env_4731_; lean_object* v_nextMacroScope_4732_; lean_object* v_ngen_4733_; lean_object* v_auxDeclNGen_4734_; lean_object* v_cache_4735_; lean_object* v_messages_4736_; lean_object* v_infoState_4737_; lean_object* v_snapshotTasks_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4757_; 
lean_dec(v_snd_4708_);
lean_dec(v_fst_4707_);
lean_dec_ref(v_msg_4682_);
lean_dec_ref(v_tag_4678_);
lean_dec(v_cls_4676_);
v___x_4729_ = lean_st_ref_take(v___y_4689_);
v_traceState_4730_ = lean_ctor_get(v___x_4729_, 4);
v_env_4731_ = lean_ctor_get(v___x_4729_, 0);
v_nextMacroScope_4732_ = lean_ctor_get(v___x_4729_, 1);
v_ngen_4733_ = lean_ctor_get(v___x_4729_, 2);
v_auxDeclNGen_4734_ = lean_ctor_get(v___x_4729_, 3);
v_cache_4735_ = lean_ctor_get(v___x_4729_, 5);
v_messages_4736_ = lean_ctor_get(v___x_4729_, 6);
v_infoState_4737_ = lean_ctor_get(v___x_4729_, 7);
v_snapshotTasks_4738_ = lean_ctor_get(v___x_4729_, 8);
v_isSharedCheck_4757_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4757_ == 0)
{
v___x_4740_ = v___x_4729_;
v_isShared_4741_ = v_isSharedCheck_4757_;
goto v_resetjp_4739_;
}
else
{
lean_inc(v_snapshotTasks_4738_);
lean_inc(v_infoState_4737_);
lean_inc(v_messages_4736_);
lean_inc(v_cache_4735_);
lean_inc(v_traceState_4730_);
lean_inc(v_auxDeclNGen_4734_);
lean_inc(v_ngen_4733_);
lean_inc(v_nextMacroScope_4732_);
lean_inc(v_env_4731_);
lean_dec(v___x_4729_);
v___x_4740_ = lean_box(0);
v_isShared_4741_ = v_isSharedCheck_4757_;
goto v_resetjp_4739_;
}
v_resetjp_4739_:
{
uint64_t v_tid_4742_; lean_object* v_traces_4743_; lean_object* v___x_4745_; uint8_t v_isShared_4746_; uint8_t v_isSharedCheck_4756_; 
v_tid_4742_ = lean_ctor_get_uint64(v_traceState_4730_, sizeof(void*)*1);
v_traces_4743_ = lean_ctor_get(v_traceState_4730_, 0);
v_isSharedCheck_4756_ = !lean_is_exclusive(v_traceState_4730_);
if (v_isSharedCheck_4756_ == 0)
{
v___x_4745_ = v_traceState_4730_;
v_isShared_4746_ = v_isSharedCheck_4756_;
goto v_resetjp_4744_;
}
else
{
lean_inc(v_traces_4743_);
lean_dec(v_traceState_4730_);
v___x_4745_ = lean_box(0);
v_isShared_4746_ = v_isSharedCheck_4756_;
goto v_resetjp_4744_;
}
v_resetjp_4744_:
{
lean_object* v___x_4747_; lean_object* v___x_4749_; 
v___x_4747_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_4681_, v_traces_4743_);
lean_dec_ref(v_traces_4743_);
if (v_isShared_4746_ == 0)
{
lean_ctor_set(v___x_4745_, 0, v___x_4747_);
v___x_4749_ = v___x_4745_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v___x_4747_);
lean_ctor_set_uint64(v_reuseFailAlloc_4755_, sizeof(void*)*1, v_tid_4742_);
v___x_4749_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
lean_object* v___x_4751_; 
if (v_isShared_4741_ == 0)
{
lean_ctor_set(v___x_4740_, 4, v___x_4749_);
v___x_4751_ = v___x_4740_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v_env_4731_);
lean_ctor_set(v_reuseFailAlloc_4754_, 1, v_nextMacroScope_4732_);
lean_ctor_set(v_reuseFailAlloc_4754_, 2, v_ngen_4733_);
lean_ctor_set(v_reuseFailAlloc_4754_, 3, v_auxDeclNGen_4734_);
lean_ctor_set(v_reuseFailAlloc_4754_, 4, v___x_4749_);
lean_ctor_set(v_reuseFailAlloc_4754_, 5, v_cache_4735_);
lean_ctor_set(v_reuseFailAlloc_4754_, 6, v_messages_4736_);
lean_ctor_set(v_reuseFailAlloc_4754_, 7, v_infoState_4737_);
lean_ctor_set(v_reuseFailAlloc_4754_, 8, v_snapshotTasks_4738_);
v___x_4751_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
lean_object* v___x_4752_; lean_object* v___x_4753_; 
v___x_4752_ = lean_st_ref_set(v___y_4689_, v___x_4751_);
v___x_4753_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(v_fst_4691_);
return v___x_4753_;
}
}
}
}
}
else
{
goto v___jp_4722_;
}
}
else
{
goto v___jp_4722_;
}
}
v___jp_4758_:
{
double v___x_4760_; double v___x_4761_; double v___x_4762_; uint8_t v___x_4763_; 
v___x_4760_ = lean_unbox_float(v_snd_4708_);
v___x_4761_ = lean_unbox_float(v_fst_4707_);
v___x_4762_ = lean_float_sub(v___x_4760_, v___x_4761_);
v___x_4763_ = lean_float_decLt(v___y_4759_, v___x_4762_);
v___y_4728_ = v___x_4763_;
goto v___jp_4727_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2___boxed(lean_object* v_cls_4774_, lean_object* v_collapsed_4775_, lean_object* v_tag_4776_, lean_object* v_opts_4777_, lean_object* v_clsEnabled_4778_, lean_object* v_oldTraces_4779_, lean_object* v_msg_4780_, lean_object* v_resStartStop_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_){
_start:
{
uint8_t v_collapsed_boxed_4789_; uint8_t v_clsEnabled_boxed_4790_; lean_object* v_res_4791_; 
v_collapsed_boxed_4789_ = lean_unbox(v_collapsed_4775_);
v_clsEnabled_boxed_4790_ = lean_unbox(v_clsEnabled_4778_);
v_res_4791_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v_cls_4774_, v_collapsed_boxed_4789_, v_tag_4776_, v_opts_4777_, v_clsEnabled_boxed_4790_, v_oldTraces_4779_, v_msg_4780_, v_resStartStop_4781_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_);
lean_dec(v___y_4787_);
lean_dec_ref(v___y_4786_);
lean_dec(v___y_4785_);
lean_dec_ref(v___y_4784_);
lean_dec(v___y_4783_);
lean_dec_ref(v___y_4782_);
lean_dec_ref(v_opts_4777_);
return v_res_4791_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4793_; lean_object* v___x_4794_; 
v___x_4793_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__0));
v___x_4794_ = l_Lean_stringToMessageData(v___x_4793_);
return v___x_4794_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4796_; lean_object* v___x_4797_; 
v___x_4796_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__2));
v___x_4797_ = l_Lean_stringToMessageData(v___x_4796_);
return v___x_4797_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4799_; lean_object* v___x_4800_; 
v___x_4799_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__4));
v___x_4800_ = l_Lean_stringToMessageData(v___x_4799_);
return v___x_4800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0(lean_object* v_a_4801_, lean_object* v___x_4802_, lean_object* v_x_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_){
_start:
{
if (lean_obj_tag(v_x_4803_) == 0)
{
lean_object* v_a_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4826_; 
lean_dec_ref(v___x_4802_);
v_a_4811_ = lean_ctor_get(v_x_4803_, 0);
v_isSharedCheck_4826_ = !lean_is_exclusive(v_x_4803_);
if (v_isSharedCheck_4826_ == 0)
{
v___x_4813_ = v_x_4803_;
v_isShared_4814_ = v_isSharedCheck_4826_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_a_4811_);
lean_dec(v_x_4803_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4826_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4824_; 
v___x_4815_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1);
v___x_4816_ = l_Lean_LocalDecl_userName(v_a_4801_);
v___x_4817_ = l_Lean_MessageData_ofName(v___x_4816_);
v___x_4818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4818_, 0, v___x_4815_);
lean_ctor_set(v___x_4818_, 1, v___x_4817_);
v___x_4819_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__3);
v___x_4820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4820_, 0, v___x_4818_);
lean_ctor_set(v___x_4820_, 1, v___x_4819_);
v___x_4821_ = l_Lean_Exception_toMessageData(v_a_4811_);
v___x_4822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4822_, 0, v___x_4820_);
lean_ctor_set(v___x_4822_, 1, v___x_4821_);
if (v_isShared_4814_ == 0)
{
lean_ctor_set(v___x_4813_, 0, v___x_4822_);
v___x_4824_ = v___x_4813_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v___x_4822_);
v___x_4824_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
return v___x_4824_;
}
}
}
else
{
lean_object* v_a_4827_; lean_object* v___x_4829_; uint8_t v_isShared_4830_; uint8_t v_isSharedCheck_4856_; 
v_a_4827_ = lean_ctor_get(v_x_4803_, 0);
v_isSharedCheck_4856_ = !lean_is_exclusive(v_x_4803_);
if (v_isSharedCheck_4856_ == 0)
{
v___x_4829_ = v_x_4803_;
v_isShared_4830_ = v_isSharedCheck_4856_;
goto v_resetjp_4828_;
}
else
{
lean_inc(v_a_4827_);
lean_dec(v_x_4803_);
v___x_4829_ = lean_box(0);
v_isShared_4830_ = v_isSharedCheck_4856_;
goto v_resetjp_4828_;
}
v_resetjp_4828_:
{
if (lean_obj_tag(v_a_4827_) == 0)
{
lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4836_; lean_object* v___x_4838_; 
lean_dec_ref_known(v_a_4827_, 0);
lean_dec_ref(v___x_4802_);
v___x_4831_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1);
v___x_4832_ = l_Lean_LocalDecl_userName(v_a_4801_);
v___x_4833_ = l_Lean_MessageData_ofName(v___x_4832_);
v___x_4834_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4834_, 0, v___x_4831_);
lean_ctor_set(v___x_4834_, 1, v___x_4833_);
v___x_4835_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__5);
v___x_4836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4836_, 0, v___x_4834_);
lean_ctor_set(v___x_4836_, 1, v___x_4835_);
if (v_isShared_4830_ == 0)
{
lean_ctor_set_tag(v___x_4829_, 0);
lean_ctor_set(v___x_4829_, 0, v___x_4836_);
v___x_4838_ = v___x_4829_;
goto v_reusejp_4837_;
}
else
{
lean_object* v_reuseFailAlloc_4839_; 
v_reuseFailAlloc_4839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4839_, 0, v___x_4836_);
v___x_4838_ = v_reuseFailAlloc_4839_;
goto v_reusejp_4837_;
}
v_reusejp_4837_:
{
return v___x_4838_;
}
}
else
{
lean_object* v_e_x27_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4854_; 
v_e_x27_4840_ = lean_ctor_get(v_a_4827_, 0);
lean_inc_ref(v_e_x27_4840_);
lean_dec_ref_known(v_a_4827_, 2);
v___x_4841_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___closed__1);
v___x_4842_ = l_Lean_LocalDecl_userName(v_a_4801_);
v___x_4843_ = l_Lean_MessageData_ofName(v___x_4842_);
v___x_4844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4844_, 0, v___x_4841_);
lean_ctor_set(v___x_4844_, 1, v___x_4843_);
v___x_4845_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__8);
v___x_4846_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4846_, 0, v___x_4844_);
lean_ctor_set(v___x_4846_, 1, v___x_4845_);
v___x_4847_ = l_Lean_indentExpr(v___x_4802_);
v___x_4848_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4848_, 0, v___x_4846_);
lean_ctor_set(v___x_4848_, 1, v___x_4847_);
v___x_4849_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_4850_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4850_, 0, v___x_4848_);
lean_ctor_set(v___x_4850_, 1, v___x_4849_);
v___x_4851_ = l_Lean_indentExpr(v_e_x27_4840_);
v___x_4852_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4852_, 0, v___x_4850_);
lean_ctor_set(v___x_4852_, 1, v___x_4851_);
if (v_isShared_4830_ == 0)
{
lean_ctor_set_tag(v___x_4829_, 0);
lean_ctor_set(v___x_4829_, 0, v___x_4852_);
v___x_4854_ = v___x_4829_;
goto v_reusejp_4853_;
}
else
{
lean_object* v_reuseFailAlloc_4855_; 
v_reuseFailAlloc_4855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4855_, 0, v___x_4852_);
v___x_4854_ = v_reuseFailAlloc_4855_;
goto v_reusejp_4853_;
}
v_reusejp_4853_:
{
return v___x_4854_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___boxed(lean_object* v_a_4857_, lean_object* v___x_4858_, lean_object* v_x_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_){
_start:
{
lean_object* v_res_4867_; 
v_res_4867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0(v_a_4857_, v___x_4858_, v_x_4859_, v___y_4860_, v___y_4861_, v___y_4862_, v___y_4863_, v___y_4864_, v___y_4865_);
lean_dec(v___y_4865_);
lean_dec_ref(v___y_4864_);
lean_dec(v___y_4863_);
lean_dec_ref(v___y_4862_);
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
lean_dec_ref(v_a_4857_);
return v_res_4867_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(lean_object* v_x_4868_, lean_object* v_x_4869_, lean_object* v_x_4870_, lean_object* v_x_4871_){
_start:
{
lean_object* v_ks_4872_; lean_object* v_vs_4873_; lean_object* v___x_4875_; uint8_t v_isShared_4876_; uint8_t v_isSharedCheck_4897_; 
v_ks_4872_ = lean_ctor_get(v_x_4868_, 0);
v_vs_4873_ = lean_ctor_get(v_x_4868_, 1);
v_isSharedCheck_4897_ = !lean_is_exclusive(v_x_4868_);
if (v_isSharedCheck_4897_ == 0)
{
v___x_4875_ = v_x_4868_;
v_isShared_4876_ = v_isSharedCheck_4897_;
goto v_resetjp_4874_;
}
else
{
lean_inc(v_vs_4873_);
lean_inc(v_ks_4872_);
lean_dec(v_x_4868_);
v___x_4875_ = lean_box(0);
v_isShared_4876_ = v_isSharedCheck_4897_;
goto v_resetjp_4874_;
}
v_resetjp_4874_:
{
lean_object* v___x_4877_; uint8_t v___x_4878_; 
v___x_4877_ = lean_array_get_size(v_ks_4872_);
v___x_4878_ = lean_nat_dec_lt(v_x_4869_, v___x_4877_);
if (v___x_4878_ == 0)
{
lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4882_; 
lean_dec(v_x_4869_);
v___x_4879_ = lean_array_push(v_ks_4872_, v_x_4870_);
v___x_4880_ = lean_array_push(v_vs_4873_, v_x_4871_);
if (v_isShared_4876_ == 0)
{
lean_ctor_set(v___x_4875_, 1, v___x_4880_);
lean_ctor_set(v___x_4875_, 0, v___x_4879_);
v___x_4882_ = v___x_4875_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_4883_; 
v_reuseFailAlloc_4883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4883_, 0, v___x_4879_);
lean_ctor_set(v_reuseFailAlloc_4883_, 1, v___x_4880_);
v___x_4882_ = v_reuseFailAlloc_4883_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
return v___x_4882_;
}
}
else
{
lean_object* v_k_x27_4884_; uint8_t v___x_4885_; 
v_k_x27_4884_ = lean_array_fget_borrowed(v_ks_4872_, v_x_4869_);
v___x_4885_ = l_Lean_instBEqMVarId_beq(v_x_4870_, v_k_x27_4884_);
if (v___x_4885_ == 0)
{
lean_object* v___x_4887_; 
if (v_isShared_4876_ == 0)
{
v___x_4887_ = v___x_4875_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4891_; 
v_reuseFailAlloc_4891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4891_, 0, v_ks_4872_);
lean_ctor_set(v_reuseFailAlloc_4891_, 1, v_vs_4873_);
v___x_4887_ = v_reuseFailAlloc_4891_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
lean_object* v___x_4888_; lean_object* v___x_4889_; 
v___x_4888_ = lean_unsigned_to_nat(1u);
v___x_4889_ = lean_nat_add(v_x_4869_, v___x_4888_);
lean_dec(v_x_4869_);
v_x_4868_ = v___x_4887_;
v_x_4869_ = v___x_4889_;
goto _start;
}
}
else
{
lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4895_; 
v___x_4892_ = lean_array_fset(v_ks_4872_, v_x_4869_, v_x_4870_);
v___x_4893_ = lean_array_fset(v_vs_4873_, v_x_4869_, v_x_4871_);
lean_dec(v_x_4869_);
if (v_isShared_4876_ == 0)
{
lean_ctor_set(v___x_4875_, 1, v___x_4893_);
lean_ctor_set(v___x_4875_, 0, v___x_4892_);
v___x_4895_ = v___x_4875_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v___x_4892_);
lean_ctor_set(v_reuseFailAlloc_4896_, 1, v___x_4893_);
v___x_4895_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
return v___x_4895_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7___redArg(lean_object* v_n_4898_, lean_object* v_k_4899_, lean_object* v_v_4900_){
_start:
{
lean_object* v___x_4901_; lean_object* v___x_4902_; 
v___x_4901_ = lean_unsigned_to_nat(0u);
v___x_4902_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_n_4898_, v___x_4901_, v_k_4899_, v_v_4900_);
return v___x_4902_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_4903_; 
v___x_4903_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_4903_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(lean_object* v_x_4904_, size_t v_x_4905_, size_t v_x_4906_, lean_object* v_x_4907_, lean_object* v_x_4908_){
_start:
{
if (lean_obj_tag(v_x_4904_) == 0)
{
lean_object* v_es_4909_; size_t v___x_4910_; size_t v___x_4911_; lean_object* v_j_4912_; lean_object* v___x_4913_; uint8_t v___x_4914_; 
v_es_4909_ = lean_ctor_get(v_x_4904_, 0);
v___x_4910_ = ((size_t)31ULL);
v___x_4911_ = lean_usize_land(v_x_4905_, v___x_4910_);
v_j_4912_ = lean_usize_to_nat(v___x_4911_);
v___x_4913_ = lean_array_get_size(v_es_4909_);
v___x_4914_ = lean_nat_dec_lt(v_j_4912_, v___x_4913_);
if (v___x_4914_ == 0)
{
lean_dec(v_j_4912_);
lean_dec(v_x_4908_);
lean_dec(v_x_4907_);
return v_x_4904_;
}
else
{
lean_object* v___x_4916_; uint8_t v_isShared_4917_; uint8_t v_isSharedCheck_4953_; 
lean_inc_ref(v_es_4909_);
v_isSharedCheck_4953_ = !lean_is_exclusive(v_x_4904_);
if (v_isSharedCheck_4953_ == 0)
{
lean_object* v_unused_4954_; 
v_unused_4954_ = lean_ctor_get(v_x_4904_, 0);
lean_dec(v_unused_4954_);
v___x_4916_ = v_x_4904_;
v_isShared_4917_ = v_isSharedCheck_4953_;
goto v_resetjp_4915_;
}
else
{
lean_dec(v_x_4904_);
v___x_4916_ = lean_box(0);
v_isShared_4917_ = v_isSharedCheck_4953_;
goto v_resetjp_4915_;
}
v_resetjp_4915_:
{
lean_object* v_v_4918_; lean_object* v___x_4919_; lean_object* v_xs_x27_4920_; lean_object* v___y_4922_; 
v_v_4918_ = lean_array_fget(v_es_4909_, v_j_4912_);
v___x_4919_ = lean_box(0);
v_xs_x27_4920_ = lean_array_fset(v_es_4909_, v_j_4912_, v___x_4919_);
switch(lean_obj_tag(v_v_4918_))
{
case 0:
{
lean_object* v_key_4927_; lean_object* v_val_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4938_; 
v_key_4927_ = lean_ctor_get(v_v_4918_, 0);
v_val_4928_ = lean_ctor_get(v_v_4918_, 1);
v_isSharedCheck_4938_ = !lean_is_exclusive(v_v_4918_);
if (v_isSharedCheck_4938_ == 0)
{
v___x_4930_ = v_v_4918_;
v_isShared_4931_ = v_isSharedCheck_4938_;
goto v_resetjp_4929_;
}
else
{
lean_inc(v_val_4928_);
lean_inc(v_key_4927_);
lean_dec(v_v_4918_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4938_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
uint8_t v___x_4932_; 
v___x_4932_ = l_Lean_instBEqMVarId_beq(v_x_4907_, v_key_4927_);
if (v___x_4932_ == 0)
{
lean_object* v___x_4933_; lean_object* v___x_4934_; 
lean_del_object(v___x_4930_);
v___x_4933_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_4927_, v_val_4928_, v_x_4907_, v_x_4908_);
v___x_4934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4934_, 0, v___x_4933_);
v___y_4922_ = v___x_4934_;
goto v___jp_4921_;
}
else
{
lean_object* v___x_4936_; 
lean_dec(v_val_4928_);
lean_dec(v_key_4927_);
if (v_isShared_4931_ == 0)
{
lean_ctor_set(v___x_4930_, 1, v_x_4908_);
lean_ctor_set(v___x_4930_, 0, v_x_4907_);
v___x_4936_ = v___x_4930_;
goto v_reusejp_4935_;
}
else
{
lean_object* v_reuseFailAlloc_4937_; 
v_reuseFailAlloc_4937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4937_, 0, v_x_4907_);
lean_ctor_set(v_reuseFailAlloc_4937_, 1, v_x_4908_);
v___x_4936_ = v_reuseFailAlloc_4937_;
goto v_reusejp_4935_;
}
v_reusejp_4935_:
{
v___y_4922_ = v___x_4936_;
goto v___jp_4921_;
}
}
}
}
case 1:
{
lean_object* v_node_4939_; lean_object* v___x_4941_; uint8_t v_isShared_4942_; uint8_t v_isSharedCheck_4951_; 
v_node_4939_ = lean_ctor_get(v_v_4918_, 0);
v_isSharedCheck_4951_ = !lean_is_exclusive(v_v_4918_);
if (v_isSharedCheck_4951_ == 0)
{
v___x_4941_ = v_v_4918_;
v_isShared_4942_ = v_isSharedCheck_4951_;
goto v_resetjp_4940_;
}
else
{
lean_inc(v_node_4939_);
lean_dec(v_v_4918_);
v___x_4941_ = lean_box(0);
v_isShared_4942_ = v_isSharedCheck_4951_;
goto v_resetjp_4940_;
}
v_resetjp_4940_:
{
size_t v___x_4943_; size_t v___x_4944_; size_t v___x_4945_; size_t v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4949_; 
v___x_4943_ = ((size_t)5ULL);
v___x_4944_ = lean_usize_shift_right(v_x_4905_, v___x_4943_);
v___x_4945_ = ((size_t)1ULL);
v___x_4946_ = lean_usize_add(v_x_4906_, v___x_4945_);
v___x_4947_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_node_4939_, v___x_4944_, v___x_4946_, v_x_4907_, v_x_4908_);
if (v_isShared_4942_ == 0)
{
lean_ctor_set(v___x_4941_, 0, v___x_4947_);
v___x_4949_ = v___x_4941_;
goto v_reusejp_4948_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v___x_4947_);
v___x_4949_ = v_reuseFailAlloc_4950_;
goto v_reusejp_4948_;
}
v_reusejp_4948_:
{
v___y_4922_ = v___x_4949_;
goto v___jp_4921_;
}
}
}
default: 
{
lean_object* v___x_4952_; 
v___x_4952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4952_, 0, v_x_4907_);
lean_ctor_set(v___x_4952_, 1, v_x_4908_);
v___y_4922_ = v___x_4952_;
goto v___jp_4921_;
}
}
v___jp_4921_:
{
lean_object* v___x_4923_; lean_object* v___x_4925_; 
v___x_4923_ = lean_array_fset(v_xs_x27_4920_, v_j_4912_, v___y_4922_);
lean_dec(v_j_4912_);
if (v_isShared_4917_ == 0)
{
lean_ctor_set(v___x_4916_, 0, v___x_4923_);
v___x_4925_ = v___x_4916_;
goto v_reusejp_4924_;
}
else
{
lean_object* v_reuseFailAlloc_4926_; 
v_reuseFailAlloc_4926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4926_, 0, v___x_4923_);
v___x_4925_ = v_reuseFailAlloc_4926_;
goto v_reusejp_4924_;
}
v_reusejp_4924_:
{
return v___x_4925_;
}
}
}
}
}
else
{
lean_object* v_ks_4955_; lean_object* v_vs_4956_; lean_object* v___x_4958_; uint8_t v_isShared_4959_; uint8_t v_isSharedCheck_4976_; 
v_ks_4955_ = lean_ctor_get(v_x_4904_, 0);
v_vs_4956_ = lean_ctor_get(v_x_4904_, 1);
v_isSharedCheck_4976_ = !lean_is_exclusive(v_x_4904_);
if (v_isSharedCheck_4976_ == 0)
{
v___x_4958_ = v_x_4904_;
v_isShared_4959_ = v_isSharedCheck_4976_;
goto v_resetjp_4957_;
}
else
{
lean_inc(v_vs_4956_);
lean_inc(v_ks_4955_);
lean_dec(v_x_4904_);
v___x_4958_ = lean_box(0);
v_isShared_4959_ = v_isSharedCheck_4976_;
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
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_ks_4955_);
lean_ctor_set(v_reuseFailAlloc_4975_, 1, v_vs_4956_);
v___x_4961_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4960_;
}
v_reusejp_4960_:
{
lean_object* v_newNode_4962_; uint8_t v___y_4964_; size_t v___x_4970_; uint8_t v___x_4971_; 
v_newNode_4962_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7___redArg(v___x_4961_, v_x_4907_, v_x_4908_);
v___x_4970_ = ((size_t)7ULL);
v___x_4971_ = lean_usize_dec_le(v___x_4970_, v_x_4906_);
if (v___x_4971_ == 0)
{
lean_object* v___x_4972_; lean_object* v___x_4973_; uint8_t v___x_4974_; 
v___x_4972_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4962_);
v___x_4973_ = lean_unsigned_to_nat(4u);
v___x_4974_ = lean_nat_dec_lt(v___x_4972_, v___x_4973_);
lean_dec(v___x_4972_);
v___y_4964_ = v___x_4974_;
goto v___jp_4963_;
}
else
{
v___y_4964_ = v___x_4971_;
goto v___jp_4963_;
}
v___jp_4963_:
{
if (v___y_4964_ == 0)
{
lean_object* v_ks_4965_; lean_object* v_vs_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; lean_object* v___x_4969_; 
v_ks_4965_ = lean_ctor_get(v_newNode_4962_, 0);
lean_inc_ref(v_ks_4965_);
v_vs_4966_ = lean_ctor_get(v_newNode_4962_, 1);
lean_inc_ref(v_vs_4966_);
lean_dec_ref(v_newNode_4962_);
v___x_4967_ = lean_unsigned_to_nat(0u);
v___x_4968_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_4969_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg(v_x_4906_, v_ks_4965_, v_vs_4966_, v___x_4967_, v___x_4968_);
lean_dec_ref(v_vs_4966_);
lean_dec_ref(v_ks_4965_);
return v___x_4969_;
}
else
{
return v_newNode_4962_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg(size_t v_depth_4977_, lean_object* v_keys_4978_, lean_object* v_vals_4979_, lean_object* v_i_4980_, lean_object* v_entries_4981_){
_start:
{
lean_object* v___x_4982_; uint8_t v___x_4983_; 
v___x_4982_ = lean_array_get_size(v_keys_4978_);
v___x_4983_ = lean_nat_dec_lt(v_i_4980_, v___x_4982_);
if (v___x_4983_ == 0)
{
lean_dec(v_i_4980_);
return v_entries_4981_;
}
else
{
lean_object* v_k_4984_; lean_object* v_v_4985_; uint64_t v___x_4986_; size_t v_h_4987_; size_t v___x_4988_; lean_object* v___x_4989_; size_t v___x_4990_; size_t v___x_4991_; size_t v___x_4992_; size_t v_h_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; 
v_k_4984_ = lean_array_fget_borrowed(v_keys_4978_, v_i_4980_);
v_v_4985_ = lean_array_fget_borrowed(v_vals_4979_, v_i_4980_);
v___x_4986_ = l_Lean_instHashableMVarId_hash(v_k_4984_);
v_h_4987_ = lean_uint64_to_usize(v___x_4986_);
v___x_4988_ = ((size_t)5ULL);
v___x_4989_ = lean_unsigned_to_nat(1u);
v___x_4990_ = ((size_t)1ULL);
v___x_4991_ = lean_usize_sub(v_depth_4977_, v___x_4990_);
v___x_4992_ = lean_usize_mul(v___x_4988_, v___x_4991_);
v_h_4993_ = lean_usize_shift_right(v_h_4987_, v___x_4992_);
v___x_4994_ = lean_nat_add(v_i_4980_, v___x_4989_);
lean_dec(v_i_4980_);
lean_inc(v_v_4985_);
lean_inc(v_k_4984_);
v___x_4995_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_entries_4981_, v_h_4993_, v_depth_4977_, v_k_4984_, v_v_4985_);
v_i_4980_ = v___x_4994_;
v_entries_4981_ = v___x_4995_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object* v_depth_4997_, lean_object* v_keys_4998_, lean_object* v_vals_4999_, lean_object* v_i_5000_, lean_object* v_entries_5001_){
_start:
{
size_t v_depth_boxed_5002_; lean_object* v_res_5003_; 
v_depth_boxed_5002_ = lean_unbox_usize(v_depth_4997_);
lean_dec(v_depth_4997_);
v_res_5003_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg(v_depth_boxed_5002_, v_keys_4998_, v_vals_4999_, v_i_5000_, v_entries_5001_);
lean_dec_ref(v_vals_4999_);
lean_dec_ref(v_keys_4998_);
return v_res_5003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_x_5004_, lean_object* v_x_5005_, lean_object* v_x_5006_, lean_object* v_x_5007_, lean_object* v_x_5008_){
_start:
{
size_t v_x_48522__boxed_5009_; size_t v_x_48523__boxed_5010_; lean_object* v_res_5011_; 
v_x_48522__boxed_5009_ = lean_unbox_usize(v_x_5005_);
lean_dec(v_x_5005_);
v_x_48523__boxed_5010_ = lean_unbox_usize(v_x_5006_);
lean_dec(v_x_5006_);
v_res_5011_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_x_5004_, v_x_48522__boxed_5009_, v_x_48523__boxed_5010_, v_x_5007_, v_x_5008_);
return v_res_5011_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0___redArg(lean_object* v_x_5012_, lean_object* v_x_5013_, lean_object* v_x_5014_){
_start:
{
uint64_t v___x_5015_; size_t v___x_5016_; size_t v___x_5017_; lean_object* v___x_5018_; 
v___x_5015_ = l_Lean_instHashableMVarId_hash(v_x_5013_);
v___x_5016_ = lean_uint64_to_usize(v___x_5015_);
v___x_5017_ = ((size_t)1ULL);
v___x_5018_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_x_5012_, v___x_5016_, v___x_5017_, v_x_5013_, v_x_5014_);
return v___x_5018_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(lean_object* v_mvarId_5019_, lean_object* v_val_5020_, lean_object* v___y_5021_){
_start:
{
lean_object* v___x_5023_; lean_object* v_mctx_5024_; lean_object* v_cache_5025_; lean_object* v_zetaDeltaFVarIds_5026_; lean_object* v_postponed_5027_; lean_object* v_diag_5028_; lean_object* v___x_5030_; uint8_t v_isShared_5031_; uint8_t v_isSharedCheck_5056_; 
v___x_5023_ = lean_st_ref_take(v___y_5021_);
v_mctx_5024_ = lean_ctor_get(v___x_5023_, 0);
v_cache_5025_ = lean_ctor_get(v___x_5023_, 1);
v_zetaDeltaFVarIds_5026_ = lean_ctor_get(v___x_5023_, 2);
v_postponed_5027_ = lean_ctor_get(v___x_5023_, 3);
v_diag_5028_ = lean_ctor_get(v___x_5023_, 4);
v_isSharedCheck_5056_ = !lean_is_exclusive(v___x_5023_);
if (v_isSharedCheck_5056_ == 0)
{
v___x_5030_ = v___x_5023_;
v_isShared_5031_ = v_isSharedCheck_5056_;
goto v_resetjp_5029_;
}
else
{
lean_inc(v_diag_5028_);
lean_inc(v_postponed_5027_);
lean_inc(v_zetaDeltaFVarIds_5026_);
lean_inc(v_cache_5025_);
lean_inc(v_mctx_5024_);
lean_dec(v___x_5023_);
v___x_5030_ = lean_box(0);
v_isShared_5031_ = v_isSharedCheck_5056_;
goto v_resetjp_5029_;
}
v_resetjp_5029_:
{
lean_object* v_depth_5032_; lean_object* v_levelAssignDepth_5033_; lean_object* v_lmvarCounter_5034_; lean_object* v_mvarCounter_5035_; lean_object* v_lDecls_5036_; lean_object* v_decls_5037_; lean_object* v_userNames_5038_; lean_object* v_lAssignment_5039_; lean_object* v_eAssignment_5040_; lean_object* v_dAssignment_5041_; lean_object* v___x_5043_; uint8_t v_isShared_5044_; uint8_t v_isSharedCheck_5055_; 
v_depth_5032_ = lean_ctor_get(v_mctx_5024_, 0);
v_levelAssignDepth_5033_ = lean_ctor_get(v_mctx_5024_, 1);
v_lmvarCounter_5034_ = lean_ctor_get(v_mctx_5024_, 2);
v_mvarCounter_5035_ = lean_ctor_get(v_mctx_5024_, 3);
v_lDecls_5036_ = lean_ctor_get(v_mctx_5024_, 4);
v_decls_5037_ = lean_ctor_get(v_mctx_5024_, 5);
v_userNames_5038_ = lean_ctor_get(v_mctx_5024_, 6);
v_lAssignment_5039_ = lean_ctor_get(v_mctx_5024_, 7);
v_eAssignment_5040_ = lean_ctor_get(v_mctx_5024_, 8);
v_dAssignment_5041_ = lean_ctor_get(v_mctx_5024_, 9);
v_isSharedCheck_5055_ = !lean_is_exclusive(v_mctx_5024_);
if (v_isSharedCheck_5055_ == 0)
{
v___x_5043_ = v_mctx_5024_;
v_isShared_5044_ = v_isSharedCheck_5055_;
goto v_resetjp_5042_;
}
else
{
lean_inc(v_dAssignment_5041_);
lean_inc(v_eAssignment_5040_);
lean_inc(v_lAssignment_5039_);
lean_inc(v_userNames_5038_);
lean_inc(v_decls_5037_);
lean_inc(v_lDecls_5036_);
lean_inc(v_mvarCounter_5035_);
lean_inc(v_lmvarCounter_5034_);
lean_inc(v_levelAssignDepth_5033_);
lean_inc(v_depth_5032_);
lean_dec(v_mctx_5024_);
v___x_5043_ = lean_box(0);
v_isShared_5044_ = v_isSharedCheck_5055_;
goto v_resetjp_5042_;
}
v_resetjp_5042_:
{
lean_object* v___x_5045_; lean_object* v___x_5047_; 
v___x_5045_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0___redArg(v_eAssignment_5040_, v_mvarId_5019_, v_val_5020_);
if (v_isShared_5044_ == 0)
{
lean_ctor_set(v___x_5043_, 8, v___x_5045_);
v___x_5047_ = v___x_5043_;
goto v_reusejp_5046_;
}
else
{
lean_object* v_reuseFailAlloc_5054_; 
v_reuseFailAlloc_5054_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5054_, 0, v_depth_5032_);
lean_ctor_set(v_reuseFailAlloc_5054_, 1, v_levelAssignDepth_5033_);
lean_ctor_set(v_reuseFailAlloc_5054_, 2, v_lmvarCounter_5034_);
lean_ctor_set(v_reuseFailAlloc_5054_, 3, v_mvarCounter_5035_);
lean_ctor_set(v_reuseFailAlloc_5054_, 4, v_lDecls_5036_);
lean_ctor_set(v_reuseFailAlloc_5054_, 5, v_decls_5037_);
lean_ctor_set(v_reuseFailAlloc_5054_, 6, v_userNames_5038_);
lean_ctor_set(v_reuseFailAlloc_5054_, 7, v_lAssignment_5039_);
lean_ctor_set(v_reuseFailAlloc_5054_, 8, v___x_5045_);
lean_ctor_set(v_reuseFailAlloc_5054_, 9, v_dAssignment_5041_);
v___x_5047_ = v_reuseFailAlloc_5054_;
goto v_reusejp_5046_;
}
v_reusejp_5046_:
{
lean_object* v___x_5049_; 
if (v_isShared_5031_ == 0)
{
lean_ctor_set(v___x_5030_, 0, v___x_5047_);
v___x_5049_ = v___x_5030_;
goto v_reusejp_5048_;
}
else
{
lean_object* v_reuseFailAlloc_5053_; 
v_reuseFailAlloc_5053_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5053_, 0, v___x_5047_);
lean_ctor_set(v_reuseFailAlloc_5053_, 1, v_cache_5025_);
lean_ctor_set(v_reuseFailAlloc_5053_, 2, v_zetaDeltaFVarIds_5026_);
lean_ctor_set(v_reuseFailAlloc_5053_, 3, v_postponed_5027_);
lean_ctor_set(v_reuseFailAlloc_5053_, 4, v_diag_5028_);
v___x_5049_ = v_reuseFailAlloc_5053_;
goto v_reusejp_5048_;
}
v_reusejp_5048_:
{
lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; 
v___x_5050_ = lean_st_ref_set(v___y_5021_, v___x_5049_);
v___x_5051_ = lean_box(0);
v___x_5052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5052_, 0, v___x_5051_);
return v___x_5052_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg___boxed(lean_object* v_mvarId_5057_, lean_object* v_val_5058_, lean_object* v___y_5059_, lean_object* v___y_5060_){
_start:
{
lean_object* v_res_5061_; 
v_res_5061_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(v_mvarId_5057_, v_val_5058_, v___y_5059_);
lean_dec(v___y_5059_);
return v_res_5061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3(lean_object* v_mvarId_5069_, lean_object* v_config_5070_, lean_object* v_as_5071_, size_t v_sz_5072_, size_t v_i_5073_, lean_object* v_b_5074_, lean_object* v___y_5075_, lean_object* v___y_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_){
_start:
{
lean_object* v_a_5083_; uint8_t v___x_5087_; 
v___x_5087_ = lean_usize_dec_lt(v_i_5073_, v_sz_5072_);
if (v___x_5087_ == 0)
{
lean_object* v___x_5088_; 
lean_dec_ref(v_config_5070_);
lean_dec(v_mvarId_5069_);
v___x_5088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5088_, 0, v_b_5074_);
return v___x_5088_;
}
else
{
lean_object* v_a_5089_; lean_object* v___x_5090_; 
v_a_5089_ = lean_array_uget_borrowed(v_as_5071_, v_i_5073_);
lean_inc(v_a_5089_);
v___x_5090_ = l_Lean_FVarId_getDecl___redArg(v_a_5089_, v___y_5077_, v___y_5079_, v___y_5080_);
if (lean_obj_tag(v___x_5090_) == 0)
{
lean_object* v_options_5091_; lean_object* v_a_5092_; lean_object* v_snd_5093_; lean_object* v___x_5095_; uint8_t v_isShared_5096_; uint8_t v_isSharedCheck_5284_; 
v_options_5091_ = lean_ctor_get(v___y_5079_, 2);
v_a_5092_ = lean_ctor_get(v___x_5090_, 0);
lean_inc(v_a_5092_);
lean_dec_ref_known(v___x_5090_, 1);
v_snd_5093_ = lean_ctor_get(v_b_5074_, 1);
v_isSharedCheck_5284_ = !lean_is_exclusive(v_b_5074_);
if (v_isSharedCheck_5284_ == 0)
{
lean_object* v_unused_5285_; 
v_unused_5285_ = lean_ctor_get(v_b_5074_, 0);
lean_dec(v_unused_5285_);
v___x_5095_ = v_b_5074_;
v_isShared_5096_ = v_isSharedCheck_5284_;
goto v_resetjp_5094_;
}
else
{
lean_inc(v_snd_5093_);
lean_dec(v_b_5074_);
v___x_5095_ = lean_box(0);
v_isShared_5096_ = v_isSharedCheck_5284_;
goto v_resetjp_5094_;
}
v_resetjp_5094_:
{
lean_object* v_inheritedTraceOptions_5097_; uint8_t v_hasTrace_5098_; lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___y_5102_; 
v_inheritedTraceOptions_5097_ = lean_ctor_get(v___y_5079_, 13);
v_hasTrace_5098_ = lean_ctor_get_uint8(v_options_5091_, sizeof(void*)*1);
v___x_5099_ = lean_box(0);
v___x_5100_ = l_Lean_LocalDecl_type(v_a_5092_);
if (v_hasTrace_5098_ == 0)
{
lean_object* v___x_5199_; 
lean_inc_ref(v_config_5070_);
lean_inc_ref(v___x_5100_);
v___x_5199_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5100_, v_config_5070_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_);
v___y_5102_ = v___x_5199_;
goto v___jp_5101_;
}
else
{
lean_object* v___f_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; uint8_t v___x_5204_; lean_object* v___y_5206_; lean_object* v___y_5207_; lean_object* v_a_5208_; lean_object* v___y_5221_; lean_object* v___y_5222_; lean_object* v_a_5223_; 
lean_inc_ref(v___x_5100_);
lean_inc(v_a_5092_);
v___f_5200_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___lam__0___boxed), 10, 2);
lean_closure_set(v___f_5200_, 0, v_a_5092_);
lean_closure_set(v___f_5200_, 1, v___x_5100_);
v___x_5201_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_5202_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_5203_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_5204_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5097_, v_options_5091_, v___x_5203_);
if (v___x_5204_ == 0)
{
lean_object* v___x_5281_; uint8_t v___x_5282_; 
v___x_5281_ = l_Lean_trace_profiler;
v___x_5282_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5091_, v___x_5281_);
if (v___x_5282_ == 0)
{
lean_object* v___x_5283_; 
lean_dec_ref(v___f_5200_);
lean_inc_ref(v_config_5070_);
lean_inc_ref(v___x_5100_);
v___x_5283_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5100_, v_config_5070_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_);
v___y_5102_ = v___x_5283_;
goto v___jp_5101_;
}
else
{
goto v___jp_5232_;
}
}
else
{
goto v___jp_5232_;
}
v___jp_5205_:
{
lean_object* v___x_5209_; double v___x_5210_; double v___x_5211_; double v___x_5212_; double v___x_5213_; double v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; 
v___x_5209_ = lean_io_mono_nanos_now();
v___x_5210_ = lean_float_of_nat(v___y_5207_);
v___x_5211_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_5212_ = lean_float_div(v___x_5210_, v___x_5211_);
v___x_5213_ = lean_float_of_nat(v___x_5209_);
v___x_5214_ = lean_float_div(v___x_5213_, v___x_5211_);
v___x_5215_ = lean_box_float(v___x_5212_);
v___x_5216_ = lean_box_float(v___x_5214_);
v___x_5217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5217_, 0, v___x_5215_);
lean_ctor_set(v___x_5217_, 1, v___x_5216_);
v___x_5218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5218_, 0, v_a_5208_);
lean_ctor_set(v___x_5218_, 1, v___x_5217_);
v___x_5219_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v___x_5201_, v_hasTrace_5098_, v___x_5202_, v_options_5091_, v___x_5204_, v___y_5206_, v___f_5200_, v___x_5218_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_);
v___y_5102_ = v___x_5219_;
goto v___jp_5101_;
}
v___jp_5220_:
{
lean_object* v___x_5224_; double v___x_5225_; double v___x_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; 
v___x_5224_ = lean_io_get_num_heartbeats();
v___x_5225_ = lean_float_of_nat(v___y_5222_);
v___x_5226_ = lean_float_of_nat(v___x_5224_);
v___x_5227_ = lean_box_float(v___x_5225_);
v___x_5228_ = lean_box_float(v___x_5226_);
v___x_5229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5229_, 0, v___x_5227_);
lean_ctor_set(v___x_5229_, 1, v___x_5228_);
v___x_5230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5230_, 0, v_a_5223_);
lean_ctor_set(v___x_5230_, 1, v___x_5229_);
v___x_5231_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v___x_5201_, v_hasTrace_5098_, v___x_5202_, v_options_5091_, v___x_5204_, v___y_5221_, v___f_5200_, v___x_5230_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_);
v___y_5102_ = v___x_5231_;
goto v___jp_5101_;
}
v___jp_5232_:
{
lean_object* v___x_5233_; 
v___x_5233_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(v___y_5080_);
if (lean_obj_tag(v___x_5233_) == 0)
{
lean_object* v_a_5234_; lean_object* v___x_5235_; uint8_t v___x_5236_; 
v_a_5234_ = lean_ctor_get(v___x_5233_, 0);
lean_inc(v_a_5234_);
lean_dec_ref_known(v___x_5233_, 1);
v___x_5235_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5236_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5091_, v___x_5235_);
if (v___x_5236_ == 0)
{
lean_object* v___x_5237_; lean_object* v___x_5238_; 
v___x_5237_ = lean_io_mono_nanos_now();
lean_inc_ref(v_config_5070_);
lean_inc_ref(v___x_5100_);
v___x_5238_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5100_, v_config_5070_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_);
if (lean_obj_tag(v___x_5238_) == 0)
{
lean_object* v_a_5239_; lean_object* v___x_5241_; uint8_t v_isShared_5242_; uint8_t v_isSharedCheck_5246_; 
v_a_5239_ = lean_ctor_get(v___x_5238_, 0);
v_isSharedCheck_5246_ = !lean_is_exclusive(v___x_5238_);
if (v_isSharedCheck_5246_ == 0)
{
v___x_5241_ = v___x_5238_;
v_isShared_5242_ = v_isSharedCheck_5246_;
goto v_resetjp_5240_;
}
else
{
lean_inc(v_a_5239_);
lean_dec(v___x_5238_);
v___x_5241_ = lean_box(0);
v_isShared_5242_ = v_isSharedCheck_5246_;
goto v_resetjp_5240_;
}
v_resetjp_5240_:
{
lean_object* v___x_5244_; 
if (v_isShared_5242_ == 0)
{
lean_ctor_set_tag(v___x_5241_, 1);
v___x_5244_ = v___x_5241_;
goto v_reusejp_5243_;
}
else
{
lean_object* v_reuseFailAlloc_5245_; 
v_reuseFailAlloc_5245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5245_, 0, v_a_5239_);
v___x_5244_ = v_reuseFailAlloc_5245_;
goto v_reusejp_5243_;
}
v_reusejp_5243_:
{
v___y_5206_ = v_a_5234_;
v___y_5207_ = v___x_5237_;
v_a_5208_ = v___x_5244_;
goto v___jp_5205_;
}
}
}
else
{
lean_object* v_a_5247_; lean_object* v___x_5249_; uint8_t v_isShared_5250_; uint8_t v_isSharedCheck_5254_; 
v_a_5247_ = lean_ctor_get(v___x_5238_, 0);
v_isSharedCheck_5254_ = !lean_is_exclusive(v___x_5238_);
if (v_isSharedCheck_5254_ == 0)
{
v___x_5249_ = v___x_5238_;
v_isShared_5250_ = v_isSharedCheck_5254_;
goto v_resetjp_5248_;
}
else
{
lean_inc(v_a_5247_);
lean_dec(v___x_5238_);
v___x_5249_ = lean_box(0);
v_isShared_5250_ = v_isSharedCheck_5254_;
goto v_resetjp_5248_;
}
v_resetjp_5248_:
{
lean_object* v___x_5252_; 
if (v_isShared_5250_ == 0)
{
lean_ctor_set_tag(v___x_5249_, 0);
v___x_5252_ = v___x_5249_;
goto v_reusejp_5251_;
}
else
{
lean_object* v_reuseFailAlloc_5253_; 
v_reuseFailAlloc_5253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5253_, 0, v_a_5247_);
v___x_5252_ = v_reuseFailAlloc_5253_;
goto v_reusejp_5251_;
}
v_reusejp_5251_:
{
v___y_5206_ = v_a_5234_;
v___y_5207_ = v___x_5237_;
v_a_5208_ = v___x_5252_;
goto v___jp_5205_;
}
}
}
}
else
{
lean_object* v___x_5255_; lean_object* v___x_5256_; 
v___x_5255_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_config_5070_);
lean_inc_ref(v___x_5100_);
v___x_5256_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5100_, v_config_5070_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_);
if (lean_obj_tag(v___x_5256_) == 0)
{
lean_object* v_a_5257_; lean_object* v___x_5259_; uint8_t v_isShared_5260_; uint8_t v_isSharedCheck_5264_; 
v_a_5257_ = lean_ctor_get(v___x_5256_, 0);
v_isSharedCheck_5264_ = !lean_is_exclusive(v___x_5256_);
if (v_isSharedCheck_5264_ == 0)
{
v___x_5259_ = v___x_5256_;
v_isShared_5260_ = v_isSharedCheck_5264_;
goto v_resetjp_5258_;
}
else
{
lean_inc(v_a_5257_);
lean_dec(v___x_5256_);
v___x_5259_ = lean_box(0);
v_isShared_5260_ = v_isSharedCheck_5264_;
goto v_resetjp_5258_;
}
v_resetjp_5258_:
{
lean_object* v___x_5262_; 
if (v_isShared_5260_ == 0)
{
lean_ctor_set_tag(v___x_5259_, 1);
v___x_5262_ = v___x_5259_;
goto v_reusejp_5261_;
}
else
{
lean_object* v_reuseFailAlloc_5263_; 
v_reuseFailAlloc_5263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5263_, 0, v_a_5257_);
v___x_5262_ = v_reuseFailAlloc_5263_;
goto v_reusejp_5261_;
}
v_reusejp_5261_:
{
v___y_5221_ = v_a_5234_;
v___y_5222_ = v___x_5255_;
v_a_5223_ = v___x_5262_;
goto v___jp_5220_;
}
}
}
else
{
lean_object* v_a_5265_; lean_object* v___x_5267_; uint8_t v_isShared_5268_; uint8_t v_isSharedCheck_5272_; 
v_a_5265_ = lean_ctor_get(v___x_5256_, 0);
v_isSharedCheck_5272_ = !lean_is_exclusive(v___x_5256_);
if (v_isSharedCheck_5272_ == 0)
{
v___x_5267_ = v___x_5256_;
v_isShared_5268_ = v_isSharedCheck_5272_;
goto v_resetjp_5266_;
}
else
{
lean_inc(v_a_5265_);
lean_dec(v___x_5256_);
v___x_5267_ = lean_box(0);
v_isShared_5268_ = v_isSharedCheck_5272_;
goto v_resetjp_5266_;
}
v_resetjp_5266_:
{
lean_object* v___x_5270_; 
if (v_isShared_5268_ == 0)
{
lean_ctor_set_tag(v___x_5267_, 0);
v___x_5270_ = v___x_5267_;
goto v_reusejp_5269_;
}
else
{
lean_object* v_reuseFailAlloc_5271_; 
v_reuseFailAlloc_5271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5271_, 0, v_a_5265_);
v___x_5270_ = v_reuseFailAlloc_5271_;
goto v_reusejp_5269_;
}
v_reusejp_5269_:
{
v___y_5221_ = v_a_5234_;
v___y_5222_ = v___x_5255_;
v_a_5223_ = v___x_5270_;
goto v___jp_5220_;
}
}
}
}
}
else
{
lean_object* v_a_5273_; lean_object* v___x_5275_; uint8_t v_isShared_5276_; uint8_t v_isSharedCheck_5280_; 
lean_dec_ref(v___f_5200_);
lean_dec_ref(v___x_5100_);
lean_del_object(v___x_5095_);
lean_dec(v_snd_5093_);
lean_dec(v_a_5092_);
lean_dec_ref(v_config_5070_);
lean_dec(v_mvarId_5069_);
v_a_5273_ = lean_ctor_get(v___x_5233_, 0);
v_isSharedCheck_5280_ = !lean_is_exclusive(v___x_5233_);
if (v_isSharedCheck_5280_ == 0)
{
v___x_5275_ = v___x_5233_;
v_isShared_5276_ = v_isSharedCheck_5280_;
goto v_resetjp_5274_;
}
else
{
lean_inc(v_a_5273_);
lean_dec(v___x_5233_);
v___x_5275_ = lean_box(0);
v_isShared_5276_ = v_isSharedCheck_5280_;
goto v_resetjp_5274_;
}
v_resetjp_5274_:
{
lean_object* v___x_5278_; 
if (v_isShared_5276_ == 0)
{
v___x_5278_ = v___x_5275_;
goto v_reusejp_5277_;
}
else
{
lean_object* v_reuseFailAlloc_5279_; 
v_reuseFailAlloc_5279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5279_, 0, v_a_5273_);
v___x_5278_ = v_reuseFailAlloc_5279_;
goto v_reusejp_5277_;
}
v_reusejp_5277_:
{
return v___x_5278_;
}
}
}
}
}
v___jp_5101_:
{
if (lean_obj_tag(v___y_5102_) == 0)
{
lean_object* v_a_5103_; 
v_a_5103_ = lean_ctor_get(v___y_5102_, 0);
lean_inc(v_a_5103_);
lean_dec_ref_known(v___y_5102_, 1);
if (lean_obj_tag(v_a_5103_) == 0)
{
lean_object* v___x_5105_; 
lean_dec_ref_known(v_a_5103_, 0);
lean_dec_ref(v___x_5100_);
lean_dec(v_a_5092_);
if (v_isShared_5096_ == 0)
{
lean_ctor_set(v___x_5095_, 0, v___x_5099_);
v___x_5105_ = v___x_5095_;
goto v_reusejp_5104_;
}
else
{
lean_object* v_reuseFailAlloc_5106_; 
v_reuseFailAlloc_5106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5106_, 0, v___x_5099_);
lean_ctor_set(v_reuseFailAlloc_5106_, 1, v_snd_5093_);
v___x_5105_ = v_reuseFailAlloc_5106_;
goto v_reusejp_5104_;
}
v_reusejp_5104_:
{
v_a_5083_ = v___x_5105_;
goto v___jp_5082_;
}
}
else
{
lean_object* v_e_x27_5107_; lean_object* v_proof_5108_; uint8_t v___x_5109_; 
v_e_x27_5107_ = lean_ctor_get(v_a_5103_, 0);
lean_inc_ref_n(v_e_x27_5107_, 2);
v_proof_5108_ = lean_ctor_get(v_a_5103_, 1);
lean_inc_ref(v_proof_5108_);
lean_dec_ref_known(v_a_5103_, 2);
v___x_5109_ = l_Lean_Expr_isFalse(v_e_x27_5107_);
if (v___x_5109_ == 0)
{
lean_object* v___x_5110_; 
lean_inc_ref(v___x_5100_);
v___x_5110_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_5100_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_);
if (lean_obj_tag(v___x_5110_) == 0)
{
lean_object* v_a_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; uint8_t v___x_5119_; uint8_t v___x_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5124_; 
v_a_5111_ = lean_ctor_get(v___x_5110_, 0);
lean_inc(v_a_5111_);
lean_dec_ref_known(v___x_5110_, 1);
v___x_5112_ = l_Lean_LocalDecl_userName(v_a_5092_);
lean_dec(v_a_5092_);
v___x_5113_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__2));
v___x_5114_ = lean_box(0);
v___x_5115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5115_, 0, v_a_5111_);
lean_ctor_set(v___x_5115_, 1, v___x_5114_);
v___x_5116_ = l_Lean_mkConst(v___x_5113_, v___x_5115_);
lean_inc(v_a_5089_);
v___x_5117_ = l_Lean_mkFVar(v_a_5089_);
lean_inc_ref(v_e_x27_5107_);
v___x_5118_ = l_Lean_mkApp4(v___x_5116_, v___x_5100_, v_e_x27_5107_, v_proof_5108_, v___x_5117_);
v___x_5119_ = 0;
v___x_5120_ = 0;
v___x_5121_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5121_, 0, v___x_5112_);
lean_ctor_set(v___x_5121_, 1, v_e_x27_5107_);
lean_ctor_set(v___x_5121_, 2, v___x_5118_);
lean_ctor_set_uint8(v___x_5121_, sizeof(void*)*3, v___x_5119_);
lean_ctor_set_uint8(v___x_5121_, sizeof(void*)*3 + 1, v___x_5120_);
v___x_5122_ = lean_array_push(v_snd_5093_, v___x_5121_);
if (v_isShared_5096_ == 0)
{
lean_ctor_set(v___x_5095_, 1, v___x_5122_);
lean_ctor_set(v___x_5095_, 0, v___x_5099_);
v___x_5124_ = v___x_5095_;
goto v_reusejp_5123_;
}
else
{
lean_object* v_reuseFailAlloc_5125_; 
v_reuseFailAlloc_5125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5125_, 0, v___x_5099_);
lean_ctor_set(v_reuseFailAlloc_5125_, 1, v___x_5122_);
v___x_5124_ = v_reuseFailAlloc_5125_;
goto v_reusejp_5123_;
}
v_reusejp_5123_:
{
v_a_5083_ = v___x_5124_;
goto v___jp_5082_;
}
}
else
{
lean_object* v_a_5126_; lean_object* v___x_5128_; uint8_t v_isShared_5129_; uint8_t v_isSharedCheck_5133_; 
lean_dec_ref(v_proof_5108_);
lean_dec_ref(v_e_x27_5107_);
lean_dec_ref(v___x_5100_);
lean_del_object(v___x_5095_);
lean_dec(v_snd_5093_);
lean_dec(v_a_5092_);
lean_dec_ref(v_config_5070_);
lean_dec(v_mvarId_5069_);
v_a_5126_ = lean_ctor_get(v___x_5110_, 0);
v_isSharedCheck_5133_ = !lean_is_exclusive(v___x_5110_);
if (v_isSharedCheck_5133_ == 0)
{
v___x_5128_ = v___x_5110_;
v_isShared_5129_ = v_isSharedCheck_5133_;
goto v_resetjp_5127_;
}
else
{
lean_inc(v_a_5126_);
lean_dec(v___x_5110_);
v___x_5128_ = lean_box(0);
v_isShared_5129_ = v_isSharedCheck_5133_;
goto v_resetjp_5127_;
}
v_resetjp_5127_:
{
lean_object* v___x_5131_; 
if (v_isShared_5129_ == 0)
{
v___x_5131_ = v___x_5128_;
goto v_reusejp_5130_;
}
else
{
lean_object* v_reuseFailAlloc_5132_; 
v_reuseFailAlloc_5132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5132_, 0, v_a_5126_);
v___x_5131_ = v_reuseFailAlloc_5132_;
goto v_reusejp_5130_;
}
v_reusejp_5130_:
{
return v___x_5131_;
}
}
}
}
else
{
lean_object* v___x_5134_; 
lean_dec(v_a_5092_);
lean_dec_ref(v_config_5070_);
lean_inc_ref(v___x_5100_);
v___x_5134_ = l_Lean_Meta_Sym_getLevel___redArg(v___x_5100_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_);
if (lean_obj_tag(v___x_5134_) == 0)
{
lean_object* v_a_5135_; lean_object* v___x_5136_; 
v_a_5135_ = lean_ctor_get(v___x_5134_, 0);
lean_inc(v_a_5135_);
lean_dec_ref_known(v___x_5134_, 1);
lean_inc(v_mvarId_5069_);
v___x_5136_ = l_Lean_MVarId_getType(v_mvarId_5069_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_);
if (lean_obj_tag(v___x_5136_) == 0)
{
lean_object* v_a_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; 
v_a_5137_ = lean_ctor_get(v___x_5136_, 0);
lean_inc(v_a_5137_);
lean_dec_ref_known(v___x_5136_, 1);
v___x_5138_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__2));
v___x_5139_ = lean_box(0);
v___x_5140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5140_, 0, v_a_5135_);
lean_ctor_set(v___x_5140_, 1, v___x_5139_);
v___x_5141_ = l_Lean_mkConst(v___x_5138_, v___x_5140_);
lean_inc(v_a_5089_);
v___x_5142_ = l_Lean_mkFVar(v_a_5089_);
v___x_5143_ = l_Lean_mkApp4(v___x_5141_, v___x_5100_, v_e_x27_5107_, v_proof_5108_, v___x_5142_);
v___x_5144_ = l_Lean_Meta_mkFalseElim(v_a_5137_, v___x_5143_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_);
if (lean_obj_tag(v___x_5144_) == 0)
{
lean_object* v_a_5145_; lean_object* v___x_5146_; 
v_a_5145_ = lean_ctor_get(v___x_5144_, 0);
lean_inc(v_a_5145_);
lean_dec_ref_known(v___x_5144_, 1);
v___x_5146_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(v_mvarId_5069_, v_a_5145_, v___y_5078_);
if (lean_obj_tag(v___x_5146_) == 0)
{
lean_object* v___x_5148_; uint8_t v_isShared_5149_; uint8_t v_isSharedCheck_5157_; 
v_isSharedCheck_5157_ = !lean_is_exclusive(v___x_5146_);
if (v_isSharedCheck_5157_ == 0)
{
lean_object* v_unused_5158_; 
v_unused_5158_ = lean_ctor_get(v___x_5146_, 0);
lean_dec(v_unused_5158_);
v___x_5148_ = v___x_5146_;
v_isShared_5149_ = v_isSharedCheck_5157_;
goto v_resetjp_5147_;
}
else
{
lean_dec(v___x_5146_);
v___x_5148_ = lean_box(0);
v_isShared_5149_ = v_isSharedCheck_5157_;
goto v_resetjp_5147_;
}
v_resetjp_5147_:
{
lean_object* v___x_5150_; lean_object* v___x_5152_; 
v___x_5150_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___closed__3));
if (v_isShared_5096_ == 0)
{
lean_ctor_set(v___x_5095_, 0, v___x_5150_);
v___x_5152_ = v___x_5095_;
goto v_reusejp_5151_;
}
else
{
lean_object* v_reuseFailAlloc_5156_; 
v_reuseFailAlloc_5156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5156_, 0, v___x_5150_);
lean_ctor_set(v_reuseFailAlloc_5156_, 1, v_snd_5093_);
v___x_5152_ = v_reuseFailAlloc_5156_;
goto v_reusejp_5151_;
}
v_reusejp_5151_:
{
lean_object* v___x_5154_; 
if (v_isShared_5149_ == 0)
{
lean_ctor_set(v___x_5148_, 0, v___x_5152_);
v___x_5154_ = v___x_5148_;
goto v_reusejp_5153_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v___x_5152_);
v___x_5154_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5153_;
}
v_reusejp_5153_:
{
return v___x_5154_;
}
}
}
}
else
{
lean_object* v_a_5159_; lean_object* v___x_5161_; uint8_t v_isShared_5162_; uint8_t v_isSharedCheck_5166_; 
lean_del_object(v___x_5095_);
lean_dec(v_snd_5093_);
v_a_5159_ = lean_ctor_get(v___x_5146_, 0);
v_isSharedCheck_5166_ = !lean_is_exclusive(v___x_5146_);
if (v_isSharedCheck_5166_ == 0)
{
v___x_5161_ = v___x_5146_;
v_isShared_5162_ = v_isSharedCheck_5166_;
goto v_resetjp_5160_;
}
else
{
lean_inc(v_a_5159_);
lean_dec(v___x_5146_);
v___x_5161_ = lean_box(0);
v_isShared_5162_ = v_isSharedCheck_5166_;
goto v_resetjp_5160_;
}
v_resetjp_5160_:
{
lean_object* v___x_5164_; 
if (v_isShared_5162_ == 0)
{
v___x_5164_ = v___x_5161_;
goto v_reusejp_5163_;
}
else
{
lean_object* v_reuseFailAlloc_5165_; 
v_reuseFailAlloc_5165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5165_, 0, v_a_5159_);
v___x_5164_ = v_reuseFailAlloc_5165_;
goto v_reusejp_5163_;
}
v_reusejp_5163_:
{
return v___x_5164_;
}
}
}
}
else
{
lean_object* v_a_5167_; lean_object* v___x_5169_; uint8_t v_isShared_5170_; uint8_t v_isSharedCheck_5174_; 
lean_del_object(v___x_5095_);
lean_dec(v_snd_5093_);
lean_dec(v_mvarId_5069_);
v_a_5167_ = lean_ctor_get(v___x_5144_, 0);
v_isSharedCheck_5174_ = !lean_is_exclusive(v___x_5144_);
if (v_isSharedCheck_5174_ == 0)
{
v___x_5169_ = v___x_5144_;
v_isShared_5170_ = v_isSharedCheck_5174_;
goto v_resetjp_5168_;
}
else
{
lean_inc(v_a_5167_);
lean_dec(v___x_5144_);
v___x_5169_ = lean_box(0);
v_isShared_5170_ = v_isSharedCheck_5174_;
goto v_resetjp_5168_;
}
v_resetjp_5168_:
{
lean_object* v___x_5172_; 
if (v_isShared_5170_ == 0)
{
v___x_5172_ = v___x_5169_;
goto v_reusejp_5171_;
}
else
{
lean_object* v_reuseFailAlloc_5173_; 
v_reuseFailAlloc_5173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5173_, 0, v_a_5167_);
v___x_5172_ = v_reuseFailAlloc_5173_;
goto v_reusejp_5171_;
}
v_reusejp_5171_:
{
return v___x_5172_;
}
}
}
}
else
{
lean_object* v_a_5175_; lean_object* v___x_5177_; uint8_t v_isShared_5178_; uint8_t v_isSharedCheck_5182_; 
lean_dec(v_a_5135_);
lean_dec_ref(v_proof_5108_);
lean_dec_ref(v_e_x27_5107_);
lean_dec_ref(v___x_5100_);
lean_del_object(v___x_5095_);
lean_dec(v_snd_5093_);
lean_dec(v_mvarId_5069_);
v_a_5175_ = lean_ctor_get(v___x_5136_, 0);
v_isSharedCheck_5182_ = !lean_is_exclusive(v___x_5136_);
if (v_isSharedCheck_5182_ == 0)
{
v___x_5177_ = v___x_5136_;
v_isShared_5178_ = v_isSharedCheck_5182_;
goto v_resetjp_5176_;
}
else
{
lean_inc(v_a_5175_);
lean_dec(v___x_5136_);
v___x_5177_ = lean_box(0);
v_isShared_5178_ = v_isSharedCheck_5182_;
goto v_resetjp_5176_;
}
v_resetjp_5176_:
{
lean_object* v___x_5180_; 
if (v_isShared_5178_ == 0)
{
v___x_5180_ = v___x_5177_;
goto v_reusejp_5179_;
}
else
{
lean_object* v_reuseFailAlloc_5181_; 
v_reuseFailAlloc_5181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5181_, 0, v_a_5175_);
v___x_5180_ = v_reuseFailAlloc_5181_;
goto v_reusejp_5179_;
}
v_reusejp_5179_:
{
return v___x_5180_;
}
}
}
}
else
{
lean_object* v_a_5183_; lean_object* v___x_5185_; uint8_t v_isShared_5186_; uint8_t v_isSharedCheck_5190_; 
lean_dec_ref(v_proof_5108_);
lean_dec_ref(v_e_x27_5107_);
lean_dec_ref(v___x_5100_);
lean_del_object(v___x_5095_);
lean_dec(v_snd_5093_);
lean_dec(v_mvarId_5069_);
v_a_5183_ = lean_ctor_get(v___x_5134_, 0);
v_isSharedCheck_5190_ = !lean_is_exclusive(v___x_5134_);
if (v_isSharedCheck_5190_ == 0)
{
v___x_5185_ = v___x_5134_;
v_isShared_5186_ = v_isSharedCheck_5190_;
goto v_resetjp_5184_;
}
else
{
lean_inc(v_a_5183_);
lean_dec(v___x_5134_);
v___x_5185_ = lean_box(0);
v_isShared_5186_ = v_isSharedCheck_5190_;
goto v_resetjp_5184_;
}
v_resetjp_5184_:
{
lean_object* v___x_5188_; 
if (v_isShared_5186_ == 0)
{
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
return v___x_5188_;
}
}
}
}
}
}
else
{
lean_object* v_a_5191_; lean_object* v___x_5193_; uint8_t v_isShared_5194_; uint8_t v_isSharedCheck_5198_; 
lean_dec_ref(v___x_5100_);
lean_del_object(v___x_5095_);
lean_dec(v_snd_5093_);
lean_dec(v_a_5092_);
lean_dec_ref(v_config_5070_);
lean_dec(v_mvarId_5069_);
v_a_5191_ = lean_ctor_get(v___y_5102_, 0);
v_isSharedCheck_5198_ = !lean_is_exclusive(v___y_5102_);
if (v_isSharedCheck_5198_ == 0)
{
v___x_5193_ = v___y_5102_;
v_isShared_5194_ = v_isSharedCheck_5198_;
goto v_resetjp_5192_;
}
else
{
lean_inc(v_a_5191_);
lean_dec(v___y_5102_);
v___x_5193_ = lean_box(0);
v_isShared_5194_ = v_isSharedCheck_5198_;
goto v_resetjp_5192_;
}
v_resetjp_5192_:
{
lean_object* v___x_5196_; 
if (v_isShared_5194_ == 0)
{
v___x_5196_ = v___x_5193_;
goto v_reusejp_5195_;
}
else
{
lean_object* v_reuseFailAlloc_5197_; 
v_reuseFailAlloc_5197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5197_, 0, v_a_5191_);
v___x_5196_ = v_reuseFailAlloc_5197_;
goto v_reusejp_5195_;
}
v_reusejp_5195_:
{
return v___x_5196_;
}
}
}
}
}
}
else
{
lean_object* v_a_5286_; lean_object* v___x_5288_; uint8_t v_isShared_5289_; uint8_t v_isSharedCheck_5293_; 
lean_dec_ref(v_b_5074_);
lean_dec_ref(v_config_5070_);
lean_dec(v_mvarId_5069_);
v_a_5286_ = lean_ctor_get(v___x_5090_, 0);
v_isSharedCheck_5293_ = !lean_is_exclusive(v___x_5090_);
if (v_isSharedCheck_5293_ == 0)
{
v___x_5288_ = v___x_5090_;
v_isShared_5289_ = v_isSharedCheck_5293_;
goto v_resetjp_5287_;
}
else
{
lean_inc(v_a_5286_);
lean_dec(v___x_5090_);
v___x_5288_ = lean_box(0);
v_isShared_5289_ = v_isSharedCheck_5293_;
goto v_resetjp_5287_;
}
v_resetjp_5287_:
{
lean_object* v___x_5291_; 
if (v_isShared_5289_ == 0)
{
v___x_5291_ = v___x_5288_;
goto v_reusejp_5290_;
}
else
{
lean_object* v_reuseFailAlloc_5292_; 
v_reuseFailAlloc_5292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5292_, 0, v_a_5286_);
v___x_5291_ = v_reuseFailAlloc_5292_;
goto v_reusejp_5290_;
}
v_reusejp_5290_:
{
return v___x_5291_;
}
}
}
}
v___jp_5082_:
{
size_t v___x_5084_; size_t v___x_5085_; 
v___x_5084_ = ((size_t)1ULL);
v___x_5085_ = lean_usize_add(v_i_5073_, v___x_5084_);
v_i_5073_ = v___x_5085_;
v_b_5074_ = v_a_5083_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3___boxed(lean_object* v_mvarId_5294_, lean_object* v_config_5295_, lean_object* v_as_5296_, lean_object* v_sz_5297_, lean_object* v_i_5298_, lean_object* v_b_5299_, lean_object* v___y_5300_, lean_object* v___y_5301_, lean_object* v___y_5302_, lean_object* v___y_5303_, lean_object* v___y_5304_, lean_object* v___y_5305_, lean_object* v___y_5306_){
_start:
{
size_t v_sz_boxed_5307_; size_t v_i_boxed_5308_; lean_object* v_res_5309_; 
v_sz_boxed_5307_ = lean_unbox_usize(v_sz_5297_);
lean_dec(v_sz_5297_);
v_i_boxed_5308_ = lean_unbox_usize(v_i_5298_);
lean_dec(v_i_5298_);
v_res_5309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3(v_mvarId_5294_, v_config_5295_, v_as_5296_, v_sz_boxed_5307_, v_i_boxed_5308_, v_b_5299_, v___y_5300_, v___y_5301_, v___y_5302_, v___y_5303_, v___y_5304_, v___y_5305_);
lean_dec(v___y_5305_);
lean_dec_ref(v___y_5304_);
lean_dec(v___y_5303_);
lean_dec_ref(v___y_5302_);
lean_dec(v___y_5301_);
lean_dec_ref(v___y_5300_);
lean_dec_ref(v_as_5296_);
return v_res_5309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1(lean_object* v_mvarId_5310_, lean_object* v_config_5311_, lean_object* v_fvarIdsToSimp_5312_, size_t v_sz_5313_, size_t v___x_5314_, lean_object* v___x_5315_, uint8_t v_simplifyTarget_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_, lean_object* v___y_5320_, lean_object* v___y_5321_, lean_object* v___y_5322_){
_start:
{
lean_object* v___y_5325_; lean_object* v___y_5326_; lean_object* v___y_5327_; lean_object* v___y_5328_; lean_object* v___y_5329_; uint8_t v___y_5330_; lean_object* v___x_5350_; 
lean_inc_ref(v_config_5311_);
lean_inc(v_mvarId_5310_);
v___x_5350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__3(v_mvarId_5310_, v_config_5311_, v_fvarIdsToSimp_5312_, v_sz_5313_, v___x_5314_, v___x_5315_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_);
if (lean_obj_tag(v___x_5350_) == 0)
{
lean_object* v_a_5351_; lean_object* v___x_5353_; uint8_t v_isShared_5354_; uint8_t v_isSharedCheck_5553_; 
v_a_5351_ = lean_ctor_get(v___x_5350_, 0);
v_isSharedCheck_5553_ = !lean_is_exclusive(v___x_5350_);
if (v_isSharedCheck_5553_ == 0)
{
v___x_5353_ = v___x_5350_;
v_isShared_5354_ = v_isSharedCheck_5553_;
goto v_resetjp_5352_;
}
else
{
lean_inc(v_a_5351_);
lean_dec(v___x_5350_);
v___x_5353_ = lean_box(0);
v_isShared_5354_ = v_isSharedCheck_5553_;
goto v_resetjp_5352_;
}
v_resetjp_5352_:
{
lean_object* v_fst_5355_; lean_object* v_snd_5356_; lean_object* v___x_5358_; uint8_t v_isShared_5359_; uint8_t v_isSharedCheck_5552_; 
v_fst_5355_ = lean_ctor_get(v_a_5351_, 0);
v_snd_5356_ = lean_ctor_get(v_a_5351_, 1);
v_isSharedCheck_5552_ = !lean_is_exclusive(v_a_5351_);
if (v_isSharedCheck_5552_ == 0)
{
v___x_5358_ = v_a_5351_;
v_isShared_5359_ = v_isSharedCheck_5552_;
goto v_resetjp_5357_;
}
else
{
lean_inc(v_snd_5356_);
lean_inc(v_fst_5355_);
lean_dec(v_a_5351_);
v___x_5358_ = lean_box(0);
v_isShared_5359_ = v_isSharedCheck_5552_;
goto v_resetjp_5357_;
}
v_resetjp_5357_:
{
lean_object* v_mvarIdNew_5361_; lean_object* v___y_5362_; lean_object* v___y_5363_; lean_object* v___y_5364_; lean_object* v___y_5365_; lean_object* v___y_5412_; 
if (lean_obj_tag(v_fst_5355_) == 0)
{
lean_del_object(v___x_5353_);
if (v_simplifyTarget_5316_ == 0)
{
lean_del_object(v___x_5358_);
lean_dec_ref(v_config_5311_);
v_mvarIdNew_5361_ = v_mvarId_5310_;
v___y_5362_ = v___y_5319_;
v___y_5363_ = v___y_5320_;
v___y_5364_ = v___y_5321_;
v___y_5365_ = v___y_5322_;
goto v___jp_5360_;
}
else
{
lean_object* v___x_5455_; 
lean_inc(v_mvarId_5310_);
v___x_5455_ = l_Lean_MVarId_getType(v_mvarId_5310_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_);
if (lean_obj_tag(v___x_5455_) == 0)
{
lean_object* v_options_5456_; uint8_t v_hasTrace_5457_; 
v_options_5456_ = lean_ctor_get(v___y_5321_, 2);
v_hasTrace_5457_ = lean_ctor_get_uint8(v_options_5456_, sizeof(void*)*1);
if (v_hasTrace_5457_ == 0)
{
lean_object* v_a_5458_; lean_object* v___x_5459_; 
lean_del_object(v___x_5358_);
v_a_5458_ = lean_ctor_get(v___x_5455_, 0);
lean_inc(v_a_5458_);
lean_dec_ref_known(v___x_5455_, 1);
v___x_5459_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5458_, v_config_5311_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_);
v___y_5412_ = v___x_5459_;
goto v___jp_5411_;
}
else
{
lean_object* v_a_5460_; lean_object* v_inheritedTraceOptions_5461_; lean_object* v___f_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; lean_object* v___x_5465_; uint8_t v___x_5466_; lean_object* v___y_5468_; lean_object* v___y_5469_; lean_object* v_a_5470_; lean_object* v___y_5485_; lean_object* v___y_5486_; lean_object* v_a_5487_; 
v_a_5460_ = lean_ctor_get(v___x_5455_, 0);
lean_inc_n(v_a_5460_, 2);
lean_dec_ref_known(v___x_5455_, 1);
v_inheritedTraceOptions_5461_ = lean_ctor_get(v___y_5321_, 13);
v___f_5462_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__0___boxed), 9, 1);
lean_closure_set(v___f_5462_, 0, v_a_5460_);
v___x_5463_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
v___x_5464_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_5465_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_5466_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5461_, v_options_5456_, v___x_5465_);
if (v___x_5466_ == 0)
{
lean_object* v___x_5537_; uint8_t v___x_5538_; 
v___x_5537_ = l_Lean_trace_profiler;
v___x_5538_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5456_, v___x_5537_);
if (v___x_5538_ == 0)
{
lean_object* v___x_5539_; 
lean_dec_ref(v___f_5462_);
lean_del_object(v___x_5358_);
v___x_5539_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5460_, v_config_5311_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_);
v___y_5412_ = v___x_5539_;
goto v___jp_5411_;
}
else
{
goto v___jp_5496_;
}
}
else
{
goto v___jp_5496_;
}
v___jp_5467_:
{
lean_object* v___x_5471_; double v___x_5472_; double v___x_5473_; double v___x_5474_; double v___x_5475_; double v___x_5476_; lean_object* v___x_5477_; lean_object* v___x_5478_; lean_object* v___x_5480_; 
v___x_5471_ = lean_io_mono_nanos_now();
v___x_5472_ = lean_float_of_nat(v___y_5468_);
v___x_5473_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_5474_ = lean_float_div(v___x_5472_, v___x_5473_);
v___x_5475_ = lean_float_of_nat(v___x_5471_);
v___x_5476_ = lean_float_div(v___x_5475_, v___x_5473_);
v___x_5477_ = lean_box_float(v___x_5474_);
v___x_5478_ = lean_box_float(v___x_5476_);
if (v_isShared_5359_ == 0)
{
lean_ctor_set(v___x_5358_, 1, v___x_5478_);
lean_ctor_set(v___x_5358_, 0, v___x_5477_);
v___x_5480_ = v___x_5358_;
goto v_reusejp_5479_;
}
else
{
lean_object* v_reuseFailAlloc_5483_; 
v_reuseFailAlloc_5483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5483_, 0, v___x_5477_);
lean_ctor_set(v_reuseFailAlloc_5483_, 1, v___x_5478_);
v___x_5480_ = v_reuseFailAlloc_5483_;
goto v_reusejp_5479_;
}
v_reusejp_5479_:
{
lean_object* v___x_5481_; lean_object* v___x_5482_; 
v___x_5481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5481_, 0, v_a_5470_);
lean_ctor_set(v___x_5481_, 1, v___x_5480_);
v___x_5482_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v___x_5463_, v_hasTrace_5457_, v___x_5464_, v_options_5456_, v___x_5466_, v___y_5469_, v___f_5462_, v___x_5481_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_);
v___y_5412_ = v___x_5482_;
goto v___jp_5411_;
}
}
v___jp_5484_:
{
lean_object* v___x_5488_; double v___x_5489_; double v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; lean_object* v___x_5493_; lean_object* v___x_5494_; lean_object* v___x_5495_; 
v___x_5488_ = lean_io_get_num_heartbeats();
v___x_5489_ = lean_float_of_nat(v___y_5485_);
v___x_5490_ = lean_float_of_nat(v___x_5488_);
v___x_5491_ = lean_box_float(v___x_5489_);
v___x_5492_ = lean_box_float(v___x_5490_);
v___x_5493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5493_, 0, v___x_5491_);
lean_ctor_set(v___x_5493_, 1, v___x_5492_);
v___x_5494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5494_, 0, v_a_5487_);
lean_ctor_set(v___x_5494_, 1, v___x_5493_);
v___x_5495_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2(v___x_5463_, v_hasTrace_5457_, v___x_5464_, v_options_5456_, v___x_5466_, v___y_5486_, v___f_5462_, v___x_5494_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_);
v___y_5412_ = v___x_5495_;
goto v___jp_5411_;
}
v___jp_5496_:
{
lean_object* v___x_5497_; lean_object* v_a_5498_; lean_object* v___x_5499_; uint8_t v___x_5500_; 
v___x_5497_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__1___redArg(v___y_5322_);
v_a_5498_ = lean_ctor_get(v___x_5497_, 0);
lean_inc(v_a_5498_);
lean_dec_ref(v___x_5497_);
v___x_5499_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5500_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_5456_, v___x_5499_);
if (v___x_5500_ == 0)
{
lean_object* v___x_5501_; lean_object* v___x_5502_; 
v___x_5501_ = lean_io_mono_nanos_now();
v___x_5502_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5460_, v_config_5311_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_);
if (lean_obj_tag(v___x_5502_) == 0)
{
lean_object* v_a_5503_; lean_object* v___x_5505_; uint8_t v_isShared_5506_; uint8_t v_isSharedCheck_5510_; 
v_a_5503_ = lean_ctor_get(v___x_5502_, 0);
v_isSharedCheck_5510_ = !lean_is_exclusive(v___x_5502_);
if (v_isSharedCheck_5510_ == 0)
{
v___x_5505_ = v___x_5502_;
v_isShared_5506_ = v_isSharedCheck_5510_;
goto v_resetjp_5504_;
}
else
{
lean_inc(v_a_5503_);
lean_dec(v___x_5502_);
v___x_5505_ = lean_box(0);
v_isShared_5506_ = v_isSharedCheck_5510_;
goto v_resetjp_5504_;
}
v_resetjp_5504_:
{
lean_object* v___x_5508_; 
if (v_isShared_5506_ == 0)
{
lean_ctor_set_tag(v___x_5505_, 1);
v___x_5508_ = v___x_5505_;
goto v_reusejp_5507_;
}
else
{
lean_object* v_reuseFailAlloc_5509_; 
v_reuseFailAlloc_5509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5509_, 0, v_a_5503_);
v___x_5508_ = v_reuseFailAlloc_5509_;
goto v_reusejp_5507_;
}
v_reusejp_5507_:
{
v___y_5468_ = v___x_5501_;
v___y_5469_ = v_a_5498_;
v_a_5470_ = v___x_5508_;
goto v___jp_5467_;
}
}
}
else
{
lean_object* v_a_5511_; lean_object* v___x_5513_; uint8_t v_isShared_5514_; uint8_t v_isSharedCheck_5518_; 
v_a_5511_ = lean_ctor_get(v___x_5502_, 0);
v_isSharedCheck_5518_ = !lean_is_exclusive(v___x_5502_);
if (v_isSharedCheck_5518_ == 0)
{
v___x_5513_ = v___x_5502_;
v_isShared_5514_ = v_isSharedCheck_5518_;
goto v_resetjp_5512_;
}
else
{
lean_inc(v_a_5511_);
lean_dec(v___x_5502_);
v___x_5513_ = lean_box(0);
v_isShared_5514_ = v_isSharedCheck_5518_;
goto v_resetjp_5512_;
}
v_resetjp_5512_:
{
lean_object* v___x_5516_; 
if (v_isShared_5514_ == 0)
{
lean_ctor_set_tag(v___x_5513_, 0);
v___x_5516_ = v___x_5513_;
goto v_reusejp_5515_;
}
else
{
lean_object* v_reuseFailAlloc_5517_; 
v_reuseFailAlloc_5517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5517_, 0, v_a_5511_);
v___x_5516_ = v_reuseFailAlloc_5517_;
goto v_reusejp_5515_;
}
v_reusejp_5515_:
{
v___y_5468_ = v___x_5501_;
v___y_5469_ = v_a_5498_;
v_a_5470_ = v___x_5516_;
goto v___jp_5467_;
}
}
}
}
else
{
lean_object* v___x_5519_; lean_object* v___x_5520_; 
lean_del_object(v___x_5358_);
v___x_5519_ = lean_io_get_num_heartbeats();
v___x_5520_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v_a_5460_, v_config_5311_, v___y_5317_, v___y_5318_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_);
if (lean_obj_tag(v___x_5520_) == 0)
{
lean_object* v_a_5521_; lean_object* v___x_5523_; uint8_t v_isShared_5524_; uint8_t v_isSharedCheck_5528_; 
v_a_5521_ = lean_ctor_get(v___x_5520_, 0);
v_isSharedCheck_5528_ = !lean_is_exclusive(v___x_5520_);
if (v_isSharedCheck_5528_ == 0)
{
v___x_5523_ = v___x_5520_;
v_isShared_5524_ = v_isSharedCheck_5528_;
goto v_resetjp_5522_;
}
else
{
lean_inc(v_a_5521_);
lean_dec(v___x_5520_);
v___x_5523_ = lean_box(0);
v_isShared_5524_ = v_isSharedCheck_5528_;
goto v_resetjp_5522_;
}
v_resetjp_5522_:
{
lean_object* v___x_5526_; 
if (v_isShared_5524_ == 0)
{
lean_ctor_set_tag(v___x_5523_, 1);
v___x_5526_ = v___x_5523_;
goto v_reusejp_5525_;
}
else
{
lean_object* v_reuseFailAlloc_5527_; 
v_reuseFailAlloc_5527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5527_, 0, v_a_5521_);
v___x_5526_ = v_reuseFailAlloc_5527_;
goto v_reusejp_5525_;
}
v_reusejp_5525_:
{
v___y_5485_ = v___x_5519_;
v___y_5486_ = v_a_5498_;
v_a_5487_ = v___x_5526_;
goto v___jp_5484_;
}
}
}
else
{
lean_object* v_a_5529_; lean_object* v___x_5531_; uint8_t v_isShared_5532_; uint8_t v_isSharedCheck_5536_; 
v_a_5529_ = lean_ctor_get(v___x_5520_, 0);
v_isSharedCheck_5536_ = !lean_is_exclusive(v___x_5520_);
if (v_isSharedCheck_5536_ == 0)
{
v___x_5531_ = v___x_5520_;
v_isShared_5532_ = v_isSharedCheck_5536_;
goto v_resetjp_5530_;
}
else
{
lean_inc(v_a_5529_);
lean_dec(v___x_5520_);
v___x_5531_ = lean_box(0);
v_isShared_5532_ = v_isSharedCheck_5536_;
goto v_resetjp_5530_;
}
v_resetjp_5530_:
{
lean_object* v___x_5534_; 
if (v_isShared_5532_ == 0)
{
lean_ctor_set_tag(v___x_5531_, 0);
v___x_5534_ = v___x_5531_;
goto v_reusejp_5533_;
}
else
{
lean_object* v_reuseFailAlloc_5535_; 
v_reuseFailAlloc_5535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5535_, 0, v_a_5529_);
v___x_5534_ = v_reuseFailAlloc_5535_;
goto v_reusejp_5533_;
}
v_reusejp_5533_:
{
v___y_5485_ = v___x_5519_;
v___y_5486_ = v_a_5498_;
v_a_5487_ = v___x_5534_;
goto v___jp_5484_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5540_; lean_object* v___x_5542_; uint8_t v_isShared_5543_; uint8_t v_isSharedCheck_5547_; 
lean_del_object(v___x_5358_);
lean_dec(v_snd_5356_);
lean_dec_ref(v_config_5311_);
lean_dec(v_mvarId_5310_);
v_a_5540_ = lean_ctor_get(v___x_5455_, 0);
v_isSharedCheck_5547_ = !lean_is_exclusive(v___x_5455_);
if (v_isSharedCheck_5547_ == 0)
{
v___x_5542_ = v___x_5455_;
v_isShared_5543_ = v_isSharedCheck_5547_;
goto v_resetjp_5541_;
}
else
{
lean_inc(v_a_5540_);
lean_dec(v___x_5455_);
v___x_5542_ = lean_box(0);
v_isShared_5543_ = v_isSharedCheck_5547_;
goto v_resetjp_5541_;
}
v_resetjp_5541_:
{
lean_object* v___x_5545_; 
if (v_isShared_5543_ == 0)
{
v___x_5545_ = v___x_5542_;
goto v_reusejp_5544_;
}
else
{
lean_object* v_reuseFailAlloc_5546_; 
v_reuseFailAlloc_5546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5546_, 0, v_a_5540_);
v___x_5545_ = v_reuseFailAlloc_5546_;
goto v_reusejp_5544_;
}
v_reusejp_5544_:
{
return v___x_5545_;
}
}
}
}
}
else
{
lean_object* v_val_5548_; lean_object* v___x_5550_; 
lean_del_object(v___x_5358_);
lean_dec(v_snd_5356_);
lean_dec_ref(v_config_5311_);
lean_dec(v_mvarId_5310_);
v_val_5548_ = lean_ctor_get(v_fst_5355_, 0);
lean_inc(v_val_5548_);
lean_dec_ref_known(v_fst_5355_, 1);
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 0, v_val_5548_);
v___x_5550_ = v___x_5353_;
goto v_reusejp_5549_;
}
else
{
lean_object* v_reuseFailAlloc_5551_; 
v_reuseFailAlloc_5551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5551_, 0, v_val_5548_);
v___x_5550_ = v_reuseFailAlloc_5551_;
goto v_reusejp_5549_;
}
v_reusejp_5549_:
{
return v___x_5550_;
}
}
v___jp_5360_:
{
lean_object* v___x_5366_; 
v___x_5366_ = l_Lean_MVarId_assertHypotheses(v_mvarIdNew_5361_, v_snd_5356_, v___y_5362_, v___y_5363_, v___y_5364_, v___y_5365_);
if (lean_obj_tag(v___x_5366_) == 0)
{
lean_object* v_a_5367_; lean_object* v_snd_5368_; lean_object* v___x_5369_; 
v_a_5367_ = lean_ctor_get(v___x_5366_, 0);
lean_inc(v_a_5367_);
lean_dec_ref_known(v___x_5366_, 1);
v_snd_5368_ = lean_ctor_get(v_a_5367_, 1);
lean_inc(v_snd_5368_);
lean_dec(v_a_5367_);
v___x_5369_ = l_Lean_MVarId_tryClearMany(v_snd_5368_, v_fvarIdsToSimp_5312_, v___y_5362_, v___y_5363_, v___y_5364_, v___y_5365_);
if (lean_obj_tag(v___x_5369_) == 0)
{
lean_object* v_a_5370_; lean_object* v___x_5371_; 
v_a_5370_ = lean_ctor_get(v___x_5369_, 0);
lean_inc(v_a_5370_);
lean_dec_ref_known(v___x_5369_, 1);
v___x_5371_ = l_Lean_Meta_saveState___redArg(v___y_5363_, v___y_5365_);
if (lean_obj_tag(v___x_5371_) == 0)
{
lean_object* v_a_5372_; uint8_t v___x_5373_; lean_object* v___x_5374_; 
v_a_5372_ = lean_ctor_get(v___x_5371_, 0);
lean_inc(v_a_5372_);
lean_dec_ref_known(v___x_5371_, 1);
v___x_5373_ = 1;
lean_inc(v_a_5370_);
v___x_5374_ = l_Lean_MVarId_refl(v_a_5370_, v___x_5373_, v___y_5362_, v___y_5363_, v___y_5364_, v___y_5365_);
if (lean_obj_tag(v___x_5374_) == 0)
{
lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5382_; 
lean_dec(v_a_5372_);
lean_dec(v_a_5370_);
v_isSharedCheck_5382_ = !lean_is_exclusive(v___x_5374_);
if (v_isSharedCheck_5382_ == 0)
{
lean_object* v_unused_5383_; 
v_unused_5383_ = lean_ctor_get(v___x_5374_, 0);
lean_dec(v_unused_5383_);
v___x_5376_ = v___x_5374_;
v_isShared_5377_ = v_isSharedCheck_5382_;
goto v_resetjp_5375_;
}
else
{
lean_dec(v___x_5374_);
v___x_5376_ = lean_box(0);
v_isShared_5377_ = v_isSharedCheck_5382_;
goto v_resetjp_5375_;
}
v_resetjp_5375_:
{
lean_object* v___x_5378_; lean_object* v___x_5380_; 
v___x_5378_ = lean_box(0);
if (v_isShared_5377_ == 0)
{
lean_ctor_set(v___x_5376_, 0, v___x_5378_);
v___x_5380_ = v___x_5376_;
goto v_reusejp_5379_;
}
else
{
lean_object* v_reuseFailAlloc_5381_; 
v_reuseFailAlloc_5381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5381_, 0, v___x_5378_);
v___x_5380_ = v_reuseFailAlloc_5381_;
goto v_reusejp_5379_;
}
v_reusejp_5379_:
{
return v___x_5380_;
}
}
}
else
{
lean_object* v_a_5384_; uint8_t v___x_5385_; 
v_a_5384_ = lean_ctor_get(v___x_5374_, 0);
lean_inc(v_a_5384_);
lean_dec_ref_known(v___x_5374_, 1);
v___x_5385_ = l_Lean_Exception_isInterrupt(v_a_5384_);
if (v___x_5385_ == 0)
{
uint8_t v___x_5386_; 
lean_inc(v_a_5384_);
v___x_5386_ = l_Lean_Exception_isRuntime(v_a_5384_);
v___y_5325_ = v___y_5365_;
v___y_5326_ = v_a_5370_;
v___y_5327_ = v_a_5384_;
v___y_5328_ = v___y_5363_;
v___y_5329_ = v_a_5372_;
v___y_5330_ = v___x_5386_;
goto v___jp_5324_;
}
else
{
v___y_5325_ = v___y_5365_;
v___y_5326_ = v_a_5370_;
v___y_5327_ = v_a_5384_;
v___y_5328_ = v___y_5363_;
v___y_5329_ = v_a_5372_;
v___y_5330_ = v___x_5385_;
goto v___jp_5324_;
}
}
}
else
{
lean_object* v_a_5387_; lean_object* v___x_5389_; uint8_t v_isShared_5390_; uint8_t v_isSharedCheck_5394_; 
lean_dec(v_a_5370_);
v_a_5387_ = lean_ctor_get(v___x_5371_, 0);
v_isSharedCheck_5394_ = !lean_is_exclusive(v___x_5371_);
if (v_isSharedCheck_5394_ == 0)
{
v___x_5389_ = v___x_5371_;
v_isShared_5390_ = v_isSharedCheck_5394_;
goto v_resetjp_5388_;
}
else
{
lean_inc(v_a_5387_);
lean_dec(v___x_5371_);
v___x_5389_ = lean_box(0);
v_isShared_5390_ = v_isSharedCheck_5394_;
goto v_resetjp_5388_;
}
v_resetjp_5388_:
{
lean_object* v___x_5392_; 
if (v_isShared_5390_ == 0)
{
v___x_5392_ = v___x_5389_;
goto v_reusejp_5391_;
}
else
{
lean_object* v_reuseFailAlloc_5393_; 
v_reuseFailAlloc_5393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5393_, 0, v_a_5387_);
v___x_5392_ = v_reuseFailAlloc_5393_;
goto v_reusejp_5391_;
}
v_reusejp_5391_:
{
return v___x_5392_;
}
}
}
}
else
{
lean_object* v_a_5395_; lean_object* v___x_5397_; uint8_t v_isShared_5398_; uint8_t v_isSharedCheck_5402_; 
v_a_5395_ = lean_ctor_get(v___x_5369_, 0);
v_isSharedCheck_5402_ = !lean_is_exclusive(v___x_5369_);
if (v_isSharedCheck_5402_ == 0)
{
v___x_5397_ = v___x_5369_;
v_isShared_5398_ = v_isSharedCheck_5402_;
goto v_resetjp_5396_;
}
else
{
lean_inc(v_a_5395_);
lean_dec(v___x_5369_);
v___x_5397_ = lean_box(0);
v_isShared_5398_ = v_isSharedCheck_5402_;
goto v_resetjp_5396_;
}
v_resetjp_5396_:
{
lean_object* v___x_5400_; 
if (v_isShared_5398_ == 0)
{
v___x_5400_ = v___x_5397_;
goto v_reusejp_5399_;
}
else
{
lean_object* v_reuseFailAlloc_5401_; 
v_reuseFailAlloc_5401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5401_, 0, v_a_5395_);
v___x_5400_ = v_reuseFailAlloc_5401_;
goto v_reusejp_5399_;
}
v_reusejp_5399_:
{
return v___x_5400_;
}
}
}
}
else
{
lean_object* v_a_5403_; lean_object* v___x_5405_; uint8_t v_isShared_5406_; uint8_t v_isSharedCheck_5410_; 
v_a_5403_ = lean_ctor_get(v___x_5366_, 0);
v_isSharedCheck_5410_ = !lean_is_exclusive(v___x_5366_);
if (v_isSharedCheck_5410_ == 0)
{
v___x_5405_ = v___x_5366_;
v_isShared_5406_ = v_isSharedCheck_5410_;
goto v_resetjp_5404_;
}
else
{
lean_inc(v_a_5403_);
lean_dec(v___x_5366_);
v___x_5405_ = lean_box(0);
v_isShared_5406_ = v_isSharedCheck_5410_;
goto v_resetjp_5404_;
}
v_resetjp_5404_:
{
lean_object* v___x_5408_; 
if (v_isShared_5406_ == 0)
{
v___x_5408_ = v___x_5405_;
goto v_reusejp_5407_;
}
else
{
lean_object* v_reuseFailAlloc_5409_; 
v_reuseFailAlloc_5409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5409_, 0, v_a_5403_);
v___x_5408_ = v_reuseFailAlloc_5409_;
goto v_reusejp_5407_;
}
v_reusejp_5407_:
{
return v___x_5408_;
}
}
}
}
v___jp_5411_:
{
if (lean_obj_tag(v___y_5412_) == 0)
{
lean_object* v_a_5413_; 
v_a_5413_ = lean_ctor_get(v___y_5412_, 0);
lean_inc(v_a_5413_);
lean_dec_ref_known(v___y_5412_, 1);
if (lean_obj_tag(v_a_5413_) == 0)
{
lean_dec_ref_known(v_a_5413_, 0);
v_mvarIdNew_5361_ = v_mvarId_5310_;
v___y_5362_ = v___y_5319_;
v___y_5363_ = v___y_5320_;
v___y_5364_ = v___y_5321_;
v___y_5365_ = v___y_5322_;
goto v___jp_5360_;
}
else
{
lean_object* v_e_x27_5414_; lean_object* v_proof_5415_; uint8_t v___x_5416_; 
v_e_x27_5414_ = lean_ctor_get(v_a_5413_, 0);
lean_inc_ref_n(v_e_x27_5414_, 2);
v_proof_5415_ = lean_ctor_get(v_a_5413_, 1);
lean_inc_ref(v_proof_5415_);
lean_dec_ref_known(v_a_5413_, 2);
v___x_5416_ = l_Lean_Expr_isTrue(v_e_x27_5414_);
if (v___x_5416_ == 0)
{
lean_object* v___x_5417_; 
v___x_5417_ = l_Lean_MVarId_replaceTargetEq(v_mvarId_5310_, v_e_x27_5414_, v_proof_5415_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_);
if (lean_obj_tag(v___x_5417_) == 0)
{
lean_object* v_a_5418_; 
v_a_5418_ = lean_ctor_get(v___x_5417_, 0);
lean_inc(v_a_5418_);
lean_dec_ref_known(v___x_5417_, 1);
v_mvarIdNew_5361_ = v_a_5418_;
v___y_5362_ = v___y_5319_;
v___y_5363_ = v___y_5320_;
v___y_5364_ = v___y_5321_;
v___y_5365_ = v___y_5322_;
goto v___jp_5360_;
}
else
{
lean_object* v_a_5419_; lean_object* v___x_5421_; uint8_t v_isShared_5422_; uint8_t v_isSharedCheck_5426_; 
lean_dec(v_snd_5356_);
v_a_5419_ = lean_ctor_get(v___x_5417_, 0);
v_isSharedCheck_5426_ = !lean_is_exclusive(v___x_5417_);
if (v_isSharedCheck_5426_ == 0)
{
v___x_5421_ = v___x_5417_;
v_isShared_5422_ = v_isSharedCheck_5426_;
goto v_resetjp_5420_;
}
else
{
lean_inc(v_a_5419_);
lean_dec(v___x_5417_);
v___x_5421_ = lean_box(0);
v_isShared_5422_ = v_isSharedCheck_5426_;
goto v_resetjp_5420_;
}
v_resetjp_5420_:
{
lean_object* v___x_5424_; 
if (v_isShared_5422_ == 0)
{
v___x_5424_ = v___x_5421_;
goto v_reusejp_5423_;
}
else
{
lean_object* v_reuseFailAlloc_5425_; 
v_reuseFailAlloc_5425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5425_, 0, v_a_5419_);
v___x_5424_ = v_reuseFailAlloc_5425_;
goto v_reusejp_5423_;
}
v_reusejp_5423_:
{
return v___x_5424_;
}
}
}
}
else
{
lean_object* v___x_5427_; 
lean_dec_ref(v_e_x27_5414_);
lean_dec(v_snd_5356_);
v___x_5427_ = l_Lean_Meta_mkOfEqTrue(v_proof_5415_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_);
if (lean_obj_tag(v___x_5427_) == 0)
{
lean_object* v_a_5428_; lean_object* v___x_5429_; lean_object* v___x_5431_; uint8_t v_isShared_5432_; uint8_t v_isSharedCheck_5437_; 
v_a_5428_ = lean_ctor_get(v___x_5427_, 0);
lean_inc(v_a_5428_);
lean_dec_ref_known(v___x_5427_, 1);
v___x_5429_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(v_mvarId_5310_, v_a_5428_, v___y_5320_);
v_isSharedCheck_5437_ = !lean_is_exclusive(v___x_5429_);
if (v_isSharedCheck_5437_ == 0)
{
lean_object* v_unused_5438_; 
v_unused_5438_ = lean_ctor_get(v___x_5429_, 0);
lean_dec(v_unused_5438_);
v___x_5431_ = v___x_5429_;
v_isShared_5432_ = v_isSharedCheck_5437_;
goto v_resetjp_5430_;
}
else
{
lean_dec(v___x_5429_);
v___x_5431_ = lean_box(0);
v_isShared_5432_ = v_isSharedCheck_5437_;
goto v_resetjp_5430_;
}
v_resetjp_5430_:
{
lean_object* v___x_5433_; lean_object* v___x_5435_; 
v___x_5433_ = lean_box(0);
if (v_isShared_5432_ == 0)
{
lean_ctor_set(v___x_5431_, 0, v___x_5433_);
v___x_5435_ = v___x_5431_;
goto v_reusejp_5434_;
}
else
{
lean_object* v_reuseFailAlloc_5436_; 
v_reuseFailAlloc_5436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5436_, 0, v___x_5433_);
v___x_5435_ = v_reuseFailAlloc_5436_;
goto v_reusejp_5434_;
}
v_reusejp_5434_:
{
return v___x_5435_;
}
}
}
else
{
lean_object* v_a_5439_; lean_object* v___x_5441_; uint8_t v_isShared_5442_; uint8_t v_isSharedCheck_5446_; 
lean_dec(v_mvarId_5310_);
v_a_5439_ = lean_ctor_get(v___x_5427_, 0);
v_isSharedCheck_5446_ = !lean_is_exclusive(v___x_5427_);
if (v_isSharedCheck_5446_ == 0)
{
v___x_5441_ = v___x_5427_;
v_isShared_5442_ = v_isSharedCheck_5446_;
goto v_resetjp_5440_;
}
else
{
lean_inc(v_a_5439_);
lean_dec(v___x_5427_);
v___x_5441_ = lean_box(0);
v_isShared_5442_ = v_isSharedCheck_5446_;
goto v_resetjp_5440_;
}
v_resetjp_5440_:
{
lean_object* v___x_5444_; 
if (v_isShared_5442_ == 0)
{
v___x_5444_ = v___x_5441_;
goto v_reusejp_5443_;
}
else
{
lean_object* v_reuseFailAlloc_5445_; 
v_reuseFailAlloc_5445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5445_, 0, v_a_5439_);
v___x_5444_ = v_reuseFailAlloc_5445_;
goto v_reusejp_5443_;
}
v_reusejp_5443_:
{
return v___x_5444_;
}
}
}
}
}
}
else
{
lean_object* v_a_5447_; lean_object* v___x_5449_; uint8_t v_isShared_5450_; uint8_t v_isSharedCheck_5454_; 
lean_dec(v_snd_5356_);
lean_dec(v_mvarId_5310_);
v_a_5447_ = lean_ctor_get(v___y_5412_, 0);
v_isSharedCheck_5454_ = !lean_is_exclusive(v___y_5412_);
if (v_isSharedCheck_5454_ == 0)
{
v___x_5449_ = v___y_5412_;
v_isShared_5450_ = v_isSharedCheck_5454_;
goto v_resetjp_5448_;
}
else
{
lean_inc(v_a_5447_);
lean_dec(v___y_5412_);
v___x_5449_ = lean_box(0);
v_isShared_5450_ = v_isSharedCheck_5454_;
goto v_resetjp_5448_;
}
v_resetjp_5448_:
{
lean_object* v___x_5452_; 
if (v_isShared_5450_ == 0)
{
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
return v___x_5452_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5554_; lean_object* v___x_5556_; uint8_t v_isShared_5557_; uint8_t v_isSharedCheck_5561_; 
lean_dec_ref(v_config_5311_);
lean_dec(v_mvarId_5310_);
v_a_5554_ = lean_ctor_get(v___x_5350_, 0);
v_isSharedCheck_5561_ = !lean_is_exclusive(v___x_5350_);
if (v_isSharedCheck_5561_ == 0)
{
v___x_5556_ = v___x_5350_;
v_isShared_5557_ = v_isSharedCheck_5561_;
goto v_resetjp_5555_;
}
else
{
lean_inc(v_a_5554_);
lean_dec(v___x_5350_);
v___x_5556_ = lean_box(0);
v_isShared_5557_ = v_isSharedCheck_5561_;
goto v_resetjp_5555_;
}
v_resetjp_5555_:
{
lean_object* v___x_5559_; 
if (v_isShared_5557_ == 0)
{
v___x_5559_ = v___x_5556_;
goto v_reusejp_5558_;
}
else
{
lean_object* v_reuseFailAlloc_5560_; 
v_reuseFailAlloc_5560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5560_, 0, v_a_5554_);
v___x_5559_ = v_reuseFailAlloc_5560_;
goto v_reusejp_5558_;
}
v_reusejp_5558_:
{
return v___x_5559_;
}
}
}
v___jp_5324_:
{
if (v___y_5330_ == 0)
{
lean_object* v___x_5331_; 
lean_dec_ref(v___y_5327_);
v___x_5331_ = l_Lean_Meta_SavedState_restore___redArg(v___y_5329_, v___y_5328_, v___y_5325_);
lean_dec_ref(v___y_5329_);
if (lean_obj_tag(v___x_5331_) == 0)
{
lean_object* v___x_5333_; uint8_t v_isShared_5334_; uint8_t v_isSharedCheck_5339_; 
v_isSharedCheck_5339_ = !lean_is_exclusive(v___x_5331_);
if (v_isSharedCheck_5339_ == 0)
{
lean_object* v_unused_5340_; 
v_unused_5340_ = lean_ctor_get(v___x_5331_, 0);
lean_dec(v_unused_5340_);
v___x_5333_ = v___x_5331_;
v_isShared_5334_ = v_isSharedCheck_5339_;
goto v_resetjp_5332_;
}
else
{
lean_dec(v___x_5331_);
v___x_5333_ = lean_box(0);
v_isShared_5334_ = v_isSharedCheck_5339_;
goto v_resetjp_5332_;
}
v_resetjp_5332_:
{
lean_object* v___x_5335_; lean_object* v___x_5337_; 
v___x_5335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5335_, 0, v___y_5326_);
if (v_isShared_5334_ == 0)
{
lean_ctor_set(v___x_5333_, 0, v___x_5335_);
v___x_5337_ = v___x_5333_;
goto v_reusejp_5336_;
}
else
{
lean_object* v_reuseFailAlloc_5338_; 
v_reuseFailAlloc_5338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5338_, 0, v___x_5335_);
v___x_5337_ = v_reuseFailAlloc_5338_;
goto v_reusejp_5336_;
}
v_reusejp_5336_:
{
return v___x_5337_;
}
}
}
else
{
lean_object* v_a_5341_; lean_object* v___x_5343_; uint8_t v_isShared_5344_; uint8_t v_isSharedCheck_5348_; 
lean_dec(v___y_5326_);
v_a_5341_ = lean_ctor_get(v___x_5331_, 0);
v_isSharedCheck_5348_ = !lean_is_exclusive(v___x_5331_);
if (v_isSharedCheck_5348_ == 0)
{
v___x_5343_ = v___x_5331_;
v_isShared_5344_ = v_isSharedCheck_5348_;
goto v_resetjp_5342_;
}
else
{
lean_inc(v_a_5341_);
lean_dec(v___x_5331_);
v___x_5343_ = lean_box(0);
v_isShared_5344_ = v_isSharedCheck_5348_;
goto v_resetjp_5342_;
}
v_resetjp_5342_:
{
lean_object* v___x_5346_; 
if (v_isShared_5344_ == 0)
{
v___x_5346_ = v___x_5343_;
goto v_reusejp_5345_;
}
else
{
lean_object* v_reuseFailAlloc_5347_; 
v_reuseFailAlloc_5347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5347_, 0, v_a_5341_);
v___x_5346_ = v_reuseFailAlloc_5347_;
goto v_reusejp_5345_;
}
v_reusejp_5345_:
{
return v___x_5346_;
}
}
}
}
else
{
lean_object* v___x_5349_; 
lean_dec_ref(v___y_5329_);
lean_dec(v___y_5326_);
v___x_5349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5349_, 0, v___y_5327_);
return v___x_5349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1___boxed(lean_object* v_mvarId_5562_, lean_object* v_config_5563_, lean_object* v_fvarIdsToSimp_5564_, lean_object* v_sz_5565_, lean_object* v___x_5566_, lean_object* v___x_5567_, lean_object* v_simplifyTarget_5568_, lean_object* v___y_5569_, lean_object* v___y_5570_, lean_object* v___y_5571_, lean_object* v___y_5572_, lean_object* v___y_5573_, lean_object* v___y_5574_, lean_object* v___y_5575_){
_start:
{
size_t v_sz_boxed_5576_; size_t v___x_49233__boxed_5577_; uint8_t v_simplifyTarget_boxed_5578_; lean_object* v_res_5579_; 
v_sz_boxed_5576_ = lean_unbox_usize(v_sz_5565_);
lean_dec(v_sz_5565_);
v___x_49233__boxed_5577_ = lean_unbox_usize(v___x_5566_);
lean_dec(v___x_5566_);
v_simplifyTarget_boxed_5578_ = lean_unbox(v_simplifyTarget_5568_);
v_res_5579_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1(v_mvarId_5562_, v_config_5563_, v_fvarIdsToSimp_5564_, v_sz_boxed_5576_, v___x_49233__boxed_5577_, v___x_5567_, v_simplifyTarget_boxed_5578_, v___y_5569_, v___y_5570_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_);
lean_dec(v___y_5574_);
lean_dec_ref(v___y_5573_);
lean_dec(v___y_5572_);
lean_dec_ref(v___y_5571_);
lean_dec(v___y_5570_);
lean_dec_ref(v___y_5569_);
lean_dec_ref(v_fvarIdsToSimp_5564_);
return v_res_5579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2(lean_object* v_fvarIdsToSimp_5587_, lean_object* v_mvarId_5588_, uint8_t v_simplifyTarget_5589_, lean_object* v___y_5590_, lean_object* v___y_5591_, lean_object* v___y_5592_, lean_object* v___y_5593_, lean_object* v___y_5594_, lean_object* v___y_5595_){
_start:
{
lean_object* v_options_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; lean_object* v_config_5601_; lean_object* v___x_5602_; size_t v_sz_5603_; lean_object* v___x_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; lean_object* v___f_5607_; lean_object* v___x_5608_; 
v_options_5597_ = lean_ctor_get(v___y_5594_, 2);
v___x_5598_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_5599_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_5597_, v___x_5598_);
v___x_5600_ = lean_unsigned_to_nat(2u);
v_config_5601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_config_5601_, 0, v___x_5599_);
lean_ctor_set(v_config_5601_, 1, v___x_5600_);
v___x_5602_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___closed__1));
v_sz_5603_ = lean_array_size(v_fvarIdsToSimp_5587_);
v___x_5604_ = lean_box_usize(v_sz_5603_);
v___x_5605_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___boxed__const__1));
v___x_5606_ = lean_box(v_simplifyTarget_5589_);
lean_inc(v_mvarId_5588_);
v___f_5607_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__1___boxed), 14, 7);
lean_closure_set(v___f_5607_, 0, v_mvarId_5588_);
lean_closure_set(v___f_5607_, 1, v_config_5601_);
lean_closure_set(v___f_5607_, 2, v_fvarIdsToSimp_5587_);
lean_closure_set(v___f_5607_, 3, v___x_5604_);
lean_closure_set(v___f_5607_, 4, v___x_5605_);
lean_closure_set(v___f_5607_, 5, v___x_5602_);
lean_closure_set(v___f_5607_, 6, v___x_5606_);
v___x_5608_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__4___redArg(v_mvarId_5588_, v___f_5607_, v___y_5590_, v___y_5591_, v___y_5592_, v___y_5593_, v___y_5594_, v___y_5595_);
return v___x_5608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___boxed(lean_object* v_fvarIdsToSimp_5609_, lean_object* v_mvarId_5610_, lean_object* v_simplifyTarget_5611_, lean_object* v___y_5612_, lean_object* v___y_5613_, lean_object* v___y_5614_, lean_object* v___y_5615_, lean_object* v___y_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_){
_start:
{
uint8_t v_simplifyTarget_boxed_5619_; lean_object* v_res_5620_; 
v_simplifyTarget_boxed_5619_ = lean_unbox(v_simplifyTarget_5611_);
v_res_5620_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2(v_fvarIdsToSimp_5609_, v_mvarId_5610_, v_simplifyTarget_boxed_5619_, v___y_5612_, v___y_5613_, v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_);
lean_dec(v___y_5617_);
lean_dec_ref(v___y_5616_);
lean_dec(v___y_5615_);
lean_dec_ref(v___y_5614_);
lean_dec(v___y_5613_);
lean_dec_ref(v___y_5612_);
return v_res_5620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore(lean_object* v_mvarId_5621_, uint8_t v_simplifyTarget_5622_, lean_object* v_fvarIdsToSimp_5623_, lean_object* v_a_5624_, lean_object* v_a_5625_, lean_object* v_a_5626_, lean_object* v_a_5627_, lean_object* v_a_5628_, lean_object* v_a_5629_){
_start:
{
lean_object* v___x_5631_; lean_object* v___f_5632_; lean_object* v___x_5633_; 
v___x_5631_ = lean_box(v_simplifyTarget_5622_);
v___f_5632_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoalCore___lam__2___boxed), 10, 3);
lean_closure_set(v___f_5632_, 0, v_fvarIdsToSimp_5623_);
lean_closure_set(v___f_5632_, 1, v_mvarId_5621_);
lean_closure_set(v___f_5632_, 2, v___x_5631_);
v___x_5633_ = l_Lean_Meta_Sym_withoutShareCommonChecks___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore_spec__0___redArg(v___f_5632_, v_a_5624_, v_a_5625_, v_a_5626_, v_a_5627_, v_a_5628_, v_a_5629_);
return v___x_5633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoalCore___boxed(lean_object* v_mvarId_5634_, lean_object* v_simplifyTarget_5635_, lean_object* v_fvarIdsToSimp_5636_, lean_object* v_a_5637_, lean_object* v_a_5638_, lean_object* v_a_5639_, lean_object* v_a_5640_, lean_object* v_a_5641_, lean_object* v_a_5642_, lean_object* v_a_5643_){
_start:
{
uint8_t v_simplifyTarget_boxed_5644_; lean_object* v_res_5645_; 
v_simplifyTarget_boxed_5644_ = lean_unbox(v_simplifyTarget_5635_);
v_res_5645_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore(v_mvarId_5634_, v_simplifyTarget_boxed_5644_, v_fvarIdsToSimp_5636_, v_a_5637_, v_a_5638_, v_a_5639_, v_a_5640_, v_a_5641_, v_a_5642_);
lean_dec(v_a_5642_);
lean_dec_ref(v_a_5641_);
lean_dec(v_a_5640_);
lean_dec_ref(v_a_5639_);
lean_dec(v_a_5638_);
lean_dec_ref(v_a_5637_);
return v_res_5645_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0(lean_object* v_mvarId_5646_, lean_object* v_val_5647_, lean_object* v___y_5648_, lean_object* v___y_5649_, lean_object* v___y_5650_, lean_object* v___y_5651_, lean_object* v___y_5652_, lean_object* v___y_5653_){
_start:
{
lean_object* v___x_5655_; 
v___x_5655_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___redArg(v_mvarId_5646_, v_val_5647_, v___y_5651_);
return v___x_5655_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___boxed(lean_object* v_mvarId_5656_, lean_object* v_val_5657_, lean_object* v___y_5658_, lean_object* v___y_5659_, lean_object* v___y_5660_, lean_object* v___y_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_, lean_object* v___y_5664_){
_start:
{
lean_object* v_res_5665_; 
v_res_5665_ = l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0(v_mvarId_5656_, v_val_5657_, v___y_5658_, v___y_5659_, v___y_5660_, v___y_5661_, v___y_5662_, v___y_5663_);
lean_dec(v___y_5663_);
lean_dec_ref(v___y_5662_);
lean_dec(v___y_5661_);
lean_dec_ref(v___y_5660_);
lean_dec(v___y_5659_);
lean_dec_ref(v___y_5658_);
return v_res_5665_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4(lean_object* v_00_u03b1_5666_, lean_object* v_x_5667_, lean_object* v___y_5668_, lean_object* v___y_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_){
_start:
{
lean_object* v___x_5675_; 
v___x_5675_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___redArg(v_x_5667_);
return v___x_5675_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4___boxed(lean_object* v_00_u03b1_5676_, lean_object* v_x_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_){
_start:
{
lean_object* v_res_5685_; 
v_res_5685_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__4(v_00_u03b1_5676_, v_x_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_, v___y_5683_);
lean_dec(v___y_5683_);
lean_dec_ref(v___y_5682_);
lean_dec(v___y_5681_);
lean_dec_ref(v___y_5680_);
lean_dec(v___y_5679_);
lean_dec_ref(v___y_5678_);
return v_res_5685_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0(lean_object* v_00_u03b2_5686_, lean_object* v_x_5687_, lean_object* v_x_5688_, lean_object* v_x_5689_){
_start:
{
lean_object* v___x_5690_; 
v___x_5690_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0___redArg(v_x_5687_, v_x_5688_, v_x_5689_);
return v___x_5690_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3(lean_object* v_oldTraces_5691_, lean_object* v_data_5692_, lean_object* v_ref_5693_, lean_object* v_msg_5694_, lean_object* v___y_5695_, lean_object* v___y_5696_, lean_object* v___y_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_){
_start:
{
lean_object* v___x_5702_; 
v___x_5702_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___redArg(v_oldTraces_5691_, v_data_5692_, v_ref_5693_, v_msg_5694_, v___y_5697_, v___y_5698_, v___y_5699_, v___y_5700_);
return v___x_5702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3___boxed(lean_object* v_oldTraces_5703_, lean_object* v_data_5704_, lean_object* v_ref_5705_, lean_object* v_msg_5706_, lean_object* v___y_5707_, lean_object* v___y_5708_, lean_object* v___y_5709_, lean_object* v___y_5710_, lean_object* v___y_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_){
_start:
{
lean_object* v_res_5714_; 
v_res_5714_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__2_spec__3(v_oldTraces_5703_, v_data_5704_, v_ref_5705_, v_msg_5706_, v___y_5707_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_, v___y_5712_);
lean_dec(v___y_5712_);
lean_dec_ref(v___y_5711_);
lean_dec(v___y_5710_);
lean_dec_ref(v___y_5709_);
lean_dec(v___y_5708_);
lean_dec_ref(v___y_5707_);
return v_res_5714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_5715_, lean_object* v_x_5716_, size_t v_x_5717_, size_t v_x_5718_, lean_object* v_x_5719_, lean_object* v_x_5720_){
_start:
{
lean_object* v___x_5721_; 
v___x_5721_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___redArg(v_x_5716_, v_x_5717_, v_x_5718_, v_x_5719_, v_x_5720_);
return v___x_5721_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_5722_, lean_object* v_x_5723_, lean_object* v_x_5724_, lean_object* v_x_5725_, lean_object* v_x_5726_, lean_object* v_x_5727_){
_start:
{
size_t v_x_49883__boxed_5728_; size_t v_x_49884__boxed_5729_; lean_object* v_res_5730_; 
v_x_49883__boxed_5728_ = lean_unbox_usize(v_x_5724_);
lean_dec(v_x_5724_);
v_x_49884__boxed_5729_ = lean_unbox_usize(v_x_5725_);
lean_dec(v_x_5725_);
v_res_5730_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3(v_00_u03b2_5722_, v_x_5723_, v_x_49883__boxed_5728_, v_x_49884__boxed_5729_, v_x_5726_, v_x_5727_);
return v_res_5730_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7(lean_object* v_00_u03b2_5731_, lean_object* v_n_5732_, lean_object* v_k_5733_, lean_object* v_v_5734_){
_start:
{
lean_object* v___x_5735_; 
v___x_5735_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7___redArg(v_n_5732_, v_k_5733_, v_v_5734_);
return v___x_5735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8(lean_object* v_00_u03b2_5736_, size_t v_depth_5737_, lean_object* v_keys_5738_, lean_object* v_vals_5739_, lean_object* v_heq_5740_, lean_object* v_i_5741_, lean_object* v_entries_5742_){
_start:
{
lean_object* v___x_5743_; 
v___x_5743_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___redArg(v_depth_5737_, v_keys_5738_, v_vals_5739_, v_i_5741_, v_entries_5742_);
return v___x_5743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8___boxed(lean_object* v_00_u03b2_5744_, lean_object* v_depth_5745_, lean_object* v_keys_5746_, lean_object* v_vals_5747_, lean_object* v_heq_5748_, lean_object* v_i_5749_, lean_object* v_entries_5750_){
_start:
{
size_t v_depth_boxed_5751_; lean_object* v_res_5752_; 
v_depth_boxed_5751_ = lean_unbox_usize(v_depth_5745_);
lean_dec(v_depth_5745_);
v_res_5752_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__8(v_00_u03b2_5744_, v_depth_boxed_5751_, v_keys_5746_, v_vals_5747_, v_heq_5748_, v_i_5749_, v_entries_5750_);
lean_dec_ref(v_vals_5747_);
lean_dec_ref(v_keys_5746_);
return v_res_5752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9(lean_object* v_00_u03b2_5753_, lean_object* v_x_5754_, lean_object* v_x_5755_, lean_object* v_x_5756_, lean_object* v_x_5757_){
_start:
{
lean_object* v___x_5758_; 
v___x_5758_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0_spec__0_spec__3_spec__7_spec__9___redArg(v_x_5754_, v_x_5755_, v_x_5756_, v_x_5757_);
return v___x_5758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0(lean_object* v_mvarId_5759_, uint8_t v_simplifyTarget_5760_, lean_object* v_fvarIdsToSimp_5761_, lean_object* v___y_5762_, lean_object* v___y_5763_, lean_object* v___y_5764_, lean_object* v___y_5765_, lean_object* v___y_5766_, lean_object* v___y_5767_){
_start:
{
lean_object* v___x_5769_; 
v___x_5769_ = l_Lean_Meta_Sym_preprocessMVar(v_mvarId_5759_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_);
if (lean_obj_tag(v___x_5769_) == 0)
{
lean_object* v_a_5770_; lean_object* v___x_5771_; 
v_a_5770_ = lean_ctor_get(v___x_5769_, 0);
lean_inc(v_a_5770_);
lean_dec_ref_known(v___x_5769_, 1);
v___x_5771_ = l_Lean_Meta_Tactic_Cbv_cbvGoalCore(v_a_5770_, v_simplifyTarget_5760_, v_fvarIdsToSimp_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_);
return v___x_5771_;
}
else
{
lean_object* v_a_5772_; lean_object* v___x_5774_; uint8_t v_isShared_5775_; uint8_t v_isSharedCheck_5779_; 
lean_dec_ref(v_fvarIdsToSimp_5761_);
v_a_5772_ = lean_ctor_get(v___x_5769_, 0);
v_isSharedCheck_5779_ = !lean_is_exclusive(v___x_5769_);
if (v_isSharedCheck_5779_ == 0)
{
v___x_5774_ = v___x_5769_;
v_isShared_5775_ = v_isSharedCheck_5779_;
goto v_resetjp_5773_;
}
else
{
lean_inc(v_a_5772_);
lean_dec(v___x_5769_);
v___x_5774_ = lean_box(0);
v_isShared_5775_ = v_isSharedCheck_5779_;
goto v_resetjp_5773_;
}
v_resetjp_5773_:
{
lean_object* v___x_5777_; 
if (v_isShared_5775_ == 0)
{
v___x_5777_ = v___x_5774_;
goto v_reusejp_5776_;
}
else
{
lean_object* v_reuseFailAlloc_5778_; 
v_reuseFailAlloc_5778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5778_, 0, v_a_5772_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___boxed(lean_object* v_mvarId_5780_, lean_object* v_simplifyTarget_5781_, lean_object* v_fvarIdsToSimp_5782_, lean_object* v___y_5783_, lean_object* v___y_5784_, lean_object* v___y_5785_, lean_object* v___y_5786_, lean_object* v___y_5787_, lean_object* v___y_5788_, lean_object* v___y_5789_){
_start:
{
uint8_t v_simplifyTarget_boxed_5790_; lean_object* v_res_5791_; 
v_simplifyTarget_boxed_5790_ = lean_unbox(v_simplifyTarget_5781_);
v_res_5791_ = l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0(v_mvarId_5780_, v_simplifyTarget_boxed_5790_, v_fvarIdsToSimp_5782_, v___y_5783_, v___y_5784_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_);
lean_dec(v___y_5788_);
lean_dec_ref(v___y_5787_);
lean_dec(v___y_5786_);
lean_dec_ref(v___y_5785_);
lean_dec(v___y_5784_);
lean_dec_ref(v___y_5783_);
return v_res_5791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal(lean_object* v_mvarId_5792_, uint8_t v_simplifyTarget_5793_, lean_object* v_fvarIdsToSimp_5794_, lean_object* v_a_5795_, lean_object* v_a_5796_, lean_object* v_a_5797_, lean_object* v_a_5798_){
_start:
{
lean_object* v___x_5800_; lean_object* v___f_5801_; lean_object* v___x_5802_; 
v___x_5800_ = lean_box(v_simplifyTarget_5793_);
v___f_5801_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvGoal___lam__0___boxed), 10, 3);
lean_closure_set(v___f_5801_, 0, v_mvarId_5792_);
lean_closure_set(v___f_5801_, 1, v___x_5800_);
lean_closure_set(v___f_5801_, 2, v_fvarIdsToSimp_5794_);
v___x_5802_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_5801_, v_a_5795_, v_a_5796_, v_a_5797_, v_a_5798_);
return v___x_5802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvGoal___boxed(lean_object* v_mvarId_5803_, lean_object* v_simplifyTarget_5804_, lean_object* v_fvarIdsToSimp_5805_, lean_object* v_a_5806_, lean_object* v_a_5807_, lean_object* v_a_5808_, lean_object* v_a_5809_, lean_object* v_a_5810_){
_start:
{
uint8_t v_simplifyTarget_boxed_5811_; lean_object* v_res_5812_; 
v_simplifyTarget_boxed_5811_ = lean_unbox(v_simplifyTarget_5804_);
v_res_5812_ = l_Lean_Meta_Tactic_Cbv_cbvGoal(v_mvarId_5803_, v_simplifyTarget_boxed_5811_, v_fvarIdsToSimp_5805_, v_a_5806_, v_a_5807_, v_a_5808_, v_a_5809_);
lean_dec(v_a_5809_);
lean_dec_ref(v_a_5808_);
lean_dec(v_a_5807_);
lean_dec_ref(v_a_5806_);
return v_res_5812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0(lean_object* v_a_5813_, uint8_t v___x_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_){
_start:
{
lean_object* v___x_5822_; 
v___x_5822_ = l_Lean_MVarId_refl(v_a_5813_, v___x_5814_, v___y_5817_, v___y_5818_, v___y_5819_, v___y_5820_);
return v___x_5822_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed(lean_object* v_a_5823_, lean_object* v___x_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_, lean_object* v___y_5827_, lean_object* v___y_5828_, lean_object* v___y_5829_, lean_object* v___y_5830_, lean_object* v___y_5831_){
_start:
{
uint8_t v___x_25154__boxed_5832_; lean_object* v_res_5833_; 
v___x_25154__boxed_5832_ = lean_unbox(v___x_5824_);
v_res_5833_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0(v_a_5823_, v___x_25154__boxed_5832_, v___y_5825_, v___y_5826_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_);
lean_dec(v___y_5830_);
lean_dec_ref(v___y_5829_);
lean_dec(v___y_5828_);
lean_dec_ref(v___y_5827_);
lean_dec(v___y_5826_);
lean_dec_ref(v___y_5825_);
return v_res_5833_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(lean_object* v_cls_5834_, lean_object* v_msg_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_){
_start:
{
lean_object* v_ref_5841_; lean_object* v___x_5842_; lean_object* v_a_5843_; lean_object* v___x_5845_; uint8_t v_isShared_5846_; uint8_t v_isSharedCheck_5887_; 
v_ref_5841_ = lean_ctor_get(v___y_5838_, 5);
v___x_5842_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_5835_, v___y_5836_, v___y_5837_, v___y_5838_, v___y_5839_);
v_a_5843_ = lean_ctor_get(v___x_5842_, 0);
v_isSharedCheck_5887_ = !lean_is_exclusive(v___x_5842_);
if (v_isSharedCheck_5887_ == 0)
{
v___x_5845_ = v___x_5842_;
v_isShared_5846_ = v_isSharedCheck_5887_;
goto v_resetjp_5844_;
}
else
{
lean_inc(v_a_5843_);
lean_dec(v___x_5842_);
v___x_5845_ = lean_box(0);
v_isShared_5846_ = v_isSharedCheck_5887_;
goto v_resetjp_5844_;
}
v_resetjp_5844_:
{
lean_object* v___x_5847_; lean_object* v_traceState_5848_; lean_object* v_env_5849_; lean_object* v_nextMacroScope_5850_; lean_object* v_ngen_5851_; lean_object* v_auxDeclNGen_5852_; lean_object* v_cache_5853_; lean_object* v_messages_5854_; lean_object* v_infoState_5855_; lean_object* v_snapshotTasks_5856_; lean_object* v___x_5858_; uint8_t v_isShared_5859_; uint8_t v_isSharedCheck_5886_; 
v___x_5847_ = lean_st_ref_take(v___y_5839_);
v_traceState_5848_ = lean_ctor_get(v___x_5847_, 4);
v_env_5849_ = lean_ctor_get(v___x_5847_, 0);
v_nextMacroScope_5850_ = lean_ctor_get(v___x_5847_, 1);
v_ngen_5851_ = lean_ctor_get(v___x_5847_, 2);
v_auxDeclNGen_5852_ = lean_ctor_get(v___x_5847_, 3);
v_cache_5853_ = lean_ctor_get(v___x_5847_, 5);
v_messages_5854_ = lean_ctor_get(v___x_5847_, 6);
v_infoState_5855_ = lean_ctor_get(v___x_5847_, 7);
v_snapshotTasks_5856_ = lean_ctor_get(v___x_5847_, 8);
v_isSharedCheck_5886_ = !lean_is_exclusive(v___x_5847_);
if (v_isSharedCheck_5886_ == 0)
{
v___x_5858_ = v___x_5847_;
v_isShared_5859_ = v_isSharedCheck_5886_;
goto v_resetjp_5857_;
}
else
{
lean_inc(v_snapshotTasks_5856_);
lean_inc(v_infoState_5855_);
lean_inc(v_messages_5854_);
lean_inc(v_cache_5853_);
lean_inc(v_traceState_5848_);
lean_inc(v_auxDeclNGen_5852_);
lean_inc(v_ngen_5851_);
lean_inc(v_nextMacroScope_5850_);
lean_inc(v_env_5849_);
lean_dec(v___x_5847_);
v___x_5858_ = lean_box(0);
v_isShared_5859_ = v_isSharedCheck_5886_;
goto v_resetjp_5857_;
}
v_resetjp_5857_:
{
uint64_t v_tid_5860_; lean_object* v_traces_5861_; lean_object* v___x_5863_; uint8_t v_isShared_5864_; uint8_t v_isSharedCheck_5885_; 
v_tid_5860_ = lean_ctor_get_uint64(v_traceState_5848_, sizeof(void*)*1);
v_traces_5861_ = lean_ctor_get(v_traceState_5848_, 0);
v_isSharedCheck_5885_ = !lean_is_exclusive(v_traceState_5848_);
if (v_isSharedCheck_5885_ == 0)
{
v___x_5863_ = v_traceState_5848_;
v_isShared_5864_ = v_isSharedCheck_5885_;
goto v_resetjp_5862_;
}
else
{
lean_inc(v_traces_5861_);
lean_dec(v_traceState_5848_);
v___x_5863_ = lean_box(0);
v_isShared_5864_ = v_isSharedCheck_5885_;
goto v_resetjp_5862_;
}
v_resetjp_5862_:
{
lean_object* v___x_5865_; double v___x_5866_; uint8_t v___x_5867_; lean_object* v___x_5868_; lean_object* v___x_5869_; lean_object* v___x_5870_; lean_object* v___x_5871_; lean_object* v___x_5872_; lean_object* v___x_5873_; lean_object* v___x_5875_; 
v___x_5865_ = lean_box(0);
v___x_5866_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
v___x_5867_ = 0;
v___x_5868_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_5869_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_5869_, 0, v_cls_5834_);
lean_ctor_set(v___x_5869_, 1, v___x_5865_);
lean_ctor_set(v___x_5869_, 2, v___x_5868_);
lean_ctor_set_float(v___x_5869_, sizeof(void*)*3, v___x_5866_);
lean_ctor_set_float(v___x_5869_, sizeof(void*)*3 + 8, v___x_5866_);
lean_ctor_set_uint8(v___x_5869_, sizeof(void*)*3 + 16, v___x_5867_);
v___x_5870_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__2));
v___x_5871_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_5871_, 0, v___x_5869_);
lean_ctor_set(v___x_5871_, 1, v_a_5843_);
lean_ctor_set(v___x_5871_, 2, v___x_5870_);
lean_inc(v_ref_5841_);
v___x_5872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5872_, 0, v_ref_5841_);
lean_ctor_set(v___x_5872_, 1, v___x_5871_);
v___x_5873_ = l_Lean_PersistentArray_push___redArg(v_traces_5861_, v___x_5872_);
if (v_isShared_5864_ == 0)
{
lean_ctor_set(v___x_5863_, 0, v___x_5873_);
v___x_5875_ = v___x_5863_;
goto v_reusejp_5874_;
}
else
{
lean_object* v_reuseFailAlloc_5884_; 
v_reuseFailAlloc_5884_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5884_, 0, v___x_5873_);
lean_ctor_set_uint64(v_reuseFailAlloc_5884_, sizeof(void*)*1, v_tid_5860_);
v___x_5875_ = v_reuseFailAlloc_5884_;
goto v_reusejp_5874_;
}
v_reusejp_5874_:
{
lean_object* v___x_5877_; 
if (v_isShared_5859_ == 0)
{
lean_ctor_set(v___x_5858_, 4, v___x_5875_);
v___x_5877_ = v___x_5858_;
goto v_reusejp_5876_;
}
else
{
lean_object* v_reuseFailAlloc_5883_; 
v_reuseFailAlloc_5883_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5883_, 0, v_env_5849_);
lean_ctor_set(v_reuseFailAlloc_5883_, 1, v_nextMacroScope_5850_);
lean_ctor_set(v_reuseFailAlloc_5883_, 2, v_ngen_5851_);
lean_ctor_set(v_reuseFailAlloc_5883_, 3, v_auxDeclNGen_5852_);
lean_ctor_set(v_reuseFailAlloc_5883_, 4, v___x_5875_);
lean_ctor_set(v_reuseFailAlloc_5883_, 5, v_cache_5853_);
lean_ctor_set(v_reuseFailAlloc_5883_, 6, v_messages_5854_);
lean_ctor_set(v_reuseFailAlloc_5883_, 7, v_infoState_5855_);
lean_ctor_set(v_reuseFailAlloc_5883_, 8, v_snapshotTasks_5856_);
v___x_5877_ = v_reuseFailAlloc_5883_;
goto v_reusejp_5876_;
}
v_reusejp_5876_:
{
lean_object* v___x_5878_; lean_object* v___x_5879_; lean_object* v___x_5881_; 
v___x_5878_ = lean_st_ref_set(v___y_5839_, v___x_5877_);
v___x_5879_ = lean_box(0);
if (v_isShared_5846_ == 0)
{
lean_ctor_set(v___x_5845_, 0, v___x_5879_);
v___x_5881_ = v___x_5845_;
goto v_reusejp_5880_;
}
else
{
lean_object* v_reuseFailAlloc_5882_; 
v_reuseFailAlloc_5882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5882_, 0, v___x_5879_);
v___x_5881_ = v_reuseFailAlloc_5882_;
goto v_reusejp_5880_;
}
v_reusejp_5880_:
{
return v___x_5881_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg___boxed(lean_object* v_cls_5888_, lean_object* v_msg_5889_, lean_object* v___y_5890_, lean_object* v___y_5891_, lean_object* v___y_5892_, lean_object* v___y_5893_, lean_object* v___y_5894_){
_start:
{
lean_object* v_res_5895_; 
v_res_5895_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_5888_, v_msg_5889_, v___y_5890_, v___y_5891_, v___y_5892_, v___y_5893_);
lean_dec(v___y_5893_);
lean_dec_ref(v___y_5892_);
lean_dec(v___y_5891_);
lean_dec_ref(v___y_5890_);
return v_res_5895_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(lean_object* v_msg_5896_, lean_object* v___y_5897_, lean_object* v___y_5898_, lean_object* v___y_5899_, lean_object* v___y_5900_){
_start:
{
lean_object* v_ref_5902_; lean_object* v___x_5903_; lean_object* v_a_5904_; lean_object* v___x_5906_; uint8_t v_isShared_5907_; uint8_t v_isSharedCheck_5912_; 
v_ref_5902_ = lean_ctor_get(v___y_5899_, 5);
v___x_5903_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0_spec__0(v_msg_5896_, v___y_5897_, v___y_5898_, v___y_5899_, v___y_5900_);
v_a_5904_ = lean_ctor_get(v___x_5903_, 0);
v_isSharedCheck_5912_ = !lean_is_exclusive(v___x_5903_);
if (v_isSharedCheck_5912_ == 0)
{
v___x_5906_ = v___x_5903_;
v_isShared_5907_ = v_isSharedCheck_5912_;
goto v_resetjp_5905_;
}
else
{
lean_inc(v_a_5904_);
lean_dec(v___x_5903_);
v___x_5906_ = lean_box(0);
v_isShared_5907_ = v_isSharedCheck_5912_;
goto v_resetjp_5905_;
}
v_resetjp_5905_:
{
lean_object* v___x_5908_; lean_object* v___x_5910_; 
lean_inc(v_ref_5902_);
v___x_5908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5908_, 0, v_ref_5902_);
lean_ctor_set(v___x_5908_, 1, v_a_5904_);
if (v_isShared_5907_ == 0)
{
lean_ctor_set_tag(v___x_5906_, 1);
lean_ctor_set(v___x_5906_, 0, v___x_5908_);
v___x_5910_ = v___x_5906_;
goto v_reusejp_5909_;
}
else
{
lean_object* v_reuseFailAlloc_5911_; 
v_reuseFailAlloc_5911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5911_, 0, v___x_5908_);
v___x_5910_ = v_reuseFailAlloc_5911_;
goto v_reusejp_5909_;
}
v_reusejp_5909_:
{
return v___x_5910_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg___boxed(lean_object* v_msg_5913_, lean_object* v___y_5914_, lean_object* v___y_5915_, lean_object* v___y_5916_, lean_object* v___y_5917_, lean_object* v___y_5918_){
_start:
{
lean_object* v_res_5919_; 
v_res_5919_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v_msg_5913_, v___y_5914_, v___y_5915_, v___y_5916_, v___y_5917_);
lean_dec(v___y_5917_);
lean_dec_ref(v___y_5916_);
lean_dec(v___y_5915_);
lean_dec_ref(v___y_5914_);
return v_res_5919_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5921_; lean_object* v___x_5922_; 
v___x_5921_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__0));
v___x_5922_ = l_Lean_stringToMessageData(v___x_5921_);
return v___x_5922_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3(void){
_start:
{
lean_object* v___x_5924_; lean_object* v___x_5925_; 
v___x_5924_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__2));
v___x_5925_ = l_Lean_stringToMessageData(v___x_5924_);
return v___x_5925_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6(void){
_start:
{
lean_object* v___x_5929_; lean_object* v___x_5930_; 
v___x_5929_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__5));
v___x_5930_ = l_Lean_stringToMessageData(v___x_5929_);
return v___x_5930_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8(void){
_start:
{
lean_object* v___x_5932_; lean_object* v___x_5933_; 
v___x_5932_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__7));
v___x_5933_ = l_Lean_stringToMessageData(v___x_5932_);
return v___x_5933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1(lean_object* v_m_5934_, lean_object* v___x_5935_, lean_object* v_cls_5936_, lean_object* v___y_5937_, lean_object* v___y_5938_, lean_object* v___y_5939_, lean_object* v___y_5940_, lean_object* v___y_5941_, lean_object* v___y_5942_){
_start:
{
lean_object* v_e_5945_; lean_object* v_onTrue_5946_; lean_object* v___y_5947_; lean_object* v___y_5948_; lean_object* v___y_5949_; lean_object* v___y_5950_; lean_object* v___y_5951_; lean_object* v___y_5952_; lean_object* v___x_5982_; 
v___x_5982_ = l_Lean_Meta_Sym_preprocessMVar(v_m_5934_, v___y_5937_, v___y_5938_, v___y_5939_, v___y_5940_, v___y_5941_, v___y_5942_);
if (lean_obj_tag(v___x_5982_) == 0)
{
lean_object* v_a_5983_; lean_object* v___x_5984_; 
v_a_5983_ = lean_ctor_get(v___x_5982_, 0);
lean_inc_n(v_a_5983_, 2);
lean_dec_ref_known(v___x_5982_, 1);
v___x_5984_ = l_Lean_MVarId_getType(v_a_5983_, v___y_5939_, v___y_5940_, v___y_5941_, v___y_5942_);
if (lean_obj_tag(v___x_5984_) == 0)
{
lean_object* v_a_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; uint8_t v___x_5988_; 
v_a_5985_ = lean_ctor_get(v___x_5984_, 0);
lean_inc(v_a_5985_);
lean_dec_ref_known(v___x_5984_, 1);
v___x_5986_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4));
v___x_5987_ = lean_unsigned_to_nat(3u);
v___x_5988_ = l_Lean_Expr_isAppOfArity(v_a_5985_, v___x_5986_, v___x_5987_);
if (v___x_5988_ == 0)
{
lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; 
lean_dec(v_a_5983_);
lean_dec(v_cls_5936_);
lean_dec_ref(v___x_5935_);
v___x_5989_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6);
v___x_5990_ = l_Lean_indentExpr(v_a_5985_);
v___x_5991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5991_, 0, v___x_5989_);
lean_ctor_set(v___x_5991_, 1, v___x_5990_);
v___x_5992_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5991_, v___y_5939_, v___y_5940_, v___y_5941_, v___y_5942_);
return v___x_5992_;
}
else
{
lean_object* v___x_5993_; lean_object* v___x_5994_; lean_object* v___x_5995_; 
v___x_5993_ = l_Lean_Expr_appFn_x21(v_a_5985_);
lean_dec(v_a_5985_);
v___x_5994_ = l_Lean_Expr_appArg_x21(v___x_5993_);
lean_dec_ref(v___x_5993_);
lean_inc_ref(v___x_5994_);
v___x_5995_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_5994_, v___x_5935_, v___y_5937_, v___y_5938_, v___y_5939_, v___y_5940_, v___y_5941_, v___y_5942_);
if (lean_obj_tag(v___x_5995_) == 0)
{
lean_object* v_options_5996_; lean_object* v_a_5997_; lean_object* v_inheritedTraceOptions_5998_; uint8_t v_hasTrace_5999_; lean_object* v___x_6000_; lean_object* v___f_6001_; lean_object* v___y_6003_; lean_object* v___y_6004_; lean_object* v___y_6005_; lean_object* v___y_6006_; lean_object* v___y_6007_; lean_object* v___y_6008_; 
v_options_5996_ = lean_ctor_get(v___y_5941_, 2);
v_a_5997_ = lean_ctor_get(v___x_5995_, 0);
lean_inc(v_a_5997_);
lean_dec_ref_known(v___x_5995_, 1);
v_inheritedTraceOptions_5998_ = lean_ctor_get(v___y_5941_, 13);
v_hasTrace_5999_ = lean_ctor_get_uint8(v_options_5996_, sizeof(void*)*1);
v___x_6000_ = lean_box(v___x_5988_);
lean_inc(v_a_5983_);
v___f_6001_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed), 9, 2);
lean_closure_set(v___f_6001_, 0, v_a_5983_);
lean_closure_set(v___f_6001_, 1, v___x_6000_);
if (v_hasTrace_5999_ == 0)
{
lean_dec(v_cls_5936_);
v___y_6003_ = v___y_5937_;
v___y_6004_ = v___y_5938_;
v___y_6005_ = v___y_5939_;
v___y_6006_ = v___y_5940_;
v___y_6007_ = v___y_5941_;
v___y_6008_ = v___y_5942_;
goto v___jp_6002_;
}
else
{
lean_object* v___x_6012_; lean_object* v___x_6013_; uint8_t v___x_6014_; 
v___x_6012_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
lean_inc(v_cls_5936_);
v___x_6013_ = l_Lean_Name_append(v___x_6012_, v_cls_5936_);
v___x_6014_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5998_, v_options_5996_, v___x_6013_);
lean_dec(v___x_6013_);
if (v___x_6014_ == 0)
{
lean_dec(v_cls_5936_);
v___y_6003_ = v___y_5937_;
v___y_6004_ = v___y_5938_;
v___y_6005_ = v___y_5939_;
v___y_6006_ = v___y_5940_;
v___y_6007_ = v___y_5941_;
v___y_6008_ = v___y_5942_;
goto v___jp_6002_;
}
else
{
lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; 
v___x_6015_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8);
lean_inc_ref(v___x_5994_);
v___x_6016_ = l_Lean_indentExpr(v___x_5994_);
v___x_6017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6017_, 0, v___x_6015_);
lean_ctor_set(v___x_6017_, 1, v___x_6016_);
v___x_6018_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_6019_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6019_, 0, v___x_6017_);
lean_ctor_set(v___x_6019_, 1, v___x_6018_);
v___x_6020_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_5994_, v_a_5997_);
v___x_6021_ = l_Lean_indentExpr(v___x_6020_);
v___x_6022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6022_, 0, v___x_6019_);
lean_ctor_set(v___x_6022_, 1, v___x_6021_);
v___x_6023_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_5936_, v___x_6022_, v___y_5939_, v___y_5940_, v___y_5941_, v___y_5942_);
if (lean_obj_tag(v___x_6023_) == 0)
{
lean_dec_ref_known(v___x_6023_, 1);
v___y_6003_ = v___y_5937_;
v___y_6004_ = v___y_5938_;
v___y_6005_ = v___y_5939_;
v___y_6006_ = v___y_5940_;
v___y_6007_ = v___y_5941_;
v___y_6008_ = v___y_5942_;
goto v___jp_6002_;
}
else
{
lean_dec_ref(v___f_6001_);
lean_dec(v_a_5997_);
lean_dec_ref(v___x_5994_);
lean_dec(v_a_5983_);
return v___x_6023_;
}
}
}
v___jp_6002_:
{
if (lean_obj_tag(v_a_5997_) == 0)
{
lean_dec_ref_known(v_a_5997_, 0);
lean_dec(v_a_5983_);
v_e_5945_ = v___x_5994_;
v_onTrue_5946_ = v___f_6001_;
v___y_5947_ = v___y_6003_;
v___y_5948_ = v___y_6004_;
v___y_5949_ = v___y_6005_;
v___y_5950_ = v___y_6006_;
v___y_5951_ = v___y_6007_;
v___y_5952_ = v___y_6008_;
goto v___jp_5944_;
}
else
{
lean_object* v_e_x27_6009_; lean_object* v_proof_6010_; lean_object* v___x_6011_; 
lean_dec_ref(v___f_6001_);
lean_dec_ref(v___x_5994_);
v_e_x27_6009_ = lean_ctor_get(v_a_5997_, 0);
lean_inc_ref(v_e_x27_6009_);
v_proof_6010_ = lean_ctor_get(v_a_5997_, 1);
lean_inc_ref(v_proof_6010_);
lean_dec_ref_known(v_a_5997_, 2);
v___x_6011_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_6011_, 0, v_a_5983_);
lean_closure_set(v___x_6011_, 1, v_proof_6010_);
v_e_5945_ = v_e_x27_6009_;
v_onTrue_5946_ = v___x_6011_;
v___y_5947_ = v___y_6003_;
v___y_5948_ = v___y_6004_;
v___y_5949_ = v___y_6005_;
v___y_5950_ = v___y_6006_;
v___y_5951_ = v___y_6007_;
v___y_5952_ = v___y_6008_;
goto v___jp_5944_;
}
}
}
else
{
lean_object* v_a_6024_; lean_object* v___x_6026_; uint8_t v_isShared_6027_; uint8_t v_isSharedCheck_6031_; 
lean_dec_ref(v___x_5994_);
lean_dec(v_a_5983_);
lean_dec(v_cls_5936_);
v_a_6024_ = lean_ctor_get(v___x_5995_, 0);
v_isSharedCheck_6031_ = !lean_is_exclusive(v___x_5995_);
if (v_isSharedCheck_6031_ == 0)
{
v___x_6026_ = v___x_5995_;
v_isShared_6027_ = v_isSharedCheck_6031_;
goto v_resetjp_6025_;
}
else
{
lean_inc(v_a_6024_);
lean_dec(v___x_5995_);
v___x_6026_ = lean_box(0);
v_isShared_6027_ = v_isSharedCheck_6031_;
goto v_resetjp_6025_;
}
v_resetjp_6025_:
{
lean_object* v___x_6029_; 
if (v_isShared_6027_ == 0)
{
v___x_6029_ = v___x_6026_;
goto v_reusejp_6028_;
}
else
{
lean_object* v_reuseFailAlloc_6030_; 
v_reuseFailAlloc_6030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6030_, 0, v_a_6024_);
v___x_6029_ = v_reuseFailAlloc_6030_;
goto v_reusejp_6028_;
}
v_reusejp_6028_:
{
return v___x_6029_;
}
}
}
}
}
else
{
lean_object* v_a_6032_; lean_object* v___x_6034_; uint8_t v_isShared_6035_; uint8_t v_isSharedCheck_6039_; 
lean_dec(v_a_5983_);
lean_dec(v_cls_5936_);
lean_dec_ref(v___x_5935_);
v_a_6032_ = lean_ctor_get(v___x_5984_, 0);
v_isSharedCheck_6039_ = !lean_is_exclusive(v___x_5984_);
if (v_isSharedCheck_6039_ == 0)
{
v___x_6034_ = v___x_5984_;
v_isShared_6035_ = v_isSharedCheck_6039_;
goto v_resetjp_6033_;
}
else
{
lean_inc(v_a_6032_);
lean_dec(v___x_5984_);
v___x_6034_ = lean_box(0);
v_isShared_6035_ = v_isSharedCheck_6039_;
goto v_resetjp_6033_;
}
v_resetjp_6033_:
{
lean_object* v___x_6037_; 
if (v_isShared_6035_ == 0)
{
v___x_6037_ = v___x_6034_;
goto v_reusejp_6036_;
}
else
{
lean_object* v_reuseFailAlloc_6038_; 
v_reuseFailAlloc_6038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6038_, 0, v_a_6032_);
v___x_6037_ = v_reuseFailAlloc_6038_;
goto v_reusejp_6036_;
}
v_reusejp_6036_:
{
return v___x_6037_;
}
}
}
}
else
{
lean_object* v_a_6040_; lean_object* v___x_6042_; uint8_t v_isShared_6043_; uint8_t v_isSharedCheck_6047_; 
lean_dec(v_cls_5936_);
lean_dec_ref(v___x_5935_);
v_a_6040_ = lean_ctor_get(v___x_5982_, 0);
v_isSharedCheck_6047_ = !lean_is_exclusive(v___x_5982_);
if (v_isSharedCheck_6047_ == 0)
{
v___x_6042_ = v___x_5982_;
v_isShared_6043_ = v_isSharedCheck_6047_;
goto v_resetjp_6041_;
}
else
{
lean_inc(v_a_6040_);
lean_dec(v___x_5982_);
v___x_6042_ = lean_box(0);
v_isShared_6043_ = v_isSharedCheck_6047_;
goto v_resetjp_6041_;
}
v_resetjp_6041_:
{
lean_object* v___x_6045_; 
if (v_isShared_6043_ == 0)
{
v___x_6045_ = v___x_6042_;
goto v_reusejp_6044_;
}
else
{
lean_object* v_reuseFailAlloc_6046_; 
v_reuseFailAlloc_6046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6046_, 0, v_a_6040_);
v___x_6045_ = v_reuseFailAlloc_6046_;
goto v_reusejp_6044_;
}
v_reusejp_6044_:
{
return v___x_6045_;
}
}
}
v___jp_5944_:
{
lean_object* v___x_5953_; 
v___x_5953_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_5945_, v___y_5947_);
if (lean_obj_tag(v___x_5953_) == 0)
{
lean_object* v_a_5954_; uint8_t v___x_5955_; 
v_a_5954_ = lean_ctor_get(v___x_5953_, 0);
lean_inc(v_a_5954_);
lean_dec_ref_known(v___x_5953_, 1);
v___x_5955_ = lean_unbox(v_a_5954_);
lean_dec(v_a_5954_);
if (v___x_5955_ == 0)
{
lean_object* v___x_5956_; 
lean_dec_ref(v_onTrue_5946_);
v___x_5956_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_5945_, v___y_5947_);
if (lean_obj_tag(v___x_5956_) == 0)
{
lean_object* v_a_5957_; uint8_t v___x_5958_; 
v_a_5957_ = lean_ctor_get(v___x_5956_, 0);
lean_inc(v_a_5957_);
lean_dec_ref_known(v___x_5956_, 1);
v___x_5958_ = lean_unbox(v_a_5957_);
lean_dec(v_a_5957_);
if (v___x_5958_ == 0)
{
lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; 
v___x_5959_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1);
v___x_5960_ = l_Lean_indentExpr(v_e_5945_);
v___x_5961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5961_, 0, v___x_5959_);
lean_ctor_set(v___x_5961_, 1, v___x_5960_);
v___x_5962_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5961_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_);
return v___x_5962_;
}
else
{
lean_object* v___x_5963_; lean_object* v___x_5964_; 
lean_dec_ref(v_e_5945_);
v___x_5963_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3);
v___x_5964_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_5963_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_);
return v___x_5964_;
}
}
else
{
lean_object* v_a_5965_; lean_object* v___x_5967_; uint8_t v_isShared_5968_; uint8_t v_isSharedCheck_5972_; 
lean_dec_ref(v_e_5945_);
v_a_5965_ = lean_ctor_get(v___x_5956_, 0);
v_isSharedCheck_5972_ = !lean_is_exclusive(v___x_5956_);
if (v_isSharedCheck_5972_ == 0)
{
v___x_5967_ = v___x_5956_;
v_isShared_5968_ = v_isSharedCheck_5972_;
goto v_resetjp_5966_;
}
else
{
lean_inc(v_a_5965_);
lean_dec(v___x_5956_);
v___x_5967_ = lean_box(0);
v_isShared_5968_ = v_isSharedCheck_5972_;
goto v_resetjp_5966_;
}
v_resetjp_5966_:
{
lean_object* v___x_5970_; 
if (v_isShared_5968_ == 0)
{
v___x_5970_ = v___x_5967_;
goto v_reusejp_5969_;
}
else
{
lean_object* v_reuseFailAlloc_5971_; 
v_reuseFailAlloc_5971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5971_, 0, v_a_5965_);
v___x_5970_ = v_reuseFailAlloc_5971_;
goto v_reusejp_5969_;
}
v_reusejp_5969_:
{
return v___x_5970_;
}
}
}
}
else
{
lean_object* v___x_5973_; 
lean_dec_ref(v_e_5945_);
lean_inc(v___y_5952_);
lean_inc_ref(v___y_5951_);
lean_inc(v___y_5950_);
lean_inc_ref(v___y_5949_);
lean_inc(v___y_5948_);
lean_inc_ref(v___y_5947_);
v___x_5973_ = lean_apply_7(v_onTrue_5946_, v___y_5947_, v___y_5948_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_, lean_box(0));
return v___x_5973_;
}
}
else
{
lean_object* v_a_5974_; lean_object* v___x_5976_; uint8_t v_isShared_5977_; uint8_t v_isSharedCheck_5981_; 
lean_dec_ref(v_onTrue_5946_);
lean_dec_ref(v_e_5945_);
v_a_5974_ = lean_ctor_get(v___x_5953_, 0);
v_isSharedCheck_5981_ = !lean_is_exclusive(v___x_5953_);
if (v_isSharedCheck_5981_ == 0)
{
v___x_5976_ = v___x_5953_;
v_isShared_5977_ = v_isSharedCheck_5981_;
goto v_resetjp_5975_;
}
else
{
lean_inc(v_a_5974_);
lean_dec(v___x_5953_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___boxed(lean_object* v_m_6048_, lean_object* v___x_6049_, lean_object* v_cls_6050_, lean_object* v___y_6051_, lean_object* v___y_6052_, lean_object* v___y_6053_, lean_object* v___y_6054_, lean_object* v___y_6055_, lean_object* v___y_6056_, lean_object* v___y_6057_){
_start:
{
lean_object* v_res_6058_; 
v_res_6058_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1(v_m_6048_, v___x_6049_, v_cls_6050_, v___y_6051_, v___y_6052_, v___y_6053_, v___y_6054_, v___y_6055_, v___y_6056_);
lean_dec(v___y_6056_);
lean_dec_ref(v___y_6055_);
lean_dec(v___y_6054_);
lean_dec_ref(v___y_6053_);
lean_dec(v___y_6052_);
lean_dec_ref(v___y_6051_);
return v_res_6058_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1(void){
_start:
{
lean_object* v___x_6060_; lean_object* v___x_6061_; 
v___x_6060_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__0));
v___x_6061_ = l_Lean_stringToMessageData(v___x_6060_);
return v___x_6061_;
}
}
static lean_object* _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3(void){
_start:
{
lean_object* v___x_6063_; lean_object* v___x_6064_; 
v___x_6063_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__2));
v___x_6064_ = l_Lean_stringToMessageData(v___x_6063_);
return v___x_6064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2(lean_object* v_x_6065_, lean_object* v___y_6066_, lean_object* v___y_6067_, lean_object* v___y_6068_, lean_object* v___y_6069_){
_start:
{
if (lean_obj_tag(v_x_6065_) == 0)
{
lean_object* v_a_6071_; lean_object* v___x_6073_; uint8_t v_isShared_6074_; uint8_t v_isSharedCheck_6081_; 
v_a_6071_ = lean_ctor_get(v_x_6065_, 0);
v_isSharedCheck_6081_ = !lean_is_exclusive(v_x_6065_);
if (v_isSharedCheck_6081_ == 0)
{
v___x_6073_ = v_x_6065_;
v_isShared_6074_ = v_isSharedCheck_6081_;
goto v_resetjp_6072_;
}
else
{
lean_inc(v_a_6071_);
lean_dec(v_x_6065_);
v___x_6073_ = lean_box(0);
v_isShared_6074_ = v_isSharedCheck_6081_;
goto v_resetjp_6072_;
}
v_resetjp_6072_:
{
lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6079_; 
v___x_6075_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__1);
v___x_6076_ = l_Lean_Exception_toMessageData(v_a_6071_);
v___x_6077_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6077_, 0, v___x_6075_);
lean_ctor_set(v___x_6077_, 1, v___x_6076_);
if (v_isShared_6074_ == 0)
{
lean_ctor_set(v___x_6073_, 0, v___x_6077_);
v___x_6079_ = v___x_6073_;
goto v_reusejp_6078_;
}
else
{
lean_object* v_reuseFailAlloc_6080_; 
v_reuseFailAlloc_6080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6080_, 0, v___x_6077_);
v___x_6079_ = v_reuseFailAlloc_6080_;
goto v_reusejp_6078_;
}
v_reusejp_6078_:
{
return v___x_6079_;
}
}
}
else
{
lean_object* v___x_6083_; uint8_t v_isShared_6084_; uint8_t v_isSharedCheck_6089_; 
v_isSharedCheck_6089_ = !lean_is_exclusive(v_x_6065_);
if (v_isSharedCheck_6089_ == 0)
{
lean_object* v_unused_6090_; 
v_unused_6090_ = lean_ctor_get(v_x_6065_, 0);
lean_dec(v_unused_6090_);
v___x_6083_ = v_x_6065_;
v_isShared_6084_ = v_isSharedCheck_6089_;
goto v_resetjp_6082_;
}
else
{
lean_dec(v_x_6065_);
v___x_6083_ = lean_box(0);
v_isShared_6084_ = v_isSharedCheck_6089_;
goto v_resetjp_6082_;
}
v_resetjp_6082_:
{
lean_object* v___x_6085_; lean_object* v___x_6087_; 
v___x_6085_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___closed__3);
if (v_isShared_6084_ == 0)
{
lean_ctor_set_tag(v___x_6083_, 0);
lean_ctor_set(v___x_6083_, 0, v___x_6085_);
v___x_6087_ = v___x_6083_;
goto v_reusejp_6086_;
}
else
{
lean_object* v_reuseFailAlloc_6088_; 
v_reuseFailAlloc_6088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6088_, 0, v___x_6085_);
v___x_6087_ = v_reuseFailAlloc_6088_;
goto v_reusejp_6086_;
}
v_reusejp_6086_:
{
return v___x_6087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2___boxed(lean_object* v_x_6091_, lean_object* v___y_6092_, lean_object* v___y_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_, lean_object* v___y_6096_){
_start:
{
lean_object* v_res_6097_; 
v_res_6097_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__2(v_x_6091_, v___y_6092_, v___y_6093_, v___y_6094_, v___y_6095_);
lean_dec(v___y_6095_);
lean_dec_ref(v___y_6094_);
lean_dec(v___y_6093_);
lean_dec_ref(v___y_6092_);
return v_res_6097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3(lean_object* v_a_6098_, uint8_t v_hasTrace_6099_, lean_object* v___y_6100_, lean_object* v___y_6101_, lean_object* v___y_6102_, lean_object* v___y_6103_, lean_object* v___y_6104_, lean_object* v___y_6105_){
_start:
{
lean_object* v___x_6107_; 
v___x_6107_ = l_Lean_MVarId_refl(v_a_6098_, v_hasTrace_6099_, v___y_6102_, v___y_6103_, v___y_6104_, v___y_6105_);
return v___x_6107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3___boxed(lean_object* v_a_6108_, lean_object* v_hasTrace_6109_, lean_object* v___y_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_, lean_object* v___y_6115_, lean_object* v___y_6116_){
_start:
{
uint8_t v_hasTrace_boxed_6117_; lean_object* v_res_6118_; 
v_hasTrace_boxed_6117_ = lean_unbox(v_hasTrace_6109_);
v_res_6118_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3(v_a_6108_, v_hasTrace_boxed_6117_, v___y_6110_, v___y_6111_, v___y_6112_, v___y_6113_, v___y_6114_, v___y_6115_);
lean_dec(v___y_6115_);
lean_dec_ref(v___y_6114_);
lean_dec(v___y_6113_);
lean_dec_ref(v___y_6112_);
lean_dec(v___y_6111_);
lean_dec_ref(v___y_6110_);
return v_res_6118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4(lean_object* v_m_6119_, lean_object* v___x_6120_, uint8_t v_hasTrace_6121_, lean_object* v_cls_6122_, lean_object* v___y_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_){
_start:
{
lean_object* v_e_6131_; lean_object* v_onTrue_6132_; lean_object* v___y_6133_; lean_object* v___y_6134_; lean_object* v___y_6135_; lean_object* v___y_6136_; lean_object* v___y_6137_; lean_object* v___y_6138_; lean_object* v___x_6168_; 
v___x_6168_ = l_Lean_Meta_Sym_preprocessMVar(v_m_6119_, v___y_6123_, v___y_6124_, v___y_6125_, v___y_6126_, v___y_6127_, v___y_6128_);
if (lean_obj_tag(v___x_6168_) == 0)
{
lean_object* v_a_6169_; lean_object* v___x_6170_; 
v_a_6169_ = lean_ctor_get(v___x_6168_, 0);
lean_inc_n(v_a_6169_, 2);
lean_dec_ref_known(v___x_6168_, 1);
v___x_6170_ = l_Lean_MVarId_getType(v_a_6169_, v___y_6125_, v___y_6126_, v___y_6127_, v___y_6128_);
if (lean_obj_tag(v___x_6170_) == 0)
{
lean_object* v_a_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; uint8_t v___x_6174_; 
v_a_6171_ = lean_ctor_get(v___x_6170_, 0);
lean_inc(v_a_6171_);
lean_dec_ref_known(v___x_6170_, 1);
v___x_6172_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4));
v___x_6173_ = lean_unsigned_to_nat(3u);
v___x_6174_ = l_Lean_Expr_isAppOfArity(v_a_6171_, v___x_6172_, v___x_6173_);
if (v___x_6174_ == 0)
{
lean_object* v___x_6175_; lean_object* v___x_6176_; lean_object* v___x_6177_; lean_object* v___x_6178_; 
lean_dec(v_a_6169_);
lean_dec(v_cls_6122_);
lean_dec_ref(v___x_6120_);
v___x_6175_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6);
v___x_6176_ = l_Lean_indentExpr(v_a_6171_);
v___x_6177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6177_, 0, v___x_6175_);
lean_ctor_set(v___x_6177_, 1, v___x_6176_);
v___x_6178_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6177_, v___y_6125_, v___y_6126_, v___y_6127_, v___y_6128_);
return v___x_6178_;
}
else
{
lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; 
v___x_6179_ = l_Lean_Expr_appFn_x21(v_a_6171_);
lean_dec(v_a_6171_);
v___x_6180_ = l_Lean_Expr_appArg_x21(v___x_6179_);
lean_dec_ref(v___x_6179_);
lean_inc_ref(v___x_6180_);
v___x_6181_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_6180_, v___x_6120_, v___y_6123_, v___y_6124_, v___y_6125_, v___y_6126_, v___y_6127_, v___y_6128_);
if (lean_obj_tag(v___x_6181_) == 0)
{
lean_object* v_options_6182_; lean_object* v_a_6183_; lean_object* v_inheritedTraceOptions_6184_; uint8_t v_hasTrace_6185_; lean_object* v___x_6186_; lean_object* v___f_6187_; lean_object* v___y_6189_; lean_object* v___y_6190_; lean_object* v___y_6191_; lean_object* v___y_6192_; lean_object* v___y_6193_; lean_object* v___y_6194_; 
v_options_6182_ = lean_ctor_get(v___y_6127_, 2);
v_a_6183_ = lean_ctor_get(v___x_6181_, 0);
lean_inc(v_a_6183_);
lean_dec_ref_known(v___x_6181_, 1);
v_inheritedTraceOptions_6184_ = lean_ctor_get(v___y_6127_, 13);
v_hasTrace_6185_ = lean_ctor_get_uint8(v_options_6182_, sizeof(void*)*1);
v___x_6186_ = lean_box(v_hasTrace_6121_);
lean_inc(v_a_6169_);
v___f_6187_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__3___boxed), 9, 2);
lean_closure_set(v___f_6187_, 0, v_a_6169_);
lean_closure_set(v___f_6187_, 1, v___x_6186_);
if (v_hasTrace_6185_ == 0)
{
lean_dec(v_cls_6122_);
v___y_6189_ = v___y_6123_;
v___y_6190_ = v___y_6124_;
v___y_6191_ = v___y_6125_;
v___y_6192_ = v___y_6126_;
v___y_6193_ = v___y_6127_;
v___y_6194_ = v___y_6128_;
goto v___jp_6188_;
}
else
{
lean_object* v___x_6198_; lean_object* v___x_6199_; uint8_t v___x_6200_; 
v___x_6198_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
lean_inc(v_cls_6122_);
v___x_6199_ = l_Lean_Name_append(v___x_6198_, v_cls_6122_);
v___x_6200_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6184_, v_options_6182_, v___x_6199_);
lean_dec(v___x_6199_);
if (v___x_6200_ == 0)
{
lean_dec(v_cls_6122_);
v___y_6189_ = v___y_6123_;
v___y_6190_ = v___y_6124_;
v___y_6191_ = v___y_6125_;
v___y_6192_ = v___y_6126_;
v___y_6193_ = v___y_6127_;
v___y_6194_ = v___y_6128_;
goto v___jp_6188_;
}
else
{
lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; lean_object* v___x_6204_; lean_object* v___x_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; lean_object* v___x_6208_; lean_object* v___x_6209_; 
v___x_6201_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8);
lean_inc_ref(v___x_6180_);
v___x_6202_ = l_Lean_indentExpr(v___x_6180_);
v___x_6203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6203_, 0, v___x_6201_);
lean_ctor_set(v___x_6203_, 1, v___x_6202_);
v___x_6204_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_6205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6205_, 0, v___x_6203_);
lean_ctor_set(v___x_6205_, 1, v___x_6204_);
v___x_6206_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_6180_, v_a_6183_);
v___x_6207_ = l_Lean_indentExpr(v___x_6206_);
v___x_6208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6208_, 0, v___x_6205_);
lean_ctor_set(v___x_6208_, 1, v___x_6207_);
v___x_6209_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_6122_, v___x_6208_, v___y_6125_, v___y_6126_, v___y_6127_, v___y_6128_);
if (lean_obj_tag(v___x_6209_) == 0)
{
lean_dec_ref_known(v___x_6209_, 1);
v___y_6189_ = v___y_6123_;
v___y_6190_ = v___y_6124_;
v___y_6191_ = v___y_6125_;
v___y_6192_ = v___y_6126_;
v___y_6193_ = v___y_6127_;
v___y_6194_ = v___y_6128_;
goto v___jp_6188_;
}
else
{
lean_dec_ref(v___f_6187_);
lean_dec(v_a_6183_);
lean_dec_ref(v___x_6180_);
lean_dec(v_a_6169_);
return v___x_6209_;
}
}
}
v___jp_6188_:
{
if (lean_obj_tag(v_a_6183_) == 0)
{
lean_dec_ref_known(v_a_6183_, 0);
lean_dec(v_a_6169_);
v_e_6131_ = v___x_6180_;
v_onTrue_6132_ = v___f_6187_;
v___y_6133_ = v___y_6189_;
v___y_6134_ = v___y_6190_;
v___y_6135_ = v___y_6191_;
v___y_6136_ = v___y_6192_;
v___y_6137_ = v___y_6193_;
v___y_6138_ = v___y_6194_;
goto v___jp_6130_;
}
else
{
lean_object* v_e_x27_6195_; lean_object* v_proof_6196_; lean_object* v___x_6197_; 
lean_dec_ref(v___f_6187_);
lean_dec_ref(v___x_6180_);
v_e_x27_6195_ = lean_ctor_get(v_a_6183_, 0);
lean_inc_ref(v_e_x27_6195_);
v_proof_6196_ = lean_ctor_get(v_a_6183_, 1);
lean_inc_ref(v_proof_6196_);
lean_dec_ref_known(v_a_6183_, 2);
v___x_6197_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_6197_, 0, v_a_6169_);
lean_closure_set(v___x_6197_, 1, v_proof_6196_);
v_e_6131_ = v_e_x27_6195_;
v_onTrue_6132_ = v___x_6197_;
v___y_6133_ = v___y_6189_;
v___y_6134_ = v___y_6190_;
v___y_6135_ = v___y_6191_;
v___y_6136_ = v___y_6192_;
v___y_6137_ = v___y_6193_;
v___y_6138_ = v___y_6194_;
goto v___jp_6130_;
}
}
}
else
{
lean_object* v_a_6210_; lean_object* v___x_6212_; uint8_t v_isShared_6213_; uint8_t v_isSharedCheck_6217_; 
lean_dec_ref(v___x_6180_);
lean_dec(v_a_6169_);
lean_dec(v_cls_6122_);
v_a_6210_ = lean_ctor_get(v___x_6181_, 0);
v_isSharedCheck_6217_ = !lean_is_exclusive(v___x_6181_);
if (v_isSharedCheck_6217_ == 0)
{
v___x_6212_ = v___x_6181_;
v_isShared_6213_ = v_isSharedCheck_6217_;
goto v_resetjp_6211_;
}
else
{
lean_inc(v_a_6210_);
lean_dec(v___x_6181_);
v___x_6212_ = lean_box(0);
v_isShared_6213_ = v_isSharedCheck_6217_;
goto v_resetjp_6211_;
}
v_resetjp_6211_:
{
lean_object* v___x_6215_; 
if (v_isShared_6213_ == 0)
{
v___x_6215_ = v___x_6212_;
goto v_reusejp_6214_;
}
else
{
lean_object* v_reuseFailAlloc_6216_; 
v_reuseFailAlloc_6216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6216_, 0, v_a_6210_);
v___x_6215_ = v_reuseFailAlloc_6216_;
goto v_reusejp_6214_;
}
v_reusejp_6214_:
{
return v___x_6215_;
}
}
}
}
}
else
{
lean_object* v_a_6218_; lean_object* v___x_6220_; uint8_t v_isShared_6221_; uint8_t v_isSharedCheck_6225_; 
lean_dec(v_a_6169_);
lean_dec(v_cls_6122_);
lean_dec_ref(v___x_6120_);
v_a_6218_ = lean_ctor_get(v___x_6170_, 0);
v_isSharedCheck_6225_ = !lean_is_exclusive(v___x_6170_);
if (v_isSharedCheck_6225_ == 0)
{
v___x_6220_ = v___x_6170_;
v_isShared_6221_ = v_isSharedCheck_6225_;
goto v_resetjp_6219_;
}
else
{
lean_inc(v_a_6218_);
lean_dec(v___x_6170_);
v___x_6220_ = lean_box(0);
v_isShared_6221_ = v_isSharedCheck_6225_;
goto v_resetjp_6219_;
}
v_resetjp_6219_:
{
lean_object* v___x_6223_; 
if (v_isShared_6221_ == 0)
{
v___x_6223_ = v___x_6220_;
goto v_reusejp_6222_;
}
else
{
lean_object* v_reuseFailAlloc_6224_; 
v_reuseFailAlloc_6224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6224_, 0, v_a_6218_);
v___x_6223_ = v_reuseFailAlloc_6224_;
goto v_reusejp_6222_;
}
v_reusejp_6222_:
{
return v___x_6223_;
}
}
}
}
else
{
lean_object* v_a_6226_; lean_object* v___x_6228_; uint8_t v_isShared_6229_; uint8_t v_isSharedCheck_6233_; 
lean_dec(v_cls_6122_);
lean_dec_ref(v___x_6120_);
v_a_6226_ = lean_ctor_get(v___x_6168_, 0);
v_isSharedCheck_6233_ = !lean_is_exclusive(v___x_6168_);
if (v_isSharedCheck_6233_ == 0)
{
v___x_6228_ = v___x_6168_;
v_isShared_6229_ = v_isSharedCheck_6233_;
goto v_resetjp_6227_;
}
else
{
lean_inc(v_a_6226_);
lean_dec(v___x_6168_);
v___x_6228_ = lean_box(0);
v_isShared_6229_ = v_isSharedCheck_6233_;
goto v_resetjp_6227_;
}
v_resetjp_6227_:
{
lean_object* v___x_6231_; 
if (v_isShared_6229_ == 0)
{
v___x_6231_ = v___x_6228_;
goto v_reusejp_6230_;
}
else
{
lean_object* v_reuseFailAlloc_6232_; 
v_reuseFailAlloc_6232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6232_, 0, v_a_6226_);
v___x_6231_ = v_reuseFailAlloc_6232_;
goto v_reusejp_6230_;
}
v_reusejp_6230_:
{
return v___x_6231_;
}
}
}
v___jp_6130_:
{
lean_object* v___x_6139_; 
v___x_6139_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_6131_, v___y_6133_);
if (lean_obj_tag(v___x_6139_) == 0)
{
lean_object* v_a_6140_; uint8_t v___x_6141_; 
v_a_6140_ = lean_ctor_get(v___x_6139_, 0);
lean_inc(v_a_6140_);
lean_dec_ref_known(v___x_6139_, 1);
v___x_6141_ = lean_unbox(v_a_6140_);
lean_dec(v_a_6140_);
if (v___x_6141_ == 0)
{
lean_object* v___x_6142_; 
lean_dec_ref(v_onTrue_6132_);
v___x_6142_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_6131_, v___y_6133_);
if (lean_obj_tag(v___x_6142_) == 0)
{
lean_object* v_a_6143_; uint8_t v___x_6144_; 
v_a_6143_ = lean_ctor_get(v___x_6142_, 0);
lean_inc(v_a_6143_);
lean_dec_ref_known(v___x_6142_, 1);
v___x_6144_ = lean_unbox(v_a_6143_);
lean_dec(v_a_6143_);
if (v___x_6144_ == 0)
{
lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; 
v___x_6145_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1);
v___x_6146_ = l_Lean_indentExpr(v_e_6131_);
v___x_6147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6147_, 0, v___x_6145_);
lean_ctor_set(v___x_6147_, 1, v___x_6146_);
v___x_6148_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6147_, v___y_6135_, v___y_6136_, v___y_6137_, v___y_6138_);
return v___x_6148_;
}
else
{
lean_object* v___x_6149_; lean_object* v___x_6150_; 
lean_dec_ref(v_e_6131_);
v___x_6149_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3);
v___x_6150_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6149_, v___y_6135_, v___y_6136_, v___y_6137_, v___y_6138_);
return v___x_6150_;
}
}
else
{
lean_object* v_a_6151_; lean_object* v___x_6153_; uint8_t v_isShared_6154_; uint8_t v_isSharedCheck_6158_; 
lean_dec_ref(v_e_6131_);
v_a_6151_ = lean_ctor_get(v___x_6142_, 0);
v_isSharedCheck_6158_ = !lean_is_exclusive(v___x_6142_);
if (v_isSharedCheck_6158_ == 0)
{
v___x_6153_ = v___x_6142_;
v_isShared_6154_ = v_isSharedCheck_6158_;
goto v_resetjp_6152_;
}
else
{
lean_inc(v_a_6151_);
lean_dec(v___x_6142_);
v___x_6153_ = lean_box(0);
v_isShared_6154_ = v_isSharedCheck_6158_;
goto v_resetjp_6152_;
}
v_resetjp_6152_:
{
lean_object* v___x_6156_; 
if (v_isShared_6154_ == 0)
{
v___x_6156_ = v___x_6153_;
goto v_reusejp_6155_;
}
else
{
lean_object* v_reuseFailAlloc_6157_; 
v_reuseFailAlloc_6157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6157_, 0, v_a_6151_);
v___x_6156_ = v_reuseFailAlloc_6157_;
goto v_reusejp_6155_;
}
v_reusejp_6155_:
{
return v___x_6156_;
}
}
}
}
else
{
lean_object* v___x_6159_; 
lean_dec_ref(v_e_6131_);
lean_inc(v___y_6138_);
lean_inc_ref(v___y_6137_);
lean_inc(v___y_6136_);
lean_inc_ref(v___y_6135_);
lean_inc(v___y_6134_);
lean_inc_ref(v___y_6133_);
v___x_6159_ = lean_apply_7(v_onTrue_6132_, v___y_6133_, v___y_6134_, v___y_6135_, v___y_6136_, v___y_6137_, v___y_6138_, lean_box(0));
return v___x_6159_;
}
}
else
{
lean_object* v_a_6160_; lean_object* v___x_6162_; uint8_t v_isShared_6163_; uint8_t v_isSharedCheck_6167_; 
lean_dec_ref(v_onTrue_6132_);
lean_dec_ref(v_e_6131_);
v_a_6160_ = lean_ctor_get(v___x_6139_, 0);
v_isSharedCheck_6167_ = !lean_is_exclusive(v___x_6139_);
if (v_isSharedCheck_6167_ == 0)
{
v___x_6162_ = v___x_6139_;
v_isShared_6163_ = v_isSharedCheck_6167_;
goto v_resetjp_6161_;
}
else
{
lean_inc(v_a_6160_);
lean_dec(v___x_6139_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed(lean_object* v_m_6234_, lean_object* v___x_6235_, lean_object* v_hasTrace_6236_, lean_object* v_cls_6237_, lean_object* v___y_6238_, lean_object* v___y_6239_, lean_object* v___y_6240_, lean_object* v___y_6241_, lean_object* v___y_6242_, lean_object* v___y_6243_, lean_object* v___y_6244_){
_start:
{
uint8_t v_hasTrace_boxed_6245_; lean_object* v_res_6246_; 
v_hasTrace_boxed_6245_ = lean_unbox(v_hasTrace_6236_);
v_res_6246_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4(v_m_6234_, v___x_6235_, v_hasTrace_boxed_6245_, v_cls_6237_, v___y_6238_, v___y_6239_, v___y_6240_, v___y_6241_, v___y_6242_, v___y_6243_);
lean_dec(v___y_6243_);
lean_dec_ref(v___y_6242_);
lean_dec(v___y_6241_);
lean_dec_ref(v___y_6240_);
lean_dec(v___y_6239_);
lean_dec_ref(v___y_6238_);
return v_res_6246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6(lean_object* v_m_6247_, lean_object* v___x_6248_, uint8_t v___x_6249_, lean_object* v_cls_6250_, lean_object* v___y_6251_, lean_object* v___y_6252_, lean_object* v___y_6253_, lean_object* v___y_6254_, lean_object* v___y_6255_, lean_object* v___y_6256_){
_start:
{
lean_object* v_e_6259_; lean_object* v_onTrue_6260_; lean_object* v___y_6261_; lean_object* v___y_6262_; lean_object* v___y_6263_; lean_object* v___y_6264_; lean_object* v___y_6265_; lean_object* v___y_6266_; lean_object* v___x_6296_; 
v___x_6296_ = l_Lean_Meta_Sym_preprocessMVar(v_m_6247_, v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_, v___y_6256_);
if (lean_obj_tag(v___x_6296_) == 0)
{
lean_object* v_a_6297_; lean_object* v___x_6298_; 
v_a_6297_ = lean_ctor_get(v___x_6296_, 0);
lean_inc_n(v_a_6297_, 2);
lean_dec_ref_known(v___x_6296_, 1);
v___x_6298_ = l_Lean_MVarId_getType(v_a_6297_, v___y_6253_, v___y_6254_, v___y_6255_, v___y_6256_);
if (lean_obj_tag(v___x_6298_) == 0)
{
lean_object* v_a_6299_; lean_object* v___x_6300_; lean_object* v___x_6301_; uint8_t v___x_6302_; 
v_a_6299_ = lean_ctor_get(v___x_6298_, 0);
lean_inc(v_a_6299_);
lean_dec_ref_known(v___x_6298_, 1);
v___x_6300_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__4));
v___x_6301_ = lean_unsigned_to_nat(3u);
v___x_6302_ = l_Lean_Expr_isAppOfArity(v_a_6299_, v___x_6300_, v___x_6301_);
if (v___x_6302_ == 0)
{
lean_object* v___x_6303_; lean_object* v___x_6304_; lean_object* v___x_6305_; lean_object* v___x_6306_; 
lean_dec(v_a_6297_);
lean_dec(v_cls_6250_);
lean_dec_ref(v___x_6248_);
v___x_6303_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__6);
v___x_6304_ = l_Lean_indentExpr(v_a_6299_);
v___x_6305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6305_, 0, v___x_6303_);
lean_ctor_set(v___x_6305_, 1, v___x_6304_);
v___x_6306_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6305_, v___y_6253_, v___y_6254_, v___y_6255_, v___y_6256_);
return v___x_6306_;
}
else
{
lean_object* v___x_6307_; lean_object* v___x_6308_; lean_object* v___x_6309_; 
v___x_6307_ = l_Lean_Expr_appFn_x21(v_a_6299_);
lean_dec(v_a_6299_);
v___x_6308_ = l_Lean_Expr_appArg_x21(v___x_6307_);
lean_dec_ref(v___x_6307_);
lean_inc_ref(v___x_6308_);
v___x_6309_ = l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_cbvCore(v___x_6308_, v___x_6248_, v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_, v___y_6256_);
if (lean_obj_tag(v___x_6309_) == 0)
{
lean_object* v_options_6310_; lean_object* v_a_6311_; lean_object* v_inheritedTraceOptions_6312_; uint8_t v_hasTrace_6313_; lean_object* v___x_6314_; lean_object* v___f_6315_; lean_object* v___y_6317_; lean_object* v___y_6318_; lean_object* v___y_6319_; lean_object* v___y_6320_; lean_object* v___y_6321_; lean_object* v___y_6322_; 
v_options_6310_ = lean_ctor_get(v___y_6255_, 2);
v_a_6311_ = lean_ctor_get(v___x_6309_, 0);
lean_inc(v_a_6311_);
lean_dec_ref_known(v___x_6309_, 1);
v_inheritedTraceOptions_6312_ = lean_ctor_get(v___y_6255_, 13);
v_hasTrace_6313_ = lean_ctor_get_uint8(v_options_6310_, sizeof(void*)*1);
v___x_6314_ = lean_box(v___x_6249_);
lean_inc(v_a_6297_);
v___f_6315_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__0___boxed), 9, 2);
lean_closure_set(v___f_6315_, 0, v_a_6297_);
lean_closure_set(v___f_6315_, 1, v___x_6314_);
if (v_hasTrace_6313_ == 0)
{
lean_dec(v_cls_6250_);
v___y_6317_ = v___y_6251_;
v___y_6318_ = v___y_6252_;
v___y_6319_ = v___y_6253_;
v___y_6320_ = v___y_6254_;
v___y_6321_ = v___y_6255_;
v___y_6322_ = v___y_6256_;
goto v___jp_6316_;
}
else
{
lean_object* v___x_6326_; lean_object* v___x_6327_; uint8_t v___x_6328_; 
v___x_6326_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__3));
lean_inc(v_cls_6250_);
v___x_6327_ = l_Lean_Name_append(v___x_6326_, v_cls_6250_);
v___x_6328_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6312_, v_options_6310_, v___x_6327_);
lean_dec(v___x_6327_);
if (v___x_6328_ == 0)
{
lean_dec(v_cls_6250_);
v___y_6317_ = v___y_6251_;
v___y_6318_ = v___y_6252_;
v___y_6319_ = v___y_6253_;
v___y_6320_ = v___y_6254_;
v___y_6321_ = v___y_6255_;
v___y_6322_ = v___y_6256_;
goto v___jp_6316_;
}
else
{
lean_object* v___x_6329_; lean_object* v___x_6330_; lean_object* v___x_6331_; lean_object* v___x_6332_; lean_object* v___x_6333_; lean_object* v___x_6334_; lean_object* v___x_6335_; lean_object* v___x_6336_; lean_object* v___x_6337_; 
v___x_6329_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__8);
lean_inc_ref(v___x_6308_);
v___x_6330_ = l_Lean_indentExpr(v___x_6308_);
v___x_6331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6331_, 0, v___x_6329_);
lean_ctor_set(v___x_6331_, 1, v___x_6330_);
v___x_6332_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations___closed__10);
v___x_6333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6333_, 0, v___x_6331_);
lean_ctor_set(v___x_6333_, 1, v___x_6332_);
v___x_6334_ = l_Lean_Meta_Sym_Simp_Result_getResultExpr(v___x_6308_, v_a_6311_);
v___x_6335_ = l_Lean_indentExpr(v___x_6334_);
v___x_6336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6336_, 0, v___x_6333_);
lean_ctor_set(v___x_6336_, 1, v___x_6335_);
v___x_6337_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_6250_, v___x_6336_, v___y_6253_, v___y_6254_, v___y_6255_, v___y_6256_);
if (lean_obj_tag(v___x_6337_) == 0)
{
lean_dec_ref_known(v___x_6337_, 1);
v___y_6317_ = v___y_6251_;
v___y_6318_ = v___y_6252_;
v___y_6319_ = v___y_6253_;
v___y_6320_ = v___y_6254_;
v___y_6321_ = v___y_6255_;
v___y_6322_ = v___y_6256_;
goto v___jp_6316_;
}
else
{
lean_dec_ref(v___f_6315_);
lean_dec(v_a_6311_);
lean_dec_ref(v___x_6308_);
lean_dec(v_a_6297_);
return v___x_6337_;
}
}
}
v___jp_6316_:
{
if (lean_obj_tag(v_a_6311_) == 0)
{
lean_dec_ref_known(v_a_6311_, 0);
lean_dec(v_a_6297_);
v_e_6259_ = v___x_6308_;
v_onTrue_6260_ = v___f_6315_;
v___y_6261_ = v___y_6317_;
v___y_6262_ = v___y_6318_;
v___y_6263_ = v___y_6319_;
v___y_6264_ = v___y_6320_;
v___y_6265_ = v___y_6321_;
v___y_6266_ = v___y_6322_;
goto v___jp_6258_;
}
else
{
lean_object* v_e_x27_6323_; lean_object* v_proof_6324_; lean_object* v___x_6325_; 
lean_dec_ref(v___f_6315_);
lean_dec_ref(v___x_6308_);
v_e_x27_6323_ = lean_ctor_get(v_a_6311_, 0);
lean_inc_ref(v_e_x27_6323_);
v_proof_6324_ = lean_ctor_get(v_a_6311_, 1);
lean_inc_ref(v_proof_6324_);
lean_dec_ref_known(v_a_6311_, 2);
v___x_6325_ = lean_alloc_closure((void*)(l_Lean_MVarId_assign___at___00Lean_Meta_Tactic_Cbv_cbvGoalCore_spec__0___boxed), 9, 2);
lean_closure_set(v___x_6325_, 0, v_a_6297_);
lean_closure_set(v___x_6325_, 1, v_proof_6324_);
v_e_6259_ = v_e_x27_6323_;
v_onTrue_6260_ = v___x_6325_;
v___y_6261_ = v___y_6317_;
v___y_6262_ = v___y_6318_;
v___y_6263_ = v___y_6319_;
v___y_6264_ = v___y_6320_;
v___y_6265_ = v___y_6321_;
v___y_6266_ = v___y_6322_;
goto v___jp_6258_;
}
}
}
else
{
lean_object* v_a_6338_; lean_object* v___x_6340_; uint8_t v_isShared_6341_; uint8_t v_isSharedCheck_6345_; 
lean_dec_ref(v___x_6308_);
lean_dec(v_a_6297_);
lean_dec(v_cls_6250_);
v_a_6338_ = lean_ctor_get(v___x_6309_, 0);
v_isSharedCheck_6345_ = !lean_is_exclusive(v___x_6309_);
if (v_isSharedCheck_6345_ == 0)
{
v___x_6340_ = v___x_6309_;
v_isShared_6341_ = v_isSharedCheck_6345_;
goto v_resetjp_6339_;
}
else
{
lean_inc(v_a_6338_);
lean_dec(v___x_6309_);
v___x_6340_ = lean_box(0);
v_isShared_6341_ = v_isSharedCheck_6345_;
goto v_resetjp_6339_;
}
v_resetjp_6339_:
{
lean_object* v___x_6343_; 
if (v_isShared_6341_ == 0)
{
v___x_6343_ = v___x_6340_;
goto v_reusejp_6342_;
}
else
{
lean_object* v_reuseFailAlloc_6344_; 
v_reuseFailAlloc_6344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6344_, 0, v_a_6338_);
v___x_6343_ = v_reuseFailAlloc_6344_;
goto v_reusejp_6342_;
}
v_reusejp_6342_:
{
return v___x_6343_;
}
}
}
}
}
else
{
lean_object* v_a_6346_; lean_object* v___x_6348_; uint8_t v_isShared_6349_; uint8_t v_isSharedCheck_6353_; 
lean_dec(v_a_6297_);
lean_dec(v_cls_6250_);
lean_dec_ref(v___x_6248_);
v_a_6346_ = lean_ctor_get(v___x_6298_, 0);
v_isSharedCheck_6353_ = !lean_is_exclusive(v___x_6298_);
if (v_isSharedCheck_6353_ == 0)
{
v___x_6348_ = v___x_6298_;
v_isShared_6349_ = v_isSharedCheck_6353_;
goto v_resetjp_6347_;
}
else
{
lean_inc(v_a_6346_);
lean_dec(v___x_6298_);
v___x_6348_ = lean_box(0);
v_isShared_6349_ = v_isSharedCheck_6353_;
goto v_resetjp_6347_;
}
v_resetjp_6347_:
{
lean_object* v___x_6351_; 
if (v_isShared_6349_ == 0)
{
v___x_6351_ = v___x_6348_;
goto v_reusejp_6350_;
}
else
{
lean_object* v_reuseFailAlloc_6352_; 
v_reuseFailAlloc_6352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6352_, 0, v_a_6346_);
v___x_6351_ = v_reuseFailAlloc_6352_;
goto v_reusejp_6350_;
}
v_reusejp_6350_:
{
return v___x_6351_;
}
}
}
}
else
{
lean_object* v_a_6354_; lean_object* v___x_6356_; uint8_t v_isShared_6357_; uint8_t v_isSharedCheck_6361_; 
lean_dec(v_cls_6250_);
lean_dec_ref(v___x_6248_);
v_a_6354_ = lean_ctor_get(v___x_6296_, 0);
v_isSharedCheck_6361_ = !lean_is_exclusive(v___x_6296_);
if (v_isSharedCheck_6361_ == 0)
{
v___x_6356_ = v___x_6296_;
v_isShared_6357_ = v_isSharedCheck_6361_;
goto v_resetjp_6355_;
}
else
{
lean_inc(v_a_6354_);
lean_dec(v___x_6296_);
v___x_6356_ = lean_box(0);
v_isShared_6357_ = v_isSharedCheck_6361_;
goto v_resetjp_6355_;
}
v_resetjp_6355_:
{
lean_object* v___x_6359_; 
if (v_isShared_6357_ == 0)
{
v___x_6359_ = v___x_6356_;
goto v_reusejp_6358_;
}
else
{
lean_object* v_reuseFailAlloc_6360_; 
v_reuseFailAlloc_6360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6360_, 0, v_a_6354_);
v___x_6359_ = v_reuseFailAlloc_6360_;
goto v_reusejp_6358_;
}
v_reusejp_6358_:
{
return v___x_6359_;
}
}
}
v___jp_6258_:
{
lean_object* v___x_6267_; 
v___x_6267_ = l_Lean_Meta_Sym_isBoolTrueExpr___redArg(v_e_6259_, v___y_6261_);
if (lean_obj_tag(v___x_6267_) == 0)
{
lean_object* v_a_6268_; uint8_t v___x_6269_; 
v_a_6268_ = lean_ctor_get(v___x_6267_, 0);
lean_inc(v_a_6268_);
lean_dec_ref_known(v___x_6267_, 1);
v___x_6269_ = lean_unbox(v_a_6268_);
lean_dec(v_a_6268_);
if (v___x_6269_ == 0)
{
lean_object* v___x_6270_; 
lean_dec_ref(v_onTrue_6260_);
v___x_6270_ = l_Lean_Meta_Sym_isBoolFalseExpr___redArg(v_e_6259_, v___y_6261_);
if (lean_obj_tag(v___x_6270_) == 0)
{
lean_object* v_a_6271_; uint8_t v___x_6272_; 
v_a_6271_ = lean_ctor_get(v___x_6270_, 0);
lean_inc(v_a_6271_);
lean_dec_ref_known(v___x_6270_, 1);
v___x_6272_ = lean_unbox(v_a_6271_);
lean_dec(v_a_6271_);
if (v___x_6272_ == 0)
{
lean_object* v___x_6273_; lean_object* v___x_6274_; lean_object* v___x_6275_; lean_object* v___x_6276_; 
v___x_6273_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__1);
v___x_6274_ = l_Lean_indentExpr(v_e_6259_);
v___x_6275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6275_, 0, v___x_6273_);
lean_ctor_set(v___x_6275_, 1, v___x_6274_);
v___x_6276_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6275_, v___y_6263_, v___y_6264_, v___y_6265_, v___y_6266_);
return v___x_6276_;
}
else
{
lean_object* v___x_6277_; lean_object* v___x_6278_; 
lean_dec_ref(v_e_6259_);
v___x_6277_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3, &l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3_once, _init_l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___closed__3);
v___x_6278_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v___x_6277_, v___y_6263_, v___y_6264_, v___y_6265_, v___y_6266_);
return v___x_6278_;
}
}
else
{
lean_object* v_a_6279_; lean_object* v___x_6281_; uint8_t v_isShared_6282_; uint8_t v_isSharedCheck_6286_; 
lean_dec_ref(v_e_6259_);
v_a_6279_ = lean_ctor_get(v___x_6270_, 0);
v_isSharedCheck_6286_ = !lean_is_exclusive(v___x_6270_);
if (v_isSharedCheck_6286_ == 0)
{
v___x_6281_ = v___x_6270_;
v_isShared_6282_ = v_isSharedCheck_6286_;
goto v_resetjp_6280_;
}
else
{
lean_inc(v_a_6279_);
lean_dec(v___x_6270_);
v___x_6281_ = lean_box(0);
v_isShared_6282_ = v_isSharedCheck_6286_;
goto v_resetjp_6280_;
}
v_resetjp_6280_:
{
lean_object* v___x_6284_; 
if (v_isShared_6282_ == 0)
{
v___x_6284_ = v___x_6281_;
goto v_reusejp_6283_;
}
else
{
lean_object* v_reuseFailAlloc_6285_; 
v_reuseFailAlloc_6285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6285_, 0, v_a_6279_);
v___x_6284_ = v_reuseFailAlloc_6285_;
goto v_reusejp_6283_;
}
v_reusejp_6283_:
{
return v___x_6284_;
}
}
}
}
else
{
lean_object* v___x_6287_; 
lean_dec_ref(v_e_6259_);
lean_inc(v___y_6266_);
lean_inc_ref(v___y_6265_);
lean_inc(v___y_6264_);
lean_inc_ref(v___y_6263_);
lean_inc(v___y_6262_);
lean_inc_ref(v___y_6261_);
v___x_6287_ = lean_apply_7(v_onTrue_6260_, v___y_6261_, v___y_6262_, v___y_6263_, v___y_6264_, v___y_6265_, v___y_6266_, lean_box(0));
return v___x_6287_;
}
}
else
{
lean_object* v_a_6288_; lean_object* v___x_6290_; uint8_t v_isShared_6291_; uint8_t v_isSharedCheck_6295_; 
lean_dec_ref(v_onTrue_6260_);
lean_dec_ref(v_e_6259_);
v_a_6288_ = lean_ctor_get(v___x_6267_, 0);
v_isSharedCheck_6295_ = !lean_is_exclusive(v___x_6267_);
if (v_isSharedCheck_6295_ == 0)
{
v___x_6290_ = v___x_6267_;
v_isShared_6291_ = v_isSharedCheck_6295_;
goto v_resetjp_6289_;
}
else
{
lean_inc(v_a_6288_);
lean_dec(v___x_6267_);
v___x_6290_ = lean_box(0);
v_isShared_6291_ = v_isSharedCheck_6295_;
goto v_resetjp_6289_;
}
v_resetjp_6289_:
{
lean_object* v___x_6293_; 
if (v_isShared_6291_ == 0)
{
v___x_6293_ = v___x_6290_;
goto v_reusejp_6292_;
}
else
{
lean_object* v_reuseFailAlloc_6294_; 
v_reuseFailAlloc_6294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6294_, 0, v_a_6288_);
v___x_6293_ = v_reuseFailAlloc_6294_;
goto v_reusejp_6292_;
}
v_reusejp_6292_:
{
return v___x_6293_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6___boxed(lean_object* v_m_6362_, lean_object* v___x_6363_, lean_object* v___x_6364_, lean_object* v_cls_6365_, lean_object* v___y_6366_, lean_object* v___y_6367_, lean_object* v___y_6368_, lean_object* v___y_6369_, lean_object* v___y_6370_, lean_object* v___y_6371_, lean_object* v___y_6372_){
_start:
{
uint8_t v___x_25974__boxed_6373_; lean_object* v_res_6374_; 
v___x_25974__boxed_6373_ = lean_unbox(v___x_6364_);
v_res_6374_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6(v_m_6362_, v___x_6363_, v___x_25974__boxed_6373_, v_cls_6365_, v___y_6366_, v___y_6367_, v___y_6368_, v___y_6369_, v___y_6370_, v___y_6371_);
lean_dec(v___y_6371_);
lean_dec_ref(v___y_6370_);
lean_dec(v___y_6369_);
lean_dec_ref(v___y_6368_);
lean_dec(v___y_6367_);
lean_dec_ref(v___y_6366_);
return v_res_6374_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(lean_object* v_e_6375_){
_start:
{
if (lean_obj_tag(v_e_6375_) == 0)
{
uint8_t v___x_6376_; 
v___x_6376_ = 2;
return v___x_6376_;
}
else
{
uint8_t v___x_6377_; 
v___x_6377_ = 0;
return v___x_6377_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2___boxed(lean_object* v_e_6378_){
_start:
{
uint8_t v_res_6379_; lean_object* v_r_6380_; 
v_res_6379_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(v_e_6378_);
lean_dec_ref(v_e_6378_);
v_r_6380_ = lean_box(v_res_6379_);
return v_r_6380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(lean_object* v_cls_6381_, uint8_t v_collapsed_6382_, lean_object* v_tag_6383_, lean_object* v_opts_6384_, uint8_t v_clsEnabled_6385_, lean_object* v_oldTraces_6386_, lean_object* v_msg_6387_, lean_object* v_resStartStop_6388_, lean_object* v___y_6389_, lean_object* v___y_6390_, lean_object* v___y_6391_, lean_object* v___y_6392_){
_start:
{
lean_object* v_fst_6394_; lean_object* v_snd_6395_; lean_object* v___y_6397_; lean_object* v___y_6398_; lean_object* v_data_6399_; lean_object* v_fst_6402_; lean_object* v_snd_6403_; lean_object* v___x_6404_; uint8_t v___x_6405_; lean_object* v___y_6407_; lean_object* v_a_6408_; uint8_t v___y_6423_; double v___y_6454_; 
v_fst_6394_ = lean_ctor_get(v_resStartStop_6388_, 0);
lean_inc(v_fst_6394_);
v_snd_6395_ = lean_ctor_get(v_resStartStop_6388_, 1);
lean_inc(v_snd_6395_);
lean_dec_ref(v_resStartStop_6388_);
v_fst_6402_ = lean_ctor_get(v_snd_6395_, 0);
lean_inc(v_fst_6402_);
v_snd_6403_ = lean_ctor_get(v_snd_6395_, 1);
lean_inc(v_snd_6403_);
lean_dec(v_snd_6395_);
v___x_6404_ = l_Lean_trace_profiler;
v___x_6405_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_6384_, v___x_6404_);
if (v___x_6405_ == 0)
{
v___y_6423_ = v___x_6405_;
goto v___jp_6422_;
}
else
{
lean_object* v___x_6459_; uint8_t v___x_6460_; 
v___x_6459_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6460_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_opts_6384_, v___x_6459_);
if (v___x_6460_ == 0)
{
lean_object* v___x_6461_; lean_object* v___x_6462_; double v___x_6463_; double v___x_6464_; double v___x_6465_; 
v___x_6461_ = l_Lean_trace_profiler_threshold;
v___x_6462_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_6384_, v___x_6461_);
v___x_6463_ = lean_float_of_nat(v___x_6462_);
v___x_6464_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__2);
v___x_6465_ = lean_float_div(v___x_6463_, v___x_6464_);
v___y_6454_ = v___x_6465_;
goto v___jp_6453_;
}
else
{
lean_object* v___x_6466_; lean_object* v___x_6467_; double v___x_6468_; 
v___x_6466_ = l_Lean_trace_profiler_threshold;
v___x_6467_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_opts_6384_, v___x_6466_);
v___x_6468_ = lean_float_of_nat(v___x_6467_);
v___y_6454_ = v___x_6468_;
goto v___jp_6453_;
}
}
v___jp_6396_:
{
lean_object* v___x_6400_; 
lean_inc(v___y_6398_);
v___x_6400_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__1(v_oldTraces_6386_, v_data_6399_, v___y_6398_, v___y_6397_, v___y_6389_, v___y_6390_, v___y_6391_, v___y_6392_);
if (lean_obj_tag(v___x_6400_) == 0)
{
lean_object* v___x_6401_; 
lean_dec_ref_known(v___x_6400_, 1);
v___x_6401_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_6394_);
return v___x_6401_;
}
else
{
lean_dec(v_fst_6394_);
return v___x_6400_;
}
}
v___jp_6406_:
{
uint8_t v_result_6409_; lean_object* v___x_6410_; lean_object* v___x_6411_; double v___x_6412_; lean_object* v_data_6413_; 
v_result_6409_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2_spec__2(v_fst_6394_);
v___x_6410_ = lean_box(v_result_6409_);
v___x_6411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6411_, 0, v___x_6410_);
v___x_6412_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__0);
lean_inc_ref(v_tag_6383_);
lean_inc_ref(v___x_6411_);
lean_inc(v_cls_6381_);
v_data_6413_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6413_, 0, v_cls_6381_);
lean_ctor_set(v_data_6413_, 1, v___x_6411_);
lean_ctor_set(v_data_6413_, 2, v_tag_6383_);
lean_ctor_set_float(v_data_6413_, sizeof(void*)*3, v___x_6412_);
lean_ctor_set_float(v_data_6413_, sizeof(void*)*3 + 8, v___x_6412_);
lean_ctor_set_uint8(v_data_6413_, sizeof(void*)*3 + 16, v_collapsed_6382_);
if (v___x_6405_ == 0)
{
lean_dec_ref_known(v___x_6411_, 1);
lean_dec(v_snd_6403_);
lean_dec(v_fst_6402_);
lean_dec_ref(v_tag_6383_);
lean_dec(v_cls_6381_);
v___y_6397_ = v_a_6408_;
v___y_6398_ = v___y_6407_;
v_data_6399_ = v_data_6413_;
goto v___jp_6396_;
}
else
{
lean_object* v_data_6414_; double v___x_6415_; double v___x_6416_; 
lean_dec_ref_known(v_data_6413_, 3);
v_data_6414_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_6414_, 0, v_cls_6381_);
lean_ctor_set(v_data_6414_, 1, v___x_6411_);
lean_ctor_set(v_data_6414_, 2, v_tag_6383_);
v___x_6415_ = lean_unbox_float(v_fst_6402_);
lean_dec(v_fst_6402_);
lean_ctor_set_float(v_data_6414_, sizeof(void*)*3, v___x_6415_);
v___x_6416_ = lean_unbox_float(v_snd_6403_);
lean_dec(v_snd_6403_);
lean_ctor_set_float(v_data_6414_, sizeof(void*)*3 + 8, v___x_6416_);
lean_ctor_set_uint8(v_data_6414_, sizeof(void*)*3 + 16, v_collapsed_6382_);
v___y_6397_ = v_a_6408_;
v___y_6398_ = v___y_6407_;
v_data_6399_ = v_data_6414_;
goto v___jp_6396_;
}
}
v___jp_6417_:
{
lean_object* v_ref_6418_; lean_object* v___x_6419_; 
v_ref_6418_ = lean_ctor_get(v___y_6391_, 5);
lean_inc(v___y_6392_);
lean_inc_ref(v___y_6391_);
lean_inc(v___y_6390_);
lean_inc_ref(v___y_6389_);
lean_inc(v_fst_6394_);
v___x_6419_ = lean_apply_6(v_msg_6387_, v_fst_6394_, v___y_6389_, v___y_6390_, v___y_6391_, v___y_6392_, lean_box(0));
if (lean_obj_tag(v___x_6419_) == 0)
{
lean_object* v_a_6420_; 
v_a_6420_ = lean_ctor_get(v___x_6419_, 0);
lean_inc(v_a_6420_);
lean_dec_ref_known(v___x_6419_, 1);
v___y_6407_ = v_ref_6418_;
v_a_6408_ = v_a_6420_;
goto v___jp_6406_;
}
else
{
lean_object* v___x_6421_; 
lean_dec_ref_known(v___x_6419_, 1);
v___x_6421_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4___closed__1);
v___y_6407_ = v_ref_6418_;
v_a_6408_ = v___x_6421_;
goto v___jp_6406_;
}
}
v___jp_6422_:
{
if (v_clsEnabled_6385_ == 0)
{
if (v___y_6423_ == 0)
{
lean_object* v___x_6424_; lean_object* v_traceState_6425_; lean_object* v_env_6426_; lean_object* v_nextMacroScope_6427_; lean_object* v_ngen_6428_; lean_object* v_auxDeclNGen_6429_; lean_object* v_cache_6430_; lean_object* v_messages_6431_; lean_object* v_infoState_6432_; lean_object* v_snapshotTasks_6433_; lean_object* v___x_6435_; uint8_t v_isShared_6436_; uint8_t v_isSharedCheck_6452_; 
lean_dec(v_snd_6403_);
lean_dec(v_fst_6402_);
lean_dec_ref(v_msg_6387_);
lean_dec_ref(v_tag_6383_);
lean_dec(v_cls_6381_);
v___x_6424_ = lean_st_ref_take(v___y_6392_);
v_traceState_6425_ = lean_ctor_get(v___x_6424_, 4);
v_env_6426_ = lean_ctor_get(v___x_6424_, 0);
v_nextMacroScope_6427_ = lean_ctor_get(v___x_6424_, 1);
v_ngen_6428_ = lean_ctor_get(v___x_6424_, 2);
v_auxDeclNGen_6429_ = lean_ctor_get(v___x_6424_, 3);
v_cache_6430_ = lean_ctor_get(v___x_6424_, 5);
v_messages_6431_ = lean_ctor_get(v___x_6424_, 6);
v_infoState_6432_ = lean_ctor_get(v___x_6424_, 7);
v_snapshotTasks_6433_ = lean_ctor_get(v___x_6424_, 8);
v_isSharedCheck_6452_ = !lean_is_exclusive(v___x_6424_);
if (v_isSharedCheck_6452_ == 0)
{
v___x_6435_ = v___x_6424_;
v_isShared_6436_ = v_isSharedCheck_6452_;
goto v_resetjp_6434_;
}
else
{
lean_inc(v_snapshotTasks_6433_);
lean_inc(v_infoState_6432_);
lean_inc(v_messages_6431_);
lean_inc(v_cache_6430_);
lean_inc(v_traceState_6425_);
lean_inc(v_auxDeclNGen_6429_);
lean_inc(v_ngen_6428_);
lean_inc(v_nextMacroScope_6427_);
lean_inc(v_env_6426_);
lean_dec(v___x_6424_);
v___x_6435_ = lean_box(0);
v_isShared_6436_ = v_isSharedCheck_6452_;
goto v_resetjp_6434_;
}
v_resetjp_6434_:
{
uint64_t v_tid_6437_; lean_object* v_traces_6438_; lean_object* v___x_6440_; uint8_t v_isShared_6441_; uint8_t v_isSharedCheck_6451_; 
v_tid_6437_ = lean_ctor_get_uint64(v_traceState_6425_, sizeof(void*)*1);
v_traces_6438_ = lean_ctor_get(v_traceState_6425_, 0);
v_isSharedCheck_6451_ = !lean_is_exclusive(v_traceState_6425_);
if (v_isSharedCheck_6451_ == 0)
{
v___x_6440_ = v_traceState_6425_;
v_isShared_6441_ = v_isSharedCheck_6451_;
goto v_resetjp_6439_;
}
else
{
lean_inc(v_traces_6438_);
lean_dec(v_traceState_6425_);
v___x_6440_ = lean_box(0);
v_isShared_6441_ = v_isSharedCheck_6451_;
goto v_resetjp_6439_;
}
v_resetjp_6439_:
{
lean_object* v___x_6442_; lean_object* v___x_6444_; 
v___x_6442_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_6386_, v_traces_6438_);
lean_dec_ref(v_traces_6438_);
if (v_isShared_6441_ == 0)
{
lean_ctor_set(v___x_6440_, 0, v___x_6442_);
v___x_6444_ = v___x_6440_;
goto v_reusejp_6443_;
}
else
{
lean_object* v_reuseFailAlloc_6450_; 
v_reuseFailAlloc_6450_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_6450_, 0, v___x_6442_);
lean_ctor_set_uint64(v_reuseFailAlloc_6450_, sizeof(void*)*1, v_tid_6437_);
v___x_6444_ = v_reuseFailAlloc_6450_;
goto v_reusejp_6443_;
}
v_reusejp_6443_:
{
lean_object* v___x_6446_; 
if (v_isShared_6436_ == 0)
{
lean_ctor_set(v___x_6435_, 4, v___x_6444_);
v___x_6446_ = v___x_6435_;
goto v_reusejp_6445_;
}
else
{
lean_object* v_reuseFailAlloc_6449_; 
v_reuseFailAlloc_6449_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_6449_, 0, v_env_6426_);
lean_ctor_set(v_reuseFailAlloc_6449_, 1, v_nextMacroScope_6427_);
lean_ctor_set(v_reuseFailAlloc_6449_, 2, v_ngen_6428_);
lean_ctor_set(v_reuseFailAlloc_6449_, 3, v_auxDeclNGen_6429_);
lean_ctor_set(v_reuseFailAlloc_6449_, 4, v___x_6444_);
lean_ctor_set(v_reuseFailAlloc_6449_, 5, v_cache_6430_);
lean_ctor_set(v_reuseFailAlloc_6449_, 6, v_messages_6431_);
lean_ctor_set(v_reuseFailAlloc_6449_, 7, v_infoState_6432_);
lean_ctor_set(v_reuseFailAlloc_6449_, 8, v_snapshotTasks_6433_);
v___x_6446_ = v_reuseFailAlloc_6449_;
goto v_reusejp_6445_;
}
v_reusejp_6445_:
{
lean_object* v___x_6447_; lean_object* v___x_6448_; 
v___x_6447_ = lean_st_ref_set(v___y_6392_, v___x_6446_);
v___x_6448_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__1_spec__2___redArg(v_fst_6394_);
return v___x_6448_;
}
}
}
}
}
else
{
goto v___jp_6417_;
}
}
else
{
goto v___jp_6417_;
}
}
v___jp_6453_:
{
double v___x_6455_; double v___x_6456_; double v___x_6457_; uint8_t v___x_6458_; 
v___x_6455_ = lean_unbox_float(v_snd_6403_);
v___x_6456_ = lean_unbox_float(v_fst_6402_);
v___x_6457_ = lean_float_sub(v___x_6455_, v___x_6456_);
v___x_6458_ = lean_float_decLt(v___y_6454_, v___x_6457_);
v___y_6423_ = v___x_6458_;
goto v___jp_6422_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2___boxed(lean_object* v_cls_6469_, lean_object* v_collapsed_6470_, lean_object* v_tag_6471_, lean_object* v_opts_6472_, lean_object* v_clsEnabled_6473_, lean_object* v_oldTraces_6474_, lean_object* v_msg_6475_, lean_object* v_resStartStop_6476_, lean_object* v___y_6477_, lean_object* v___y_6478_, lean_object* v___y_6479_, lean_object* v___y_6480_, lean_object* v___y_6481_){
_start:
{
uint8_t v_collapsed_boxed_6482_; uint8_t v_clsEnabled_boxed_6483_; lean_object* v_res_6484_; 
v_collapsed_boxed_6482_ = lean_unbox(v_collapsed_6470_);
v_clsEnabled_boxed_6483_ = lean_unbox(v_clsEnabled_6473_);
v_res_6484_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(v_cls_6469_, v_collapsed_boxed_6482_, v_tag_6471_, v_opts_6472_, v_clsEnabled_boxed_6483_, v_oldTraces_6474_, v_msg_6475_, v_resStartStop_6476_, v___y_6477_, v___y_6478_, v___y_6479_, v___y_6480_);
lean_dec(v___y_6480_);
lean_dec_ref(v___y_6479_);
lean_dec(v___y_6478_);
lean_dec_ref(v___y_6477_);
lean_dec_ref(v_opts_6472_);
return v_res_6484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(lean_object* v_m_6486_, lean_object* v_a_6487_, lean_object* v_a_6488_, lean_object* v_a_6489_, lean_object* v_a_6490_){
_start:
{
lean_object* v_options_6492_; lean_object* v_inheritedTraceOptions_6493_; uint8_t v_hasTrace_6494_; lean_object* v_cls_6495_; 
v_options_6492_ = lean_ctor_get(v_a_6489_, 2);
v_inheritedTraceOptions_6493_ = lean_ctor_get(v_a_6489_, 13);
v_hasTrace_6494_ = lean_ctor_get_uint8(v_options_6492_, sizeof(void*)*1);
v_cls_6495_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__0));
if (v_hasTrace_6494_ == 0)
{
lean_object* v___x_6496_; lean_object* v___x_6497_; lean_object* v___x_6498_; lean_object* v___x_6499_; lean_object* v___f_6500_; lean_object* v___x_6501_; 
v___x_6496_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6497_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6492_, v___x_6496_);
v___x_6498_ = lean_unsigned_to_nat(2u);
v___x_6499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6499_, 0, v___x_6497_);
lean_ctor_set(v___x_6499_, 1, v___x_6498_);
v___f_6500_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__1___boxed), 10, 3);
lean_closure_set(v___f_6500_, 0, v_m_6486_);
lean_closure_set(v___f_6500_, 1, v___x_6499_);
lean_closure_set(v___f_6500_, 2, v_cls_6495_);
v___x_6501_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6500_, v_a_6487_, v_a_6488_, v_a_6489_, v_a_6490_);
return v___x_6501_;
}
else
{
lean_object* v___f_6502_; lean_object* v___x_6503_; lean_object* v___x_6504_; uint8_t v___x_6505_; lean_object* v___y_6507_; lean_object* v___y_6508_; lean_object* v_a_6509_; lean_object* v___y_6522_; lean_object* v___y_6523_; lean_object* v_a_6524_; 
v___f_6502_ = ((lean_object*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___closed__0));
v___x_6503_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_tryEquations_spec__0___redArg___closed__1));
v___x_6504_ = lean_obj_once(&l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1, &l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1_once, _init_l_Lean_Meta_Tactic_Cbv_cbvEntry___closed__1);
v___x_6505_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_6493_, v_options_6492_, v___x_6504_);
if (v___x_6505_ == 0)
{
lean_object* v___x_6586_; uint8_t v___x_6587_; 
v___x_6586_ = l_Lean_trace_profiler;
v___x_6587_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_6492_, v___x_6586_);
if (v___x_6587_ == 0)
{
lean_object* v___x_6588_; lean_object* v___x_6589_; lean_object* v___x_6590_; lean_object* v___x_6591_; lean_object* v___x_6592_; lean_object* v___f_6593_; lean_object* v___x_6594_; 
v___x_6588_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6589_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6492_, v___x_6588_);
v___x_6590_ = lean_unsigned_to_nat(2u);
v___x_6591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6591_, 0, v___x_6589_);
lean_ctor_set(v___x_6591_, 1, v___x_6590_);
v___x_6592_ = lean_box(v_hasTrace_6494_);
v___f_6593_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed), 11, 4);
lean_closure_set(v___f_6593_, 0, v_m_6486_);
lean_closure_set(v___f_6593_, 1, v___x_6591_);
lean_closure_set(v___f_6593_, 2, v___x_6592_);
lean_closure_set(v___f_6593_, 3, v_cls_6495_);
v___x_6594_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6593_, v_a_6487_, v_a_6488_, v_a_6489_, v_a_6490_);
return v___x_6594_;
}
else
{
goto v___jp_6533_;
}
}
else
{
goto v___jp_6533_;
}
v___jp_6506_:
{
lean_object* v___x_6510_; double v___x_6511_; double v___x_6512_; double v___x_6513_; double v___x_6514_; double v___x_6515_; lean_object* v___x_6516_; lean_object* v___x_6517_; lean_object* v___x_6518_; lean_object* v___x_6519_; lean_object* v___x_6520_; 
v___x_6510_ = lean_io_mono_nanos_now();
v___x_6511_ = lean_float_of_nat(v___y_6507_);
v___x_6512_ = lean_float_once(&l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9, &l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9_once, _init_l___private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj___closed__9);
v___x_6513_ = lean_float_div(v___x_6511_, v___x_6512_);
v___x_6514_ = lean_float_of_nat(v___x_6510_);
v___x_6515_ = lean_float_div(v___x_6514_, v___x_6512_);
v___x_6516_ = lean_box_float(v___x_6513_);
v___x_6517_ = lean_box_float(v___x_6515_);
v___x_6518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6518_, 0, v___x_6516_);
lean_ctor_set(v___x_6518_, 1, v___x_6517_);
v___x_6519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6519_, 0, v_a_6509_);
lean_ctor_set(v___x_6519_, 1, v___x_6518_);
v___x_6520_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(v_cls_6495_, v_hasTrace_6494_, v___x_6503_, v_options_6492_, v___x_6505_, v___y_6508_, v___f_6502_, v___x_6519_, v_a_6487_, v_a_6488_, v_a_6489_, v_a_6490_);
return v___x_6520_;
}
v___jp_6521_:
{
lean_object* v___x_6525_; double v___x_6526_; double v___x_6527_; lean_object* v___x_6528_; lean_object* v___x_6529_; lean_object* v___x_6530_; lean_object* v___x_6531_; lean_object* v___x_6532_; 
v___x_6525_ = lean_io_get_num_heartbeats();
v___x_6526_ = lean_float_of_nat(v___y_6522_);
v___x_6527_ = lean_float_of_nat(v___x_6525_);
v___x_6528_ = lean_box_float(v___x_6526_);
v___x_6529_ = lean_box_float(v___x_6527_);
v___x_6530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6530_, 0, v___x_6528_);
lean_ctor_set(v___x_6530_, 1, v___x_6529_);
v___x_6531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6531_, 0, v_a_6524_);
lean_ctor_set(v___x_6531_, 1, v___x_6530_);
v___x_6532_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__2(v_cls_6495_, v_hasTrace_6494_, v___x_6503_, v_options_6492_, v___x_6505_, v___y_6523_, v___f_6502_, v___x_6531_, v_a_6487_, v_a_6488_, v_a_6489_, v_a_6490_);
return v___x_6532_;
}
v___jp_6533_:
{
lean_object* v___x_6534_; lean_object* v_a_6535_; lean_object* v___x_6536_; uint8_t v___x_6537_; 
v___x_6534_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvEntry_spec__0___redArg(v_a_6490_);
v_a_6535_ = lean_ctor_get(v___x_6534_, 0);
lean_inc(v_a_6535_);
lean_dec_ref(v___x_6534_);
v___x_6536_ = l_Lean_trace_profiler_useHeartbeats;
v___x_6537_ = l_Lean_Option_get___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__3(v_options_6492_, v___x_6536_);
if (v___x_6537_ == 0)
{
lean_object* v___x_6538_; lean_object* v___x_6539_; lean_object* v___x_6540_; lean_object* v___x_6541_; lean_object* v___x_6542_; lean_object* v___x_6543_; lean_object* v___f_6544_; lean_object* v___x_6545_; 
v___x_6538_ = lean_io_mono_nanos_now();
v___x_6539_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6540_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6492_, v___x_6539_);
v___x_6541_ = lean_unsigned_to_nat(2u);
v___x_6542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6542_, 0, v___x_6540_);
lean_ctor_set(v___x_6542_, 1, v___x_6541_);
v___x_6543_ = lean_box(v_hasTrace_6494_);
v___f_6544_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__4___boxed), 11, 4);
lean_closure_set(v___f_6544_, 0, v_m_6486_);
lean_closure_set(v___f_6544_, 1, v___x_6542_);
lean_closure_set(v___f_6544_, 2, v___x_6543_);
lean_closure_set(v___f_6544_, 3, v_cls_6495_);
v___x_6545_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6544_, v_a_6487_, v_a_6488_, v_a_6489_, v_a_6490_);
if (lean_obj_tag(v___x_6545_) == 0)
{
lean_object* v_a_6546_; lean_object* v___x_6548_; uint8_t v_isShared_6549_; uint8_t v_isSharedCheck_6553_; 
v_a_6546_ = lean_ctor_get(v___x_6545_, 0);
v_isSharedCheck_6553_ = !lean_is_exclusive(v___x_6545_);
if (v_isSharedCheck_6553_ == 0)
{
v___x_6548_ = v___x_6545_;
v_isShared_6549_ = v_isSharedCheck_6553_;
goto v_resetjp_6547_;
}
else
{
lean_inc(v_a_6546_);
lean_dec(v___x_6545_);
v___x_6548_ = lean_box(0);
v_isShared_6549_ = v_isSharedCheck_6553_;
goto v_resetjp_6547_;
}
v_resetjp_6547_:
{
lean_object* v___x_6551_; 
if (v_isShared_6549_ == 0)
{
lean_ctor_set_tag(v___x_6548_, 1);
v___x_6551_ = v___x_6548_;
goto v_reusejp_6550_;
}
else
{
lean_object* v_reuseFailAlloc_6552_; 
v_reuseFailAlloc_6552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6552_, 0, v_a_6546_);
v___x_6551_ = v_reuseFailAlloc_6552_;
goto v_reusejp_6550_;
}
v_reusejp_6550_:
{
v___y_6507_ = v___x_6538_;
v___y_6508_ = v_a_6535_;
v_a_6509_ = v___x_6551_;
goto v___jp_6506_;
}
}
}
else
{
lean_object* v_a_6554_; lean_object* v___x_6556_; uint8_t v_isShared_6557_; uint8_t v_isSharedCheck_6561_; 
v_a_6554_ = lean_ctor_get(v___x_6545_, 0);
v_isSharedCheck_6561_ = !lean_is_exclusive(v___x_6545_);
if (v_isSharedCheck_6561_ == 0)
{
v___x_6556_ = v___x_6545_;
v_isShared_6557_ = v_isSharedCheck_6561_;
goto v_resetjp_6555_;
}
else
{
lean_inc(v_a_6554_);
lean_dec(v___x_6545_);
v___x_6556_ = lean_box(0);
v_isShared_6557_ = v_isSharedCheck_6561_;
goto v_resetjp_6555_;
}
v_resetjp_6555_:
{
lean_object* v___x_6559_; 
if (v_isShared_6557_ == 0)
{
lean_ctor_set_tag(v___x_6556_, 0);
v___x_6559_ = v___x_6556_;
goto v_reusejp_6558_;
}
else
{
lean_object* v_reuseFailAlloc_6560_; 
v_reuseFailAlloc_6560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6560_, 0, v_a_6554_);
v___x_6559_ = v_reuseFailAlloc_6560_;
goto v_reusejp_6558_;
}
v_reusejp_6558_:
{
v___y_6507_ = v___x_6538_;
v___y_6508_ = v_a_6535_;
v_a_6509_ = v___x_6559_;
goto v___jp_6506_;
}
}
}
}
else
{
lean_object* v___x_6562_; lean_object* v___x_6563_; lean_object* v___x_6564_; lean_object* v___x_6565_; lean_object* v___x_6566_; lean_object* v___x_6567_; lean_object* v___f_6568_; lean_object* v___x_6569_; 
v___x_6562_ = lean_io_get_num_heartbeats();
v___x_6563_ = l_Lean_Meta_Tactic_Cbv_cbv_maxSteps;
v___x_6564_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_Tactic_Cbv_Main_0__Lean_Meta_Tactic_Cbv_handleProj_spec__4_spec__7(v_options_6492_, v___x_6563_);
v___x_6565_ = lean_unsigned_to_nat(2u);
v___x_6566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6566_, 0, v___x_6564_);
lean_ctor_set(v___x_6566_, 1, v___x_6565_);
v___x_6567_ = lean_box(v___x_6537_);
v___f_6568_ = lean_alloc_closure((void*)(l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___lam__6___boxed), 11, 4);
lean_closure_set(v___f_6568_, 0, v_m_6486_);
lean_closure_set(v___f_6568_, 1, v___x_6566_);
lean_closure_set(v___f_6568_, 2, v___x_6567_);
lean_closure_set(v___f_6568_, 3, v_cls_6495_);
v___x_6569_ = l_Lean_Meta_Sym_SymM_run___redArg(v___f_6568_, v_a_6487_, v_a_6488_, v_a_6489_, v_a_6490_);
if (lean_obj_tag(v___x_6569_) == 0)
{
lean_object* v_a_6570_; lean_object* v___x_6572_; uint8_t v_isShared_6573_; uint8_t v_isSharedCheck_6577_; 
v_a_6570_ = lean_ctor_get(v___x_6569_, 0);
v_isSharedCheck_6577_ = !lean_is_exclusive(v___x_6569_);
if (v_isSharedCheck_6577_ == 0)
{
v___x_6572_ = v___x_6569_;
v_isShared_6573_ = v_isSharedCheck_6577_;
goto v_resetjp_6571_;
}
else
{
lean_inc(v_a_6570_);
lean_dec(v___x_6569_);
v___x_6572_ = lean_box(0);
v_isShared_6573_ = v_isSharedCheck_6577_;
goto v_resetjp_6571_;
}
v_resetjp_6571_:
{
lean_object* v___x_6575_; 
if (v_isShared_6573_ == 0)
{
lean_ctor_set_tag(v___x_6572_, 1);
v___x_6575_ = v___x_6572_;
goto v_reusejp_6574_;
}
else
{
lean_object* v_reuseFailAlloc_6576_; 
v_reuseFailAlloc_6576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6576_, 0, v_a_6570_);
v___x_6575_ = v_reuseFailAlloc_6576_;
goto v_reusejp_6574_;
}
v_reusejp_6574_:
{
v___y_6522_ = v___x_6562_;
v___y_6523_ = v_a_6535_;
v_a_6524_ = v___x_6575_;
goto v___jp_6521_;
}
}
}
else
{
lean_object* v_a_6578_; lean_object* v___x_6580_; uint8_t v_isShared_6581_; uint8_t v_isSharedCheck_6585_; 
v_a_6578_ = lean_ctor_get(v___x_6569_, 0);
v_isSharedCheck_6585_ = !lean_is_exclusive(v___x_6569_);
if (v_isSharedCheck_6585_ == 0)
{
v___x_6580_ = v___x_6569_;
v_isShared_6581_ = v_isSharedCheck_6585_;
goto v_resetjp_6579_;
}
else
{
lean_inc(v_a_6578_);
lean_dec(v___x_6569_);
v___x_6580_ = lean_box(0);
v_isShared_6581_ = v_isSharedCheck_6585_;
goto v_resetjp_6579_;
}
v_resetjp_6579_:
{
lean_object* v___x_6583_; 
if (v_isShared_6581_ == 0)
{
lean_ctor_set_tag(v___x_6580_, 0);
v___x_6583_ = v___x_6580_;
goto v_reusejp_6582_;
}
else
{
lean_object* v_reuseFailAlloc_6584_; 
v_reuseFailAlloc_6584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6584_, 0, v_a_6578_);
v___x_6583_ = v_reuseFailAlloc_6584_;
goto v_reusejp_6582_;
}
v_reusejp_6582_:
{
v___y_6522_ = v___x_6562_;
v___y_6523_ = v_a_6535_;
v_a_6524_ = v___x_6583_;
goto v___jp_6521_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Tactic_Cbv_cbvDecideGoal___boxed(lean_object* v_m_6595_, lean_object* v_a_6596_, lean_object* v_a_6597_, lean_object* v_a_6598_, lean_object* v_a_6599_, lean_object* v_a_6600_){
_start:
{
lean_object* v_res_6601_; 
v_res_6601_ = l_Lean_Meta_Tactic_Cbv_cbvDecideGoal(v_m_6595_, v_a_6596_, v_a_6597_, v_a_6598_, v_a_6599_);
lean_dec(v_a_6599_);
lean_dec_ref(v_a_6598_);
lean_dec(v_a_6597_);
lean_dec_ref(v_a_6596_);
return v_res_6601_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0(lean_object* v_00_u03b1_6602_, lean_object* v_msg_6603_, lean_object* v___y_6604_, lean_object* v___y_6605_, lean_object* v___y_6606_, lean_object* v___y_6607_, lean_object* v___y_6608_, lean_object* v___y_6609_){
_start:
{
lean_object* v___x_6611_; 
v___x_6611_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___redArg(v_msg_6603_, v___y_6606_, v___y_6607_, v___y_6608_, v___y_6609_);
return v___x_6611_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0___boxed(lean_object* v_00_u03b1_6612_, lean_object* v_msg_6613_, lean_object* v___y_6614_, lean_object* v___y_6615_, lean_object* v___y_6616_, lean_object* v___y_6617_, lean_object* v___y_6618_, lean_object* v___y_6619_, lean_object* v___y_6620_){
_start:
{
lean_object* v_res_6621_; 
v_res_6621_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__0(v_00_u03b1_6612_, v_msg_6613_, v___y_6614_, v___y_6615_, v___y_6616_, v___y_6617_, v___y_6618_, v___y_6619_);
lean_dec(v___y_6619_);
lean_dec_ref(v___y_6618_);
lean_dec(v___y_6617_);
lean_dec_ref(v___y_6616_);
lean_dec(v___y_6615_);
lean_dec_ref(v___y_6614_);
return v_res_6621_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1(lean_object* v_cls_6622_, lean_object* v_msg_6623_, lean_object* v___y_6624_, lean_object* v___y_6625_, lean_object* v___y_6626_, lean_object* v___y_6627_, lean_object* v___y_6628_, lean_object* v___y_6629_){
_start:
{
lean_object* v___x_6631_; 
v___x_6631_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___redArg(v_cls_6622_, v_msg_6623_, v___y_6626_, v___y_6627_, v___y_6628_, v___y_6629_);
return v___x_6631_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1___boxed(lean_object* v_cls_6632_, lean_object* v_msg_6633_, lean_object* v___y_6634_, lean_object* v___y_6635_, lean_object* v___y_6636_, lean_object* v___y_6637_, lean_object* v___y_6638_, lean_object* v___y_6639_, lean_object* v___y_6640_){
_start:
{
lean_object* v_res_6641_; 
v_res_6641_ = l_Lean_addTrace___at___00Lean_Meta_Tactic_Cbv_cbvDecideGoal_spec__1(v_cls_6632_, v_msg_6633_, v___y_6634_, v___y_6635_, v___y_6636_, v___y_6637_, v___y_6638_, v___y_6639_);
lean_dec(v___y_6639_);
lean_dec_ref(v___y_6638_);
lean_dec(v___y_6637_);
lean_dec_ref(v___y_6636_);
lean_dec(v___y_6635_);
lean_dec_ref(v___y_6634_);
return v_res_6641_;
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
